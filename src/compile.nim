## Def-to-closure compiler for TLA-on-NIF.
##
## Compiles a module's invariant and Next action into closure trees once at
## load time, replacing the cursor-walking interpreter in the hot path:
##
## - Defs are inlined at their reference sites (they form a DAG; the
##   interpreter cannot evaluate recursive defs either), which resolves the
##   dialect's dynamic scoping statically.
## - Every binder site gets a unique index into one flat `slots` vector;
##   symbol references compile to array reads instead of Table lookups, and
##   there is no per-binding Frame (three Tables) copy.
## - Actions are compiled in continuation-passing style with the
##   continuations composed at compile time, so enumeration allocates no
##   closures at run time. Primes mutate a flat `primed`/`primedSet` pair
##   and undo themselves on backtrack, replacing frame copies.
## - Booleans, null and small ints are singletons; quantifier domains that
##   are compile-time constants are pre-collected into a `seq[Value]`.
##
## The interpreter in eval.nim stays as the reference semantics (used by
## the sequential explorer and for Init), so `--jobs:0` vs `--jobs:N` is a
## standing differential test. Def memoization is intentionally absent
## here: a memo hit costs a key build + structural hash, which compiled
## evaluation undercuts.

import std / [tables, sets, algorithm]
import nifcore, value, eval, tlanif_model

type
  CExpr = proc(): Value
  Cont = proc()

  Ctx = ref object
    slots: seq[Value]        ## [0..nvars-1] variables, then binder sites
    primed: seq[Value]
    primedSet: seq[bool]
    atStack: seq[Value]
    epoch: int               ## bumped when intern tables are flushed
    gen: int                 ## state generation, bumped by loadState
    varIds: seq[int32]       ## per-variable intern id of the current value
    curSegs: seq[string]     ## per-variable encoded bytes of current value
    emit*: proc()            ## invoked once per successful Next branch

  Scope = object
    slotOf: Table[SymId, int]

  VarIntern = object
    ## Per-variable interning of decoded values (worker-side): skips
    ## re-decoding recurring values and yields dense ids for def-cache keys.
    idx: Table[string, int32]
    vals: seq[Value]

  CompiledModule* = ref object
    m*: Module
    ctx*: Ctx
    nvars*: int
    inv: CExpr
    nextRun: Cont
    goals: seq[CExpr]
    fairActions: seq[Cont]
    numSlots: int
    inlining: HashSet[SymId]
    interns: seq[VarIntern]
    trueV, falseV, nullV, boolSetV, emptySetV, emptySeqV: Value
    intCache: seq[Value]

const
  IntCacheMax = 256
  InternCap = 1_000_000      ## per-variable intern entries before epoch flush
  DefCacheCap = 200_000      ## per-site def-cache entries before flush
  CK = 4                     ## def-cache key arity (frees beyond this: no cache)

proc mkBool(cm: CompiledModule; b: bool): Value {.inline.} =
  if b: cm.trueV else: cm.falseV

proc mkInt(cm: CompiledModule; x: int64): Value =
  if x >= 0 and x <= IntCacheMax: cm.intCache[int x]
  else:
    buildValue(cm.m.vs):
      t.addInt x

proc guardBool(v: Value): bool {.inline.} =
  if kind(v) != vkBool: raiseEval("expected boolean, got " & $kind(v))
  getBool(v)

proc newSlot(cm: CompiledModule): int =
  result = cm.numSlots
  inc cm.numSlots

# ── Expression compilation ───────────────────────────────────────────────

proc compileExpr(cm: CompiledModule; c: var Cursor; sc: Scope): CExpr

proc compileArgs(cm: CompiledModule; c: var Cursor; sc: Scope): seq[CExpr] =
  result = @[]
  while c.hasMore:
    result.add compileExpr(cm, c, sc)

proc constValue(e: CExpr): Value =
  ## Evaluate a compile-time-constant closure now.
  e()

proc compileSymRef(cm: CompiledModule; s: SymId; sc: Scope): CExpr =
  let ctx = cm.ctx
  if s in sc.slotOf:
    let idx = sc.slotOf[s]
    return proc(): Value = ctx.slots[idx]
  if s in cm.m.env:
    let v = cm.m.env[s]
    return proc(): Value = v
  if s in cm.m.defs:
    if s in cm.inlining:
      raiseEval("recursive def cannot be compiled: " & cm.m.pool.poolSym(s))
    cm.inlining.incl s
    var body = cm.m.defs[s].body
    let bodyE = compileExpr(cm, body, sc)
    cm.inlining.excl s
    # Per-site cross-state memo — the compiled reconstruction of the
    # interpreter's def memo, with integer keys instead of built-and-hashed
    # key Values. Variable frees contribute the variable's intern id for
    # the current state (see loadState), binder frees contribute their
    # (small) value directly. Flushed when the intern tables flush (epoch).
    let info = getDefInfo(cm.m, s)
    if info.memoizable and info.frees.len <= CK:
      var comps: seq[int] = @[]   # >=0: binder slot; -1-i: variable i
      var cacheable = true
      for fs in info.frees:
        if fs in sc.slotOf and sc.slotOf[fs] >= cm.nvars:
          comps.add sc.slotOf[fs]
        elif fs in sc.slotOf:
          comps.add -1 - sc.slotOf[fs]
        else:
          cacheable = false    # free not bound at this site
          break
      if cacheable:
        # Keyed by the raw encoded bytes of the def's variable frees (the
        # per-variable segments loadState already holds) plus small binder
        # values. Projection semantics give cross-state reuse: a conjunct
        # free over (status, loc) hits one entry for every state that
        # differs only in other variables — this is where the interpreter
        # memo got its win, minus the built-and-hashed key Values.
        var cache = initTable[string, Value]()
        var looks = 0
        var hits = 0
        var disabled = false
        let cs = comps
        return proc(): Value =
          # Adaptive: a site whose keys turn out nearly unique (an
          # invariant conjunct free over most variables sees one key per
          # state) pays insert churn and unbounded growth for nothing —
          # after the sampling window it disables itself and recomputes,
          # which post-guardBool-fix is cheap (short-circuited body).
          if disabled: return bodyE()
          var key = newStringOfCap(cs.len * 12)
          for i in 0 ..< cs.len:
            if cs[i] < 0:
              key.add ctx.curSegs[-1 - cs[i]]
            else:
              let v = ctx.slots[cs[i]]
              var k: uint32
              case kind(v)
              of vkModel: k = uint32(getModel(v))
              of vkInt:
                let x = getInt(v)
                if x < 0 or x >= 1 shl 29: return bodyE()
                k = uint32(x) or (1'u32 shl 29)
              of vkBool: k = uint32(ord(getBool(v))) or (2'u32 shl 30)
              of vkNull: k = 3'u32 shl 30
              else: return bodyE()
              key.add char(k and 0xff)
              key.add char((k shr 8) and 0xff)
              key.add char((k shr 16) and 0xff)
              key.add char((k shr 24) and 0xff)
          cache.withValue(key, hit):
            inc hits
            inc looks
            return hit[]
          inc looks
          if looks >= 8192:
            if hits * 4 < looks:
              disabled = true
              cache = initTable[string, Value]()
              return bodyE()
            looks = 0
            hits = 0
          if cache.len >= DefCacheCap:
            cache.clear()
          let v = bodyE()
          cache[key] = v
          return v
    return bodyE
  raiseEval("unbound symbol: " & cm.m.pool.poolSym(s))

type
  Domain = object
    ## A quantifier/funof domain: either pre-collected constant elements or
    ## a closure evaluated per entry.
    constElems: seq[Value]
    isConst: bool
    ex: CExpr

proc compileDomain(cm: CompiledModule; c: var Cursor; sc: Scope): Domain =
  # Constant when the domain is a plain reference to a grounded constant.
  if c.kind == Symbol and c.symId in cm.m.env and c.symId notin sc.slotOf:
    let v = cm.m.env[c.symId]
    c.inc
    if kind(v) != vkSet: raiseEval("domain must be a set")
    return Domain(constElems: collectItems(v), isConst: true)
  let e = compileExpr(cm, c, sc)
  result = Domain(isConst: false, ex: e)

iterator domItems(d: Domain): Value =
  if d.isConst:
    for e in d.constElems: yield e
  else:
    let dv = d.ex()
    if kind(dv) != vkSet: raiseEval("domain must be a set")
    for e in items(dv): yield e

proc compileBinderBody(cm: CompiledModule; c: var Cursor; sc: Scope;
                       binder: SymId; slot: int): CExpr =
  var sc2 = sc
  sc2.slotOf[binder] = slot
  result = compileExpr(cm, c, sc2)

proc compileExpr(cm: CompiledModule; c: var Cursor; sc: Scope): CExpr =
  let ctx = cm.ctx
  let vs = cm.m.vs
  case c.kind
  of IntLit:
    let v = mkInt(cm, c.intVal)
    c.inc
    result = proc(): Value = v
  of UIntLit:
    let v = mkInt(cm, int64(c.uintVal))
    c.inc
    result = proc(): Value = v
  of Symbol:
    result = compileSymRef(cm, c.symId, sc)
    c.inc
  of SymbolDef:
    raiseEval("SymbolDef not valid as expression use: " & c.symName)
  of Ident:
    raiseEval("Ident not allowed: " & c.strVal)
  of DotToken:
    let v = cm.nullV
    c.inc
    result = proc(): Value = v
  of TagLit:
    let tag = tlaTag(c.cursorTagId)
    case tag
    of TTrue:
      let v = cm.trueV
      c.skip
      result = proc(): Value = v
    of TFalse:
      let v = cm.falseV
      c.skip
      result = proc(): Value = v
    of TNull:
      let v = cm.nullV
      c.skip
      result = proc(): Value = v
    of TBool:
      let v = cm.boolSetV
      c.skip
      result = proc(): Value = v
    of TEmptySet:
      let v = cm.emptySetV
      c.skip
      result = proc(): Value = v
    of TEmptySeq:
      let v = cm.emptySeqV
      c.skip
      result = proc(): Value = v
    of TAt:
      c.skip
      result = proc(): Value =
        if ctx.atStack.len == 0: raiseEval("`at`/`@` outside except")
        ctx.atStack[^1]
    of TNot:
      c.into:
        let a = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, not guardBool(a()))
    of TAnd:
      c.into:
        let parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          for p in parts:
            if not guardBool(p()): return cm.falseV
          cm.trueV
    of TOr:
      c.into:
        let parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          for p in parts:
            if guardBool(p()): return cm.trueV
          cm.falseV
    of TImplies:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value =
          if guardBool(a()): mkBool(cm, guardBool(b()))
          else: cm.trueV
    of TEq:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, a() == b())
    of TNeq:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, a() != b())
    of TIn:
      c.into:
        let x = compileExpr(cm, c, sc)
        let s = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, x() in s())
    of TNotin:
      c.into:
        let x = compileExpr(cm, c, sc)
        let s = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, x() notin s())
    of TSubset:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, subset(a(), b()))
    of TUnion:
      c.into:
        var parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          var acc = parts[0]()
          for i in 1 ..< parts.len:
            acc = union(vs, acc, parts[i]())
          acc
    of TIntersect:
      c.into:
        var parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          var acc = parts[0]()
          for i in 1 ..< parts.len:
            acc = intersect(vs, acc, parts[i]())
          acc
    of TSetminus:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = setminus(vs, a(), b())
    of TCard:
      c.into:
        let a = compileExpr(cm, c, sc)
        result = proc(): Value = mkInt(cm, card(a()))
    of TSet:
      c.into:
        let parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          var xs = newSeq[Value](parts.len)
          for i in 0 ..< parts.len: xs[i] = parts[i]()
          sortedUniqueSet(vs, xs)
    of TSeq:
      c.into:
        let parts = compileArgs(cm, c, sc)
        result = proc(): Value =
          buildValue(vs):
            t.buildTree VTSeq:
              for p in parts: t.addValue p()
    of TLen:
      c.into:
        let a = compileExpr(cm, c, sc)
        result = proc(): Value =
          let s = a()
          case kind(s)
          of vkSeq, vkSet: mkInt(cm, len(s))
          else: raiseEval("len on non-seq/set")
    of TAppend:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value =
          let s = a()
          if kind(s) != vkSeq: raiseEval("append needs seq")
          let x = b()
          buildValue(vs):
            t.buildTree VTSeq:
              for e in items(s): t.addValue e
              t.addValue x
    of TConcat:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value =
          let x = a()
          let y = b()
          if kind(x) != vkSeq or kind(y) != vkSeq: raiseEval("concat needs seqs")
          buildValue(vs):
            t.buildTree VTSeq:
              for e in items(x): t.addValue e
              for e in items(y): t.addValue e
    of TRange:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value =
          let lo = a()
          let hi = b()
          if kind(lo) != vkInt or kind(hi) != vkInt: raiseEval("range needs ints")
          buildValue(vs):
            t.buildTree VTSet:
              var i = getInt(lo)
              while i <= getInt(hi):
                t.addInt i
                inc i
    of TFun:
      c.into:
        var ks: seq[CExpr] = @[]
        var vsE: seq[CExpr] = @[]
        while c.hasMore:
          expectTag(c, TMapsto)
          c.into:
            ks.add compileExpr(cm, c, sc)
            vsE.add compileExpr(cm, c, sc)
        result = proc(): Value =
          var pairs = newSeq[(Value, Value)](ks.len)
          for i in 0 ..< ks.len:
            pairs[i] = (ks[i](), vsE[i]())
          pairs.sort(proc (a, b: (Value, Value)): int = cmpValue(a[0], b[0]))
          buildValue(vs):
            t.buildTree VTFun:
              for (k, v) in pairs: t.addMapsto k, v
    of TFunof:
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        let body = compileBinderBody(cm, c, sc, binder, slot)
        result = proc(): Value =
          var pairs: seq[(Value, Value)] = @[]
          for e in domItems(dom):
            ctx.slots[slot] = e
            pairs.add (e, body())
          pairs.sort(proc (a, b: (Value, Value)): int = cmpValue(a[0], b[0]))
          buildValue(vs):
            t.buildTree VTFun:
              for (k, v) in pairs: t.addMapsto k, v
    of TSetcomp:
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        let pred = compileBinderBody(cm, c, sc, binder, slot)
        result = proc(): Value =
          var xs: seq[Value] = @[]
          for e in domItems(dom):
            ctx.slots[slot] = e
            if guardBool(pred()): xs.add e
          sortedUniqueSet(vs, xs)
    of TChoose:
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        let pred = compileBinderBody(cm, c, sc, binder, slot)
        result = proc(): Value =
          for e in domItems(dom):
            ctx.slots[slot] = e
            if guardBool(pred()): return e
          raiseEval("CHOOSE has no witness")
    of TExists, TForall:
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        let body = compileBinderBody(cm, c, sc, binder, slot)
        if tag == TExists:
          result = proc(): Value =
            for e in domItems(dom):
              ctx.slots[slot] = e
              if guardBool(body()): return cm.trueV
            cm.falseV
        else:
          result = proc(): Value =
            for e in domItems(dom):
              ctx.slots[slot] = e
              if not guardBool(body()): return cm.falseV
            cm.trueV
    of TExcept:
      c.into:
        let base = compileExpr(cm, c, sc)
        var ks: seq[CExpr] = @[]
        var vsE: seq[CExpr] = @[]
        while c.hasMore:
          expectTag(c, TMapsto)
          c.into:
            ks.add compileExpr(cm, c, sc)
            vsE.add compileExpr(cm, c, sc)
        result = proc(): Value =
          let b = base()
          if kind(b) != vkFun: raiseEval("except requires a function")
          var updates = newSeq[(Value, Value)](ks.len)
          for i in 0 ..< ks.len:
            let k = ks[i]()
            ctx.atStack.add applyFun(b, k)
            updates[i] = (k, vsE[i]())
            discard ctx.atStack.pop()
          exceptFun(vs, b, updates)
    of TDomain:
      c.into:
        let a = compileExpr(cm, c, sc)
        result = proc(): Value = domainOf(vs, a())
    of TApply:
      c.into:
        let fn = compileExpr(cm, c, sc)
        let arg = compileExpr(cm, c, sc)
        result = proc(): Value = applyFun(fn(), arg())
    of TRecord:
      c.into:
        var fs: seq[SymId] = @[]
        var vsE: seq[CExpr] = @[]
        while c.hasMore:
          expectTag(c, TKv)
          c.into:
            fs.add takeSymId(c)
            vsE.add compileExpr(cm, c, sc)
        result = proc(): Value =
          var fields = newSeq[(SymId, Value)](fs.len)
          for i in 0 ..< fs.len:
            fields[i] = (fs[i], vsE[i]())
          fields.sort(proc (a, b: (SymId, Value)): int =
            cmp(a[0].uint32, b[0].uint32))
          buildValue(vs):
            t.buildTree VTRecord:
              for (k, v) in fields: t.addKv k, v
    of TField:
      c.into:
        let rec = compileExpr(cm, c, sc)
        let fld = takeSymId(c)
        result = proc(): Value =
          let r = rec()
          if kind(r) != vkRecord: raiseEval("field: not a record")
          for (k, v) in fields(r):
            if k == fld: return v
          raiseEval("field missing: " & cm.m.pool.poolSym(fld))
    of TLet:
      c.into:
        var sc2 = sc
        var slots: seq[int] = @[]
        var binds: seq[CExpr] = @[]
        while c.hasMore and c.isTag(TBind):
          c.into:
            let s = takeSymId(c)
            binds.add compileExpr(cm, c, sc2)
            let slot = newSlot(cm)
            slots.add slot
            sc2.slotOf[s] = slot
        let body = compileExpr(cm, c, sc2)
        result = proc(): Value =
          for i in 0 ..< binds.len:
            ctx.slots[slots[i]] = binds[i]()
          body()
    of TIf:
      c.into:
        let cond = compileExpr(cm, c, sc)
        let th = compileExpr(cm, c, sc)
        if not c.hasMore: raiseEval("if expression requires an else branch")
        let el = compileExpr(cm, c, sc)
        result = proc(): Value =
          if guardBool(cond()): th() else: el()
    of TGt:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, getInt(a()) > getInt(b()))
    of TGe:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, getInt(a()) >= getInt(b()))
    of TLt:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, getInt(a()) < getInt(b()))
    of TLe:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkBool(cm, getInt(a()) <= getInt(b()))
    of TPlus:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkInt(cm, getInt(a()) + getInt(b()))
    of TMinus:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc(): Value = mkInt(cm, getInt(a()) - getInt(b()))
    of TPrime, TUnchanged:
      raiseEval("prime/unchanged only valid in actions")
    else:
      raiseEval("cannot compile tag as expression: " & $tag)
  else:
    raiseEval("unexpected kind in expr: " & $c.kind)

# ── Action compilation (CPS, continuations fixed at compile time) ────────

proc compileAction(cm: CompiledModule; c: var Cursor; sc: Scope;
                   k: Cont): Cont

proc guardCont(cm: CompiledModule; e: CExpr; k: Cont): Cont =
  result = proc() =
    if guardBool(e()): k()

proc compilePrimeInto(cm: CompiledModule; varSym: SymId; e: CExpr;
                      k: Cont): Cont =
  let ctx = cm.ctx
  var idx = -1
  for i in 0 ..< cm.m.variables.len:
    if cm.m.variables[i] == varSym: idx = i; break
  if idx < 0:
    raiseEval("prime of non-variable: " & cm.m.pool.poolSym(varSym))
  result = proc() =
    let v = e()
    if ctx.primedSet[idx]:
      if ctx.primed[idx] == v: k()
    else:
      ctx.primedSet[idx] = true
      ctx.primed[idx] = v
      k()
      ctx.primedSet[idx] = false

proc slotReader(ctx: Ctx; slot: int): CExpr =
  ## A fresh closure per call. `unchanged` builds one reader per variable in a
  ## loop; a `proc` literal written inside that loop captured the loop-body
  ## `slot` by its single shared environment cell, so EVERY reader read the
  ## slot of the last iteration: `(unchanged phase logIdx)` copied `phase`
  ## into `logIdx`. Found by the arkham_bindings port (nativenif/proofs).
  result = proc(): Value = ctx.slots[slot]

proc compileAction(cm: CompiledModule; c: var Cursor; sc: Scope;
                   k: Cont): Cont =
  let ctx = cm.ctx
  case c.kind
  of Symbol:
    let s = c.symId
    c.inc
    if s in cm.m.defs and s notin sc.slotOf:
      if s in cm.inlining:
        raiseEval("recursive def cannot be compiled: " & cm.m.pool.poolSym(s))
      cm.inlining.incl s
      var body = cm.m.defs[s].body
      result = compileAction(cm, body, sc, k)
      cm.inlining.excl s
      return
    result = guardCont(cm, compileSymRef(cm, s, sc), k)
  of TagLit:
    let tag = tlaTag(c.cursorTagId)
    case tag
    of TTrue:
      c.skip
      result = k
    of TFalse:
      c.skip
      result = proc() = discard
    of TAnd:
      # Fold right so evaluation order matches the interpreter.
      var parts: seq[Cursor] = @[]
      c.into:
        while c.hasMore:
          parts.add c
          c.skip
      var cont = k
      for i in countdown(parts.high, 0):
        var pc = parts[i]
        cont = compileAction(cm, pc, sc, cont)
      result = cont
    of TOr:
      if not containsPrime(cm.m, c):
        var tmp = c
        let e = compileExpr(cm, tmp, sc)
        c.skip
        result = guardCont(cm, e, k)
      else:
        var conts: seq[Cont] = @[]
        c.into:
          while c.hasMore:
            var pc = c
            conts.add compileAction(cm, pc, sc, k)
            c.skip
        result = proc() =
          for br in conts: br()
    of TNot:
      c.into:
        let e = compileExpr(cm, c, sc)
        result = proc() =
          if not guardBool(e()): k()
    of TExists:
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        var sc2 = sc
        sc2.slotOf[binder] = slot
        let body = compileAction(cm, c, sc2, k)
        result = proc() =
          for e in domItems(dom):
            ctx.slots[slot] = e
            body()
    of TForall:
      # Pure guard in action position, like the interpreter.
      c.into:
        let binder = takeSymId(c)
        let dom = compileDomain(cm, c, sc)
        let slot = newSlot(cm)
        let body = compileBinderBody(cm, c, sc, binder, slot)
        result = proc() =
          for e in domItems(dom):
            ctx.slots[slot] = e
            if not guardBool(body()): return
          k()
    of TPrime:
      c.into:
        let s = takeSymId(c)
        let e = compileExpr(cm, c, sc)
        result = compilePrimeInto(cm, s, e, k)
    of TUnchanged:
      var syms: seq[SymId] = @[]
      c.into:
        while c.hasMore:
          syms.add takeSymId(c)
      var cont = k
      for i in countdown(syms.high, 0):
        let s = syms[i]
        if s notin sc.slotOf or sc.slotOf[s] >= cm.nvars:
          raiseEval("unchanged of non-variable: " & cm.m.pool.poolSym(s))
        let slot = sc.slotOf[s]
        cont = compilePrimeInto(cm, s, slotReader(ctx, slot), cont)
      result = cont
    of TEq:
      c.into:
        let a = compileExpr(cm, c, sc)
        let b = compileExpr(cm, c, sc)
        result = proc() =
          if a() == b(): k()
    of TLet:
      c.into:
        var sc2 = sc
        var slots: seq[int] = @[]
        var binds: seq[CExpr] = @[]
        while c.hasMore and c.isTag(TBind):
          c.into:
            let s = takeSymId(c)
            binds.add compileExpr(cm, c, sc2)
            let slot = newSlot(cm)
            slots.add slot
            sc2.slotOf[s] = slot
        let body = compileAction(cm, c, sc2, k)
        result = proc() =
          for i in 0 ..< binds.len:
            ctx.slots[slots[i]] = binds[i]()
          body()
    of TIf:
      c.into:
        let cond = compileExpr(cm, c, sc)
        let th = compileAction(cm, c, sc, k)
        if not c.hasMore: raiseEval("if action requires an else branch")
        let el = compileAction(cm, c, sc, k)
        result = proc() =
          if guardBool(cond()): th() else: el()
    else:
      var tmp = c
      let e = compileExpr(cm, tmp, sc)
      c.skip
      result = guardCont(cm, e, k)
  else:
    var tmp = c
    let e = compileExpr(cm, tmp, sc)
    c.skip
    result = guardCont(cm, e, k)

# ── Module compilation and drivers ───────────────────────────────────────

proc compileModule*(m: Module; goals: seq[Cursor] = @[];
                    fairActions: seq[Cursor] = @[]): CompiledModule =
  ## Additional state predicates/actions share slots and one loaded state.
  let cm = CompiledModule(
    m: m,
    ctx: Ctx(atStack: @[]),
    nvars: m.variables.len,
    numSlots: m.variables.len,
    inlining: initHashSet[SymId]())
  cm.trueV = block:
    buildValue(m.vs):
      t.addBool true
  cm.falseV = block:
    buildValue(m.vs):
      t.addBool false
  cm.nullV = block:
    buildValue(m.vs):
      t.addNull
  cm.boolSetV = block:
    buildValue(m.vs):
      t.buildTree VTSet:
        t.addBool false
        t.addBool true
  cm.emptySetV = block:
    buildValue(m.vs):
      t.buildTree VTSet:
        discard
  cm.emptySeqV = block:
    buildValue(m.vs):
      t.buildTree VTSeq:
        discard
  cm.intCache = newSeq[Value](IntCacheMax + 1)
  for i in 0 .. IntCacheMax:
    cm.intCache[i] = block:
      buildValue(m.vs):
        t.addInt int64(i)

  var sc = Scope(slotOf: initTable[SymId, int]())
  for i in 0 ..< m.variables.len:
    sc.slotOf[m.variables[i]] = i

  var invBody = m.checkBody
  cm.inv = compileExpr(cm, invBody, sc)

  let ctx = cm.ctx
  let emitK: Cont = proc() = ctx.emit()
  var nextBody = m.nextBody
  cm.nextRun = compileAction(cm, nextBody, sc, emitK)

  for goal in goals:
    var body = goal
    cm.goals.add compileExpr(cm, body, sc)
  for action in fairActions:
    var body = action
    cm.fairActions.add compileAction(cm, body, sc, emitK)

  ctx.slots.setLen cm.numSlots
  ctx.primed.setLen cm.nvars
  ctx.primedSet.setLen cm.nvars
  ctx.varIds.setLen cm.nvars
  ctx.curSegs.setLen cm.nvars
  cm.interns = newSeq[VarIntern](cm.nvars)
  for i in 0 ..< cm.nvars:
    cm.interns[i] = VarIntern(idx: initTable[string, int32](), vals: @[])
  result = cm

proc loadState*(cm: CompiledModule; enc: string) =
  ## Load an encoded state into the variable slots, interning each
  ## variable's value: recurring values skip decoding entirely and get a
  ## dense id that keys the def caches.
  inc cm.ctx.gen
  var flush = false
  for i in 0 ..< cm.nvars:
    if cm.interns[i].idx.len >= InternCap: flush = true
  if flush:
    for i in 0 ..< cm.nvars:
      cm.interns[i].idx.clear()
      cm.interns[i].vals.setLen 0
    inc cm.ctx.epoch
  var pos = 0
  for i in 0 ..< cm.nvars:
    let start = pos
    skipEncodedValue(enc, pos)
    let seg = enc[start .. pos - 1]
    var id: int32
    cm.interns[i].idx.withValue(seg, hit):
      id = hit[]
    do:
      id = int32(cm.interns[i].vals.len)
      var p2 = start
      cm.interns[i].vals.add decodeValue(cm.m.vs, enc, p2)
      cm.interns[i].idx[seg] = id
    cm.ctx.slots[i] = cm.interns[i].vals[int id]
    cm.ctx.varIds[i] = id
    cm.ctx.curSegs[i] = seg

var invCalls* {.threadvar.}: int

proc checkInv*(cm: CompiledModule): bool =
  inc invCalls
  guardBool(cm.inv())

proc checkGoal*(cm: CompiledModule; index: int): bool =
  guardBool(cm.goals[index]())

proc runFairAction*(cm: CompiledModule; index: int; emit: proc()) =
  ## Same enumeration and omitted-variable stuttering as runNext.
  cm.ctx.emit = emit
  try:
    cm.fairActions[index]()
  finally:
    cm.ctx.emit = nil

proc runNext*(cm: CompiledModule; emit: proc()) =
  ## Enumerate all Next branches for the loaded state; `emit` fires once
  ## per successful branch with `ctx.primed`/`slots` describing the
  ## successor. All primes are undone by backtracking before this returns.
  cm.ctx.emit = emit
  cm.nextRun()
  cm.ctx.emit = nil

proc encodeSuccessor*(cm: CompiledModule; dest: var string) =
  ## Canonical bytes of the successor currently described by primed/slots.
  dest.setLen 0
  for i in 0 ..< cm.nvars:
    if cm.ctx.primedSet[i]:
      encodeValue(cm.ctx.primed[i], dest)
    else:
      dest.add cm.ctx.curSegs[i]

proc successorState*(cm: CompiledModule): State =
  ## Successor as a State (needed for symmetry canonicalization).
  result = State(vals: initTable[SymId, Value]())
  for i in 0 ..< cm.nvars:
    result.vals[cm.m.variables[i]] =
      (if cm.ctx.primedSet[i]: cm.ctx.primed[i] else: cm.ctx.slots[i])
