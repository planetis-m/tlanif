## Expression / action evaluator for TLA-on-NIF.

import std / [tables, sets, strutils, algorithm]
import tlanif_model, value

type
  EvalError* = object of CatchableError

  DefEntry* = object
    body*: Cursor          ## points at expression body (after SymbolDef)

  DefInfo* = object
    ## Cached analysis of a `def`, driving expression-level memoization.
    ## `frees` is the set of *environment* symbols the def transitively reads
    ## (variables + free binders it inherits from its caller), with module
    ## constants excluded. `memoizable` is false iff the def transitively
    ## touches `@`/`prime`/`unchanged`, whose value is not a pure function of
    ## `frees`. Over-approximating `frees` only costs cache hits, never
    ## soundness — so the analysis errs toward keeping symbols free.
    frees*: seq[SymId]     ## sorted, constants removed
    memoizable*: bool

  Module* = ref object
    buf*: TokenBuf
    pool*: Pool
    vs*: Values            ## value factory (shared Pool + ValueTag pool)
    constants*: seq[SymId]
    variables*: seq[SymId]
    modelGroups*: seq[seq[SymId]] ## interchangeable model elements, per sort
    defs*: Table[SymId, DefEntry]
    env*: Table[SymId, Value]     ## grounded constants + model values
    constSet*: HashSet[SymId]     ## symbols with a fixed (constant) value
    defInfo*: Table[SymId, DefInfo] ## lazily-computed free-var analysis
    memo*: Table[Value, Value]    ## (def, free-var values) → result value
    memoLimit*: int               ## entry cap; the table is flushed when it
                                  ## is reached (epoch eviction). 0 = unbounded.
    memoHits*: int
    memoMisses*: int
    initBody*: Cursor
    nextBody*: Cursor
    checkBody*: Cursor
    stutterVars*: seq[SymId]
    hasSpec*: bool
    hasCheck*: bool

  Frame* = object
    env*: Table[SymId, Value]    ## unprimed: constants, binders, current vars
    primed*: Table[SymId, Value] ## primed assignments collected so far
    atStack*: seq[Value]         ## EXCEPT `@` stack

proc raiseEval*(msg: string) {.noinline, noreturn.} =
  raise newException(EvalError, msg)

proc lookup*(f: Frame; s: SymId): Value =
  if s in f.env: return f.env[s]
  raiseEval("unbound symbol id " & $s.uint32)

proc withBind*(f: Frame; s: SymId; v: Value): Frame =
  result = f
  result.env = f.env
  result.env[s] = v
  result.primed = f.primed
  result.atStack = f.atStack

proc evalExpr*(m: Module; c: var Cursor; f: Frame): Value
proc evalAction*(m: Module; c: var Cursor; f: Frame): seq[Frame]

proc asBool(v: Value): bool =
  if kind(v) != vkBool: raiseEval("expected boolean, got " & $kind(v))
  getBool(v)

proc collectFree(m: Module; c: var Cursor; bound: HashSet[SymId];
                 acc: var HashSet[SymId]; visiting: var HashSet[SymId];
                 memoizable: var bool) =
  ## Consume one expression subtree at `c` (advancing `c` past it) and add to
  ## `acc` every symbol it reads from the surrounding environment: variables
  ## and binders inherited from an enclosing scope. Binders introduced *within*
  ## the subtree are tracked in `bound` and excluded. Def references are
  ## inlined (their bodies contribute their own residual frees) with `visiting`
  ## guarding against cycles. Sets `memoizable = false` on `@`/prime/unchanged.
  case c.kind
  of Symbol:
    let s = c.symId
    if s in bound:
      discard
    elif s in m.defs:
      if s notin visiting:
        visiting.incl s
        var body = m.defs[s].body
        collectFree(m, body, bound, acc, visiting, memoizable)
        visiting.excl s
    else:
      acc.incl s
    c.inc
  of SymbolDef:
    c.inc
  of TagLit:
    let tag = tlaTag(c.cursorTagId)
    case tag
    of TAt, TPrime, TUnchanged:
      memoizable = false
      c.skip
    of TLet:
      c.into:
        var b2 = bound
        while c.hasMore and c.isTag(TBind):
          c.into:
            let sym = takeSymId(c)
            collectFree(m, c, b2, acc, visiting, memoizable)  # RHS: pre-binding
            b2.incl sym
        while c.hasMore:
          collectFree(m, c, b2, acc, visiting, memoizable)    # body
    of TSetcomp, TFunof, TChoose, TExists, TForall:
      c.into:
        let x = takeSymId(c)
        collectFree(m, c, bound, acc, visiting, memoizable)   # domain: outer scope
        var b2 = bound
        b2.incl x
        while c.hasMore:
          collectFree(m, c, b2, acc, visiting, memoizable)    # pred/body
    of TField:
      c.into:
        collectFree(m, c, bound, acc, visiting, memoizable)   # record expr
        if c.hasMore: c.skip                                  # field name (not env)
    of TRecord:
      c.into:
        while c.hasMore:
          expectTag(c, TKv)
          c.into:
            if c.hasMore: c.skip                              # field name
            while c.hasMore:
              collectFree(m, c, bound, acc, visiting, memoizable)
    else:
      c.into:
        while c.hasMore:
          collectFree(m, c, bound, acc, visiting, memoizable)
  else:
    c.skip

proc getDefInfo*(m: Module; s: SymId): DefInfo =
  if s in m.defInfo: return m.defInfo[s]
  var acc = initHashSet[SymId]()
  var visiting = initHashSet[SymId]()
  visiting.incl s
  var memoizable = true
  var body = m.defs[s].body
  collectFree(m, body, initHashSet[SymId](), acc, visiting, memoizable)
  var frees: seq[SymId] = @[]
  for x in acc:
    if x notin m.constSet:          # constants never change: keep out of the key
      frees.add x
  frees.sort(proc (a, b: SymId): int = cmp(a.uint32, b.uint32))
  result = DefInfo(frees: frees, memoizable: memoizable)
  m.defInfo[s] = result

proc memoKey(m: Module; defSym: SymId; frees: seq[SymId]; f: Frame): Value =
  ## Flat-token key: a `(seq def s1 v1 s2 v2 ...)` value over the sorted free
  ## symbols and their current bindings. Reuses `Value`'s structural hash/`==`.
  buildValue(m.vs):
    t.buildTree VTSeq:
      t.addModel defSym
      for s in frees:
        t.addModel s
        t.addValue f.env[s]

proc evalSymRef(m: Module; s: SymId; f: Frame): Value =
  if s in f.env: return f.env[s]
  if s in m.defs:
    let info = getDefInfo(m, s)
    if info.memoizable:
      var ok = true
      for fs in info.frees:
        if fs notin f.env: ok = false; break
      if ok:
        let key = memoKey(m, s, info.frees, f)
        m.memo.withValue(key, hit):
          inc m.memoHits
          return hit[]
        inc m.memoMisses
        var body = m.defs[s].body
        let v = evalExpr(m, body, f)
        if m.memoLimit > 0 and m.memo.len >= m.memoLimit:
          m.memo.clear()
        m.memo[key] = v
        return v
    var body = m.defs[s].body
    return evalExpr(m, body, f)
  raiseEval("unbound symbol: " & m.pool.poolSym(s))

proc evalArgs(m: Module; c: var Cursor; f: Frame): seq[Value] =
  result = @[]
  while c.hasMore:
    result.add evalExpr(m, c, f)

proc evalFunof(m: Module; c: var Cursor; f: Frame): Value =
  ## (funof :x.0 Domain Body)
  let binder = takeSymId(c)
  let dom = evalExpr(m, c, f)
  if kind(dom) != vkSet: raiseEval("funof domain must be a set")
  var body = c
  c.skip
  var pairs: seq[(Value, Value)] = @[]
  for e in items(dom):
    let fr = f.withBind(binder, e)
    var b = body
    pairs.add (e, evalExpr(m, b, fr))
  pairs.sort(proc (a, b: (Value, Value)): int = cmpValue(a[0], b[0]))
  result = buildValue(m.vs):
    t.buildTree VTFun:
      for (k, v) in pairs:
        t.addMapsto k, v

proc evalSetcomp(m: Module; c: var Cursor; f: Frame): Value =
  ## (setcomp :x.0 Domain Pred)  — { x \in Domain : Pred }
  let binder = takeSymId(c)
  let dom = evalExpr(m, c, f)
  if kind(dom) != vkSet: raiseEval("setcomp domain must be a set")
  var pred = c
  c.skip
  var xs: seq[Value] = @[]
  for e in items(dom):
    let fr = f.withBind(binder, e)
    var p = pred
    if asBool(evalExpr(m, p, fr)):
      xs.add e
  result = sortedUniqueSet(m.vs, xs)

proc evalExcept(m: Module; c: var Cursor; f: Frame): Value =
  ## (except f (mapsto k v) ...)  — `@` in v refers to f[k]
  let base = evalExpr(m, c, f)
  if kind(base) != vkFun: raiseEval("except requires a function")
  var updates: seq[(Value, Value)] = @[]
  while c.hasMore:
    expectTag(c, TMapsto)
    c.into:
      let k = evalExpr(m, c, f)
      var fr = f
      fr.atStack = f.atStack
      fr.atStack.add applyFun(base, k)
      let v = evalExpr(m, c, fr)
      updates.add (k, v)
  result = exceptFun(m.vs, base, updates)

proc evalLet(m: Module; c: var Cursor; f: Frame): Value =
  ## (let (bind :x.0 e) ... body)
  var fr = f
  while c.hasMore and c.isTag(TBind):
    c.into:
      let s = takeSymId(c)
      let v = evalExpr(m, c, fr)
      fr = fr.withBind(s, v)
  result = evalExpr(m, c, fr)

proc evalChoose(m: Module; c: var Cursor; f: Frame): Value =
  ## (choose :x.0 Domain Pred) — deterministic: first match in sorted set order
  let binder = takeSymId(c)
  let dom = evalExpr(m, c, f)
  if kind(dom) != vkSet: raiseEval("choose domain must be a set")
  var pred = c
  c.skip
  for e in items(dom):
    let fr = f.withBind(binder, e)
    var p = pred
    if asBool(evalExpr(m, p, fr)):
      return e
  raiseEval("CHOOSE has no witness")

proc evalExpr*(m: Module; c: var Cursor; f: Frame): Value =
  case c.kind
  of IntLit:
    result = buildValue(m.vs):
      t.addInt c.intVal
    c.inc
  of UIntLit:
    result = buildValue(m.vs):
      t.addInt int64(c.uintVal)
    c.inc
  of Symbol:
    result = evalSymRef(m, c.symId, f)
    c.inc
  of SymbolDef:
    raiseEval("SymbolDef not valid as expression use: " & c.symName)
  of Ident:
    raiseEval("Ident not allowed: " & c.strVal)
  of DotToken:
    result = buildValue(m.vs):
      t.addNull
    c.inc
  of TagLit:
    let tag = tlaTag(c.cursorTagId)
    case tag
    of TTrue:
      result = buildValue(m.vs):
        t.addBool true
      c.skip
    of TFalse:
      result = buildValue(m.vs):
        t.addBool false
      c.skip
    of TNull:
      result = buildValue(m.vs):
        t.addNull
      c.skip
    of TBool:
      result = buildValue(m.vs):
        t.buildTree VTSet:
          t.addBool false
          t.addBool true
      c.skip
    of TAt:
      if f.atStack.len == 0: raiseEval("`at`/`@` outside except")
      result = f.atStack[^1]; c.skip
    of TNot:
      c.into:
        result = buildValue(m.vs):
          t.addBool(not asBool(evalExpr(m, c, f)))
    of TAnd:
      result = buildValue(m.vs):
        t.addBool true
      c.into:
        while c.hasMore:
          if not asBool(evalExpr(m, c, f)):
            result = buildValue(m.vs):
              t.addBool false
            while c.hasMore: c.skip
            break
    of TOr:
      result = buildValue(m.vs):
        t.addBool false
      c.into:
        while c.hasMore:
          if asBool(evalExpr(m, c, f)):
            result = buildValue(m.vs):
              t.addBool true
            while c.hasMore: c.skip
            break
    of TEq:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(a == b)
    of TNeq:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(a != b)
    of TIn:
      c.into:
        let x = evalExpr(m, c, f)
        let s = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(x in s)
    of TNotin:
      c.into:
        let x = evalExpr(m, c, f)
        let s = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(x notin s)
    of TSubset:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(subset(a, b))
    of TUnion:
      c.into:
        result = evalExpr(m, c, f)
        while c.hasMore:
          result = union(m.vs, result, evalExpr(m, c, f))
    of TIntersect:
      c.into:
        result = evalExpr(m, c, f)
        while c.hasMore:
          result = intersect(m.vs, result, evalExpr(m, c, f))
    of TSetminus:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        result = setminus(m.vs, a, b)
    of TCard:
      c.into:
        result = buildValue(m.vs):
          t.addInt card(evalExpr(m, c, f))
    of TSet:
      c.into:
        var xs = evalArgs(m, c, f)
        result = sortedUniqueSet(m.vs, xs)
    of TSeq:
      c.into:
        let xs = evalArgs(m, c, f)
        result = buildValue(m.vs):
          t.buildTree VTSeq:
            for e in xs:
              t.addValue e
    of TLen:
      c.into:
        let s = evalExpr(m, c, f)
        case kind(s)
        of vkSeq, vkSet:
          result = buildValue(m.vs):
            t.addInt len(s)
        else: raiseEval("len on non-seq/set")
    of TAppend:
      c.into:
        let s = evalExpr(m, c, f)
        let x = evalExpr(m, c, f)
        if kind(s) != vkSeq: raiseEval("append needs seq")
        result = buildValue(m.vs):
          t.buildTree VTSeq:
            for e in items(s):
              t.addValue e
            t.addValue x
    of TConcat:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        if kind(a) != vkSeq or kind(b) != vkSeq: raiseEval("concat needs seqs")
        result = buildValue(m.vs):
          t.buildTree VTSeq:
            for e in items(a):
              t.addValue e
            for e in items(b):
              t.addValue e
    of TRange:
      c.into:
        let lo = evalExpr(m, c, f)
        let hi = evalExpr(m, c, f)
        if kind(lo) != vkInt or kind(hi) != vkInt: raiseEval("range needs ints")
        result = buildValue(m.vs):
          t.buildTree VTSet:
            var i = getInt(lo)
            while i <= getInt(hi):
              t.addInt i
              inc i
    of TFun:
      c.into:
        var pairs: seq[(Value, Value)] = @[]
        while c.hasMore:
          expectTag(c, TMapsto)
          c.into:
            let k = evalExpr(m, c, f)
            let v = evalExpr(m, c, f)
            pairs.add (k, v)
        pairs.sort(proc (a, b: (Value, Value)): int = cmpValue(a[0], b[0]))
        result = buildValue(m.vs):
          t.buildTree VTFun:
            for (k, v) in pairs:
              t.addMapsto k, v
    of TFunof:
      c.into:
        result = evalFunof(m, c, f)
    of TSetcomp:
      c.into:
        result = evalSetcomp(m, c, f)
    of TExcept:
      c.into:
        result = evalExcept(m, c, f)
    of TDomain:
      c.into:
        result = domainOf(m.vs, evalExpr(m, c, f))
    of TApply:
      c.into:
        let fn = evalExpr(m, c, f)
        let arg = evalExpr(m, c, f)
        result = applyFun(fn, arg)
    of TRecord:
      c.into:
        var fields: seq[(SymId, Value)] = @[]
        while c.hasMore:
          expectTag(c, TKv)
          c.into:
            let k = takeSymId(c)
            let v = evalExpr(m, c, f)
            fields.add (k, v)
        fields.sort(proc (a, b: (SymId, Value)): int =
          cmp(a[0].uint32, b[0].uint32))
        result = buildValue(m.vs):
          t.buildTree VTRecord:
            for (k, v) in fields:
              t.addKv k, v
    of TLet:
      c.into:
        result = evalLet(m, c, f)
    of TChoose:
      c.into:
        result = evalChoose(m, c, f)
    of TIf:
      c.into:
        let cond = asBool(evalExpr(m, c, f))
        if cond:
          result = evalExpr(m, c, f)
          if c.hasMore: c.skip
        else:
          c.skip
          result = evalExpr(m, c, f)
    of TExists, TForall:
      c.into:
        let binder = takeSymId(c)
        let dom = evalExpr(m, c, f)
        if kind(dom) != vkSet: raiseEval("quantifier domain must be a set")
        var body = c
        c.skip
        if tag == TExists:
          result = buildValue(m.vs):
            t.addBool false
          for e in items(dom):
            let fr = f.withBind(binder, e)
            var b = body
            if asBool(evalExpr(m, b, fr)):
              result = buildValue(m.vs):
                t.addBool true
              break
        else:
          result = buildValue(m.vs):
            t.addBool true
          for e in items(dom):
            let fr = f.withBind(binder, e)
            var b = body
            if not asBool(evalExpr(m, b, fr)):
              result = buildValue(m.vs):
                t.addBool false
              break
    of TGt:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(getInt(a) > getInt(b))
    of TGe:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(getInt(a) >= getInt(b))
    of TLt:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(getInt(a) < getInt(b))
    of TLe:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addBool(getInt(a) <= getInt(b))
    of TPlus:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addInt(getInt(a) + getInt(b))
    of TMinus:
      c.into:
        let a = evalExpr(m, c, f); let b = evalExpr(m, c, f)
        result = buildValue(m.vs):
          t.addInt(getInt(a) - getInt(b))
    of TImplies:
      c.into:
        if asBool(evalExpr(m, c, f)):
          result = buildValue(m.vs):
            t.addBool(asBool(evalExpr(m, c, f)))
        else:
          c.skip
          result = buildValue(m.vs):
            t.addBool true
    of TField:
      result = buildValue(m.vs):
        t.addNull
      c.into:
        let rec = evalExpr(m, c, f)
        let fld = takeSymId(c)
        if kind(rec) != vkRecord: raiseEval("field: not a record")
        var found = false
        for (k, v) in fields(rec):
          if k == fld:
            result = v
            found = true
            break
        if not found: raiseEval("field missing: " & m.pool.poolSym(fld))
    of TEmptySet:
      result = buildValue(m.vs):
        t.buildTree VTSet:
          discard
      c.skip
    of TEmptySeq:
      result = buildValue(m.vs):
        t.buildTree VTSeq:
          discard
      c.skip
    of TPrime, TUnchanged:
      raiseEval("prime/unchanged only valid in actions")
    else:
      raiseEval("cannot evaluate tag as expression: " & $tag)
  else:
    raiseEval("unexpected kind in expr: " & $c.kind)

# ── Actions ──────────────────────────────────────────────────────────────

proc containsPrime(m: Module; c: Cursor; visiting: var HashSet[SymId]): bool =
  case c.kind
  of Symbol:
    if c.symId in m.defs:
      if c.symId in visiting:
        raiseEval("recursive def in action: " & m.pool.poolSym(c.symId))
      visiting.incl c.symId
      result = containsPrime(m, m.defs[c.symId].body, visiting)
      visiting.excl c.symId
    else:
      result = false
  of TagLit:
    if c.isTag(TPrime) or c.isTag(TUnchanged): return true
    var s = sub(c)
    while s.hasMore:
      if containsPrime(m, s, visiting): return true
      s.skip
    result = false
  else:
    result = false

proc containsPrime*(m: Module; c: Cursor): bool =
  ## Follow def references, rejecting cycles instead of overflowing the stack.
  ## A prime-free disjunction is a short-circuiting state predicate.
  var visiting = initHashSet[SymId]()
  containsPrime(m, c, visiting)

proc evalAction*(m: Module; c: var Cursor; f: Frame): seq[Frame] =
  case c.kind
  of Symbol:
    let s = c.symId
    c.inc
    if s in m.defs:
      var body = m.defs[s].body
      return evalAction(m, body, f)
    let v = evalSymRef(m, s, f)
    if kind(v) == vkBool and getBool(v):
      return @[f]
    return @[]
  of TagLit:
    let tag = tlaTag(c.cursorTagId)
    case tag
    of TTrue:
      c.skip; return @[f]
    of TFalse:
      c.skip; return @[]
    of TAnd:
      result = @[f]
      c.into:
        while c.hasMore:
          var next: seq[Frame] = @[]
          var child = c
          for fr in result:
            var ch = child
            for nfr in evalAction(m, ch, fr):
              next.add nfr
          result = next
          if result.len == 0:
            while c.hasMore: c.skip
            return
          c.skip
    of TOr:
      if not containsPrime(m, c):
        # Pure state-predicate disjunction: evaluate as a short-circuiting
        # boolean guard (TLC semantics), not as branching actions. This avoids
        # evaluating later disjuncts that the earlier ones guard against, e.g.
        # `(or (eq old null) (apply edges[dest] old))` with old = null.
        var tmp = c
        let v = evalExpr(m, tmp, f)
        c.skip
        result = (if asBool(v): @[f] else: @[])
      else:
        result = @[]
        c.into:
          while c.hasMore:
            var child = c
            for nfr in evalAction(m, child, f):
              result.add nfr
            c.skip
    of TNot:
      c.into:
        let v = evalExpr(m, c, f)
        if asBool(v): result = @[]
        else: result = @[f]
    of TExists:
      result = @[]
      c.into:
        let binder = takeSymId(c)
        let dom = evalExpr(m, c, f)
        if kind(dom) != vkSet: raiseEval("exists domain must be a set")
        var body = c
        c.skip
        for e in items(dom):
          let fr = f.withBind(binder, e)
          var b = body
          for nfr in evalAction(m, b, fr):
            result.add nfr
    of TForall:
      c.into:
        let binder = takeSymId(c)
        let dom = evalExpr(m, c, f)
        if kind(dom) != vkSet: raiseEval("forall domain must be a set")
        var body = c
        c.skip
        for e in items(dom):
          let fr = f.withBind(binder, e)
          var b = body
          if not asBool(evalExpr(m, b, fr)):
            return @[]
        result = @[f]
    of TPrime:
      c.into:
        let s = takeSymId(c)
        let v = evalExpr(m, c, f)
        var fr = f
        fr.primed = f.primed
        if s in fr.primed and fr.primed[s] != v:
          return @[]
        fr.primed[s] = v
        result = @[fr]
    of TUnchanged:
      c.into:
        var fr = f
        fr.primed = f.primed
        while c.hasMore:
          let s = takeSymId(c)
          let v = lookup(f, s)
          if s in fr.primed and fr.primed[s] != v:
            return @[]
          fr.primed[s] = v
        result = @[fr]
    of TEq:
      c.into:
        let a = evalExpr(m, c, f)
        let b = evalExpr(m, c, f)
        if a == b: result = @[f]
        else: result = @[]
    of TLet:
      c.into:
        var fr = f
        while c.hasMore and c.isTag(TBind):
          c.into:
            let s = takeSymId(c)
            let v = evalExpr(m, c, fr)
            fr = fr.withBind(s, v)
        result = evalAction(m, c, fr)
    of TIf:
      c.into:
        let cond = asBool(evalExpr(m, c, f))
        if cond:
          var th = c
          result = evalAction(m, th, f)
          c.skip
          if c.hasMore: c.skip
        else:
          c.skip
          result = evalAction(m, c, f)
    else:
      var tmp = c
      let v = evalExpr(m, tmp, f)
      c.skip
      if asBool(v): result = @[f]
      else: result = @[]
  else:
    var tmp = c
    let v = evalExpr(m, tmp, f)
    c.skip
    if kind(v) == vkBool and getBool(v): result = @[f]
    else: result = @[]

proc frameToState*(m: Module; f: Frame): State =
  result = State(vals: initTable[SymId, Value]())
  for v in m.variables:
    if v in f.primed:
      result.vals[v] = f.primed[v]
    elif v in f.env:
      result.vals[v] = f.env[v]
    else:
      raiseEval("variable not determined in next state: " & m.pool.poolSym(v))

proc initialStates*(m: Module): seq[State] =
  result = @[]
  var f = Frame(
    env: m.env,
    primed: initTable[SymId, Value](),
    atStack: @[])
  var body = m.initBody
  let frames = evalAction(m, body, f)
  for fr in frames:
    var st = State(vals: initTable[SymId, Value]())
    for v in m.variables:
      if v notin fr.primed:
        raiseEval("Init did not assign " & m.pool.poolSym(v))
      st.vals[v] = fr.primed[v]
    result.add st

proc successors*(m: Module; st: State): seq[State] =
  result = @[]
  var f = Frame(
    env: m.env,
    primed: initTable[SymId, Value](),
    atStack: @[])
  for k, v in st.vals:
    f.env[k] = v
  var body = m.nextBody
  let frames = evalAction(m, body, f)
  var seen = initTable[State, bool]()
  for fr in frames:
    var fr2 = fr
    for v in m.variables:
      if v notin fr2.primed:
        fr2.primed[v] = st.vals[v]
    let nxt = frameToState(m, fr2)
    if nxt notin seen:
      seen[nxt] = true
      result.add nxt

proc checkInvariant*(m: Module; st: State; inv: Cursor): bool =
  var f = Frame(
    env: m.env,
    primed: initTable[SymId, Value](),
    atStack: @[])
  for k, v in st.vals:
    f.env[k] = v
  var body = inv
  asBool(evalExpr(m, body, f))
