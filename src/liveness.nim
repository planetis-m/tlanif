## Finite []<>Goal checking under WF_vars(A), including implicit stuttering.
## A fair goal-false SCC contains, for each group, either a disabling state
## or a nonstuttering group edge. Strong connectivity joins those witnesses
## into one repeated closed walk. Conversely any fair infinite behavior has
## such witnesses among its infinitely recurring states/edges.

import std/[tables, sets, strutils]
import tlanif_model, value, eval, compile, statecodec

type
  LiveStatus* = enum
    TLivePass, TSafetyFailure, TLivenessFailure, TIncomplete, TNoFairBehavior
  GoalStatus* = enum
    TGoalPass, TGoalVacuous, TGoalFailure, TGoalNoFairBehavior
  LiveOptions* = object
    goals*, fairness*: seq[string]
    maxStates*: int
    reference*: bool
  GoalResult* = object
    name*: string
    status*: GoalStatus
    prefix*, loop*: seq[State] ## loop repeats; last state equals first
  LiveResult* = object
    status*: LiveStatus
    states*, edges*, noFairContinuation*: int
    message*: string
    goals*: seq[GoalResult]
    safetyTrace*: seq[State]
  Edge = object
    target: int32
    groups: uint64
  Node = object
    key: string
    parent: int32
    goals, enabled: uint64
  Graph = object
    interns: seq[Interner]
    nodes: seq[Node]
    offsets: seq[int] ## CSR offsets, including final sentinel
    edges: seq[Edge]
  Components = object
    ofNode: seq[int32] ## -1 for excluded nodes
    offsets: seq[int]
    nodes: seq[int32]
  DfsFrame = object
    node: int32
    edge: int

proc bit(i: int): uint64 {.inline.} = 1'u64 shl i

proc groupMask(count: int): uint64 =
  if count == 64: high(uint64) else: bit(count) - 1

proc selectedDefs(m: Module; names: seq[string]): seq[Cursor] =
  if names.len > 64: raiseEval("at most 64 goals or fairness groups are supported")
  var seen = initHashSet[string]()
  var selected = initHashSet[SymId]()
  for name in names:
    if name.len == 0 or seen.containsOrIncl(name):
      raiseEval("empty or duplicate selected definition: " & name)
    var matches: seq[SymId]
    for s in m.defs.keys:
      let full = m.pool.poolSym(s)
      if full == name or full.split('.')[0] == name:
        matches.add s
    if matches.len != 1:
      raiseEval("unknown or ambiguous selected definition: " & name)
    if selected.containsOrIncl(matches[0]):
      raiseEval("duplicate selected definition: " & name)
    result.add m.defs[matches[0]].body

proc validateOptions(m: Module; opts: LiveOptions) =
  if opts.goals.len == 0: raiseEval("liveness requires at least one selected goal")
  if opts.maxStates <= 0 or opts.maxStates > int(high(int32)):
    raiseEval("liveness state cap must be in 1..2147483647")
  var vars = initHashSet[SymId]()
  for v in m.stutterVars: vars.incl v
  if vars.len != m.variables.len or m.stutterVars.len != m.variables.len:
    raiseEval("liveness requires a complete, duplicate-free stutter tuple")
  for v in m.variables:
    if v notin vars: raiseEval("liveness requires every variable in the stutter tuple")

proc actionStates(m: Module; st: State; action: Cursor): seq[State] =
  var f = Frame(env: m.env, primed: initTable[SymId, Value]())
  for k, v in st.vals: f.env[k] = v
  var body = action
  for fr in evalAction(m, body, f):
    result.add frameToState(m, fr)

proc stateAt(g: Graph; m: Module; id: int32): State =
  decodeState(m, unpackState(g.interns, g.nodes[id].key))

proc prefix(g: Graph; m: Module; entry: int32): seq[State] =
  var ids: seq[int32]
  var id = entry
  while id >= 0:
    ids.add id
    id = g.nodes[id].parent
  for i in countdown(ids.high, 0): result.add stateAt(g, m, ids[i])

# ── Iterative Tarjan SCCs ──────────────────────────────────────────────

proc components(g: Graph; excludedGoal: uint64): Components =
  let n = g.nodes.len
  var index = newSeq[int](n)
  var low = newSeq[int](n)
  var onStack = newSeq[bool](n)
  var stack: seq[int32]
  var dfs: seq[DfsFrame]
  var clock = 0
  result.ofNode = newSeq[int32](n)
  for i in 0 ..< n:
    index[i] = -1
    result.ofNode[i] = -1
  result.offsets = @[0]
  template enter(v: int32) =
    index[v] = clock
    low[v] = clock
    inc clock
    onStack[v] = true
    stack.add v
    dfs.add DfsFrame(node: v, edge: g.offsets[v])
  for root in 0 ..< n:
    if index[root] < 0 and (g.nodes[root].goals and excludedGoal) == 0:
      enter(int32(root))
      while dfs.len > 0:
        let v = dfs[^1].node
        if dfs[^1].edge < g.offsets[v + 1]:
          let w = g.edges[dfs[^1].edge].target
          inc dfs[^1].edge
          if (g.nodes[w].goals and excludedGoal) == 0:
            if index[w] < 0:
              enter(w)
            elif onStack[w]:
              low[v] = min(low[v], index[w])
        else:
          discard dfs.pop()
          if dfs.len > 0:
            let p = dfs[^1].node
            low[p] = min(low[p], low[v])
          if low[v] == index[v]:
            let component = int32(result.offsets.len - 1)
            var w: int32
            while true:
              w = stack.pop()
              onStack[w] = false
              result.ofNode[w] = component
              result.nodes.add w
              if w == v: break
            result.offsets.add result.nodes.len

proc fairComponent(g: Graph; cs: Components; component: int;
                   required: uint64): bool =
  var satisfied = 0'u64
  for i in cs.offsets[component] ..< cs.offsets[component + 1]:
    let v = cs.nodes[i]
    satisfied = satisfied or (not g.nodes[v].enabled)
    for e in g.offsets[v] ..< g.offsets[v + 1]:
      if cs.ofNode[g.edges[e].target] == int32(component):
        satisfied = satisfied or g.edges[e].groups
  (satisfied and required) == required

proc fairContinuations(g: Graph; required: uint64): seq[bool] =
  ## Reverse reachability from all fair SCCs. Report excluded finite prefixes
  ## as well as the case where the assumptions admit no behavior anywhere.
  let cs = components(g, 0)
  result = newSeq[bool](g.nodes.len)
  var queue: seq[int32]
  for c in 0 ..< cs.offsets.len - 1:
    if fairComponent(g, cs, c, required):
      for i in cs.offsets[c] ..< cs.offsets[c + 1]:
        let v = cs.nodes[i]
        result[v] = true
        queue.add v
  var offsets = newSeq[int](g.nodes.len + 1)
  for e in g.edges: inc offsets[e.target + 1]
  for i in 1 ..< offsets.len: offsets[i] += offsets[i - 1]
  var incoming = newSeq[int32](g.edges.len)
  var positions = offsets
  for v in 0 ..< g.nodes.len:
    for e in g.offsets[v] ..< g.offsets[v + 1]:
      let w = g.edges[e].target
      incoming[positions[w]] = int32(v)
      inc positions[w]
  var head = 0
  while head < queue.len:
    let w = queue[head]
    inc head
    for i in offsets[w] ..< offsets[w + 1]:
      let v = incoming[i]
      if not result[v]:
        result[v] = true
        queue.add v

# ── Fair closed walks and independent reference validation ─────────────

proc appendPath(g: Graph; cs: Components; component: int32;
                target: int32; walk: var seq[int32];
                parents: var seq[int32]; touched: var seq[int32]) =
  let source = walk[^1]
  if source == target: return
  for v in touched: parents[v] = -1
  touched.setLen 0
  parents[source] = source
  touched.add source
  var head = 0
  while head < touched.len and parents[target] < 0:
    let v = touched[head]
    inc head
    for e in g.offsets[v] ..< g.offsets[v + 1]:
      let w = g.edges[e].target
      if cs.ofNode[w] == component and parents[w] < 0:
        parents[w] = v
        touched.add w
  if parents[target] < 0: raiseEval("internal error: disconnected SCC witness")
  var path: seq[int32]
  var v = target
  while v != source:
    path.add v
    v = parents[v]
  for i in countdown(path.high, 0): walk.add path[i]

proc fairWalk(g: Graph; cs: Components; component, groups: int): seq[int32] =
  let entry = cs.nodes[cs.offsets[component]]
  result = @[entry]
  var parents = newSeq[int32](g.nodes.len)
  for p in parents.mitems: p = -1
  var touched: seq[int32]
  for group in 0 ..< groups:
    var source = -1'i32
    var target = -1'i32
    for i in cs.offsets[component] ..< cs.offsets[component + 1]:
      let v = cs.nodes[i]
      if (g.nodes[v].enabled and bit(group)) == 0:
        source = v
        target = -1
        break
      if source < 0:
        for e in g.offsets[v] ..< g.offsets[v + 1]:
          if cs.ofNode[g.edges[e].target] == int32(component) and
              (g.edges[e].groups and bit(group)) != 0:
            source = v
            target = g.edges[e].target
            break
    if source < 0: raiseEval("internal error: missing fairness witness")
    appendPath(g, cs, int32(component), source, result, parents, touched)
    if target >= 0: result.add target
  appendPath(g, cs, int32(component), entry, result, parents, touched)
  if result.len == 1: result.add entry # implicit stuttering

proc validateWitness*(m: Module; opts: LiveOptions; goal: GoalResult) =
  ## Re-evaluate every transition, goal and fairness obligation with eval.nim.
  let goals = selectedDefs(m, @[goal.name])
  let actions = selectedDefs(m, opts.fairness)
  if goal.prefix.len == 0 or goal.loop.len < 2 or
      goal.prefix[^1] != goal.loop[0] or goal.loop[^1] != goal.loop[0]:
    raiseEval("internal error: liveness witness is not a lasso")
  if goal.prefix[0] notin initialStates(m):
    raiseEval("internal error: witness does not start in Init")
  for path in [goal.prefix, goal.loop]:
    for i in 0 ..< path.len:
      if not checkInvariant(m, path[i], m.checkBody):
        raiseEval("internal error: unsafe witness state")
      if i + 1 < path.len and path[i] != path[i+1] and
          path[i+1] notin successors(m, path[i]):
        raiseEval("internal error: invalid witness transition")
  var satisfied = 0'u64
  for i in 0 ..< goal.loop.len - 1:
    let st = goal.loop[i]
    let next = goal.loop[i+1]
    if checkInvariant(m, st, goals[0]):
      raiseEval("internal error: witness loop reaches goal")
    for j, action in actions:
      var enabled = false
      for successor in actionStates(m, st, action):
        if successor != st:
          enabled = true
          if successor == next: satisfied = satisfied or bit(j)
      if not enabled: satisfied = satisfied or bit(j)
  if (satisfied and groupMask(actions.len)) != groupMask(actions.len):
    raiseEval("internal error: emitted walk is not weakly fair")

# ── Full reachable graph, shared across selected goals ─────────────────

proc checkLiveness*(m: Module; opts: LiveOptions): LiveResult =
  validateOptions(m, opts)
  let goals = selectedDefs(m, opts.goals)
  let actions = selectedDefs(m, opts.fairness)
  # Compile even in reference mode: reject unsupported/recursive expressions
  # before exploration and keep the two modes' accepted inputs identical.
  let cm = compileModule(m, goals, actions)
  var g = Graph(interns: newSeq[Interner](m.variables.len))
  var visited = initTable[string, int32]()
  proc addState(enc: string; parent: int32): int32 =
    let key = internState(g.interns, enc)
    visited.withValue(key, hit):
      return hit[]
    if g.nodes.len >= opts.maxStates: return -1
    result = int32(g.nodes.len)
    visited[key] = result
    g.nodes.add Node(key: key, parent: parent)
  template incomplete() =
    return LiveResult(status: TIncomplete, states: g.nodes.len,
      edges: g.edges.len, message: "incomplete: state limit exceeded (" &
      $opts.maxStates & "); no liveness conclusion")
  for st in initialStates(m):
    if addState(encodeState(m, st), -1) < 0: incomplete()
  var head = 0
  while head < g.nodes.len:
    let enc = unpackState(g.interns, g.nodes[head].key)
    loadState(cm, enc)
    var st: State
    if opts.reference: st = decodeState(m, enc)
    let invOk = if opts.reference: checkInvariant(m, st, m.checkBody)
                else: checkInv(cm)
    if not invOk:
      return LiveResult(status: TSafetyFailure, states: g.nodes.len,
        edges: g.edges.len, message: "invariant violated during liveness exploration",
        safetyTrace: prefix(g, m, int32(head)))
    for i, goal in goals:
      let holds = if opts.reference: checkInvariant(m, st, goal)
                  else: checkGoal(cm, i)
      if holds: g.nodes[head].goals = g.nodes[head].goals or bit(i)
    # Deduplicate Next successors, then OR every matching action membership.
    # Fairness enabledness includes action successors outside Next and outside
    # goal-false SCCs; it is computed before either restriction.
    var outgoing = initTable[string, uint64]()
    var order: seq[string] = @[enc]
    outgoing[enc] = 0 # implicit always-stutter edge at every state
    proc emitNext(successor: string) =
      if successor notin outgoing:
        outgoing[successor] = 0
        order.add successor
    if opts.reference:
      for successor in successors(m, st): emitNext(encodeState(m, successor))
    else:
      runNext(cm, proc() =
        var successor = ""
        encodeSuccessor(cm, successor)
        emitNext(successor))
    for j, action in actions:
      proc label(successor: string) =
        if successor != enc:
          g.nodes[head].enabled = g.nodes[head].enabled or bit(j)
          outgoing.withValue(successor, membership):
            membership[] = membership[] or bit(j)
      if opts.reference:
        for successor in actionStates(m, st, action): label(encodeState(m, successor))
      else:
        runFairAction(cm, j, proc() =
          var successor = ""
          encodeSuccessor(cm, successor)
          label(successor))
    g.offsets.add g.edges.len
    for successor in order:
      let target = addState(successor, int32(head))
      if target < 0: incomplete()
      g.edges.add Edge(target: target, groups: outgoing[successor])
    inc head
  g.offsets.add g.edges.len
  result = LiveResult(status: TLivePass, states: g.nodes.len, edges: g.edges.len)
  let required = groupMask(actions.len)
  let admissible = fairContinuations(g, required)
  for possible in admissible:
    if not possible: inc result.noFairContinuation
  if g.nodes.len == 0 or result.noFairContinuation == g.nodes.len:
    result.status = TNoFairBehavior
    result.message = "no admissible fair behavior; no progress assurance"
    for i, name in opts.goals:
      var allTrue = true
      for node in g.nodes:
        if (node.goals and bit(i)) == 0: allTrue = false
      result.goals.add GoalResult(name: name,
        status: (if allTrue: TGoalVacuous else: TGoalNoFairBehavior))
    return
  for i, name in opts.goals:
    let cs = components(g, bit(i))
    var goal = GoalResult(name: name, status: TGoalPass)
    if cs.nodes.len == 0: goal.status = TGoalVacuous
    var bad = -1
    for c in 0 ..< cs.offsets.len - 1:
      if bad < 0 and fairComponent(g, cs, c, required): bad = c
    if bad >= 0:
      goal.status = TGoalFailure
      result.status = TLivenessFailure
      let walk = fairWalk(g, cs, bad, actions.len)
      goal.prefix = prefix(g, m, walk[0])
      for v in walk: goal.loop.add stateAt(g, m, v)
      validateWitness(m, opts, goal)
    result.goals.add goal
  result.message = if result.status == TLivePass: "bounded liveness passed"
                   else: "liveness violated"

proc formatLiveness*(m: Module; r: LiveResult): string =
  result = r.message & " (" & $r.states & " states, " & $r.edges & " edges)\n"
  if r.noFairContinuation > 0:
    result.add $r.noFairContinuation & " reachable states have no admissible fair continuation\n"
  proc show(st: State): string =
    for v in m.variables:
      if result.len > 0: result.add ", "
      result.add m.pool.poolSym(v) & " = "
      toString(st.vals[v], result)
  for i, st in r.safetyTrace:
    result.add "  state " & $i & ": " & show(st) & "\n"
  for goal in r.goals:
    result.add goal.name & ": "
    case goal.status
    of TGoalPass: result.add "pass\n"
    of TGoalVacuous: result.add "vacuous (no reachable goal-false states)\n"
    of TGoalNoFairBehavior: result.add "no fair behavior; no progress assurance\n"
    of TGoalFailure:
      result.add "FAIL []<>" & goal.name & "\n"
      result.add "  shortest BFS prefix:\n"
      for i, st in goal.prefix:
        result.add "    " & $i & ": " & show(st) & "\n"
      result.add "  repeating fair walk (last state returns to loop entry):\n"
      for i, st in goal.loop:
        result.add "    " & $i & ": " & show(st) & "\n"
      result.add "  transitions and weak fairness verified with reference evaluator\n"
