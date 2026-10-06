import std/[assertions, random, syncio, osproc]
import loader, liveness, eval, explore, pexplore

proc agree(input: string; options: LiveOptions; expected: LiveStatus;
           states = -1; edges = -1): LiveResult =
  let m = loadModuleBuffer(input)
  result = checkLiveness(m, options)
  var reference = options
  reference.reference = true
  let rm = loadModuleBuffer(input)
  let r = checkLiveness(rm, reference)
  doAssert result.status == expected
  doAssert formatLiveness(m, result) == formatLiveness(rm, r)
  if states >= 0: doAssert result.states == states
  if edges >= 0: doAssert result.edges == edges
  for goal in result.goals:
    if goal.status == TGoalFailure:
      validateWitness(m, options, goal)
      validateWitness(rm, reference, goal)

proc opts(fairness: seq[string] = @[]; goals = @["Goal"];
          cap = 100000): LiveOptions =
  LiveOptions(goals: goals, fairness: fairness, maxStates: cap)

proc fixture(name: string): string = readFile("examples/live_" & name & ".nif")

proc model(next, goal, defs: string; init = "(prime pc.0. 0)";
           inv = "(true)"; stutter = "pc.0."): string =
  "(stmts (variables :pc.0.) (def :Init.0. " & init & ") " &
  "(def :Next.0. " & next & ") (def :Goal.0. " & goal & ") " & defs &
  " (def :Inv.0. " & inv & ") " &
  "(spec (always-stutter Init.0. Next.0. (tuple " & stutter & "))) (check Inv.0.))"

block concrete_regressions:
  discard agree(fixture("progress"), opts(), TLivenessFailure, 2, 3)
  discard agree(fixture("progress"), opts(@["FairProgress"]), TLivePass, 2, 3)
  let deadlock = agree(fixture("deadlock"), opts(), TLivenessFailure, 1, 1)
  doAssert deadlock.goals[0].loop.len == 2
  discard agree(fixture("intermittent"), opts(@["FairToggle", "FairProgress"]),
    TLivenessFailure, 3, 6)
  let walk = agree(fixture("fair_walk"), opts(@["FairA", "FairB"]),
    TLivenessFailure, 4, 10)
  doAssert walk.goals[0].loop.len >= 5
  discard agree(fixture("pending_worker"), opts(@["FairWorker"]),
    TLivenessFailure, 2, 4)
  discard agree(fixture("groups"), opts(@["Group", "Overlap"]),
    TLivenessFailure, 3, 7)
  discard agree(fixture("groups"), opts(@["A", "B"]), TLivePass, 3, 7)
  discard agree(fixture("groups"), opts(@["Noop"]), TLivenessFailure, 3, 7)
  let vacuous = agree(fixture("groups"), opts(@[], @["Vacuous"]), TLivePass, 3, 7)
  doAssert vacuous.goals[0].status == TGoalVacuous
  let multiple = agree(fixture("groups"), opts(@["B"], @["Goal", "Vacuous", "Never"]),
    TLivenessFailure, 3, 7)
  doAssert multiple.goals[0].status == TGoalPass
  doAssert multiple.goals[1].status == TGoalVacuous
  doAssert multiple.goals[2].status == TGoalFailure
  discard agree(fixture("no_fair"), opts(@["Outside"]), TNoFairBehavior, 1, 1)
  discard agree(fixture("progress"), opts(@["FairProgress"], cap = 1), TIncomplete, 1)
  discard agree(fixture("progress"), opts(@["FairProgress"], cap = 2), TLivePass, 2, 3)

block extra_semantics:
  let multiInit = model("(false)", "(eq pc.0. 1)", "",
    "(exists :x.0 (set 0 1) (prime pc.0. x.0))")
  discard agree(multiInit, opts(), TLivenessFailure, 2, 2)
  discard agree(model("(false)", "(true)", "", "(false)"),
    opts(), TNoFairBehavior, 0, 0)
  let partial = model("(false)", "(true)",
    "(def :Fair.0. (and (eq pc.0. 0) (prime pc.0. 2)))",
    "(exists :x.0 (set 0 1) (prime pc.0. x.0))")
  let r = agree(partial, opts(@["Fair"]), TLivePass, 2, 2)
  doAssert r.noFairContinuation == 1
  discard agree(model("(prime pc.0. 1)", "(true)", "", inv = "(eq pc.0. 0)"),
    opts(), TSafetyFailure, 2)
  # let/if and quantified duplicate action membership use normal action semantics.
  let arbitrary = model("(prime pc.0. (minus 1 pc.0.))", "(false)",
    "(def :Fair.0. (let (bind :x.0 pc.0.) " &
    "(if (eq x.0 0) (prime pc.0. 1) (prime pc.0. 0))))")
  discard agree(arbitrary, opts(@["Fair"]), TLivenessFailure, 2, 4)

block invalid_inputs:
  let input = fixture("progress")
  for reference in [false, true]:
    for names in [@["Missing"], @["Goal", "Goal"], @["Goal", "Goal.0.tla"], @[""]]:
      var options = opts(goals = names)
      options.reference = reference
      doAssertRaises EvalError:
        discard checkLiveness(loadModuleBuffer(input), options)
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(input), opts(@["Missing"]))
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(input), opts(goals = @["Progress"]))
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(model("(false)", "(true)", "", stutter = "")), opts())
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(model("(false)", "(true)", "", stutter = "pc.0. pc.0.")), opts())
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(model("(false)", "(true)",
        "(def :Fair.0. Fair.0.)")), opts(@["Fair"]))
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(model("(false)", "(true)",
        "(def :Fair.0. (or (false) Fair.0.))")), opts(@["Fair"]))
    doAssertRaises EvalError:
      discard checkLiveness(loadModuleBuffer(model("(false)", "1", "")), opts())
  doAssertRaises EvalError:
    discard checkLiveness(loadModuleBuffer(input), opts(cap = 0))
  doAssertRaises EvalError:
    discard checkLiveness(loadModuleBuffer(input), opts(goals = @[]))
  doAssertRaises EvalError:
    discard checkLiveness(loadModuleBuffer(model("(false)", "(true)",
      "(def :Foo.0. (true)) (def :Foo.1. (true))")), opts(goals = @["Foo"]))

block membership_mask_boundary:
  var defs = ""
  var names: seq[string]
  for i in 0 ..< 64:
    names.add "Noop" & $i
    defs.add "(def :Noop" & $i & ".0. (unchanged pc.0.)) "
  discard agree(model("(false)", "(false)", defs), opts(names), TLivenessFailure, 1, 1)
  names.add "OneTooMany"
  doAssertRaises EvalError:
    discard checkLiveness(loadModuleBuffer(model("(false)", "(false)", defs)), opts(names))

block reject_corrupt_witnesses:
  let m = loadModuleBuffer(fixture("fair_walk"))
  let options = opts(@["FairA", "FairB"])
  let r = checkLiveness(m, options)
  var goal = r.goals[0]
  goal.loop = @[goal.loop[0], goal.loop[0]]
  doAssertRaises EvalError: validateWitness(m, options, goal)
  let start = initialStates(m)[0]
  goal.prefix = @[start]
  goal.loop = @[start, successors(m, start)[0], start]
  doAssertRaises EvalError: validateWitness(m, options, goal) # simple cycle misses B
  let im = loadModuleBuffer(fixture("intermittent"))
  let zero = initialStates(im)[0]
  let one = successors(im, zero)[0]
  let two = successors(im, one)[1]
  let bad = GoalResult(name: "Goal", status: TGoalFailure,
    prefix: @[zero], loop: @[zero, two, zero])
  doAssertRaises EvalError: validateWitness(im, opts(), bad) # illegal 0 -> 2

# Independent oracle: search (state, fulfilled fairness mask) for a closed
# nonempty walk, rather than using SCCs. Small finite graphs exhaust the
# product exactly. Action enabledness also includes edges outside Next.
type Tiny = object
  next: array[3, array[3, bool]]
  actions: array[2, array[3, array[3, bool]]]
  goals: array[3, bool]

proc reachable(t: Tiny): array[3, bool] =
  result[0] = true
  for iteration in 0 ..< 3:
    for v in 0 ..< 3:
      if result[v]:
        for w in 0 ..< 3:
          if t.next[v][w]: result[w] = true

proc closedWalk(t: Tiny; restrictGoal: bool; reach: array[3, bool]): bool =
  for entry in 0 ..< 3:
    if reach[entry] and (not restrictGoal or not t.goals[entry]):
      var seen: array[3, array[4, bool]]
      var queue = @[(entry, 0)]
      seen[entry][0] = true
      var head = 0
      while head < queue.len:
        let (v, mask) = queue[head]
        inc head
        for w in 0 ..< 3:
          if (t.next[v][w] or v == w) and (not restrictGoal or not t.goals[w]):
            var satisfied = mask
            for j in 0 ..< 2:
              var enabled = false
              for target in 0 ..< 3:
                if target != v and t.actions[j][v][target]: enabled = true
              if not enabled or (v != w and t.actions[j][v][w]):
                satisfied = satisfied or (1 shl j)
            if w == entry and satisfied == 3: return true
            if not seen[w][satisfied]:
              seen[w][satisfied] = true
              queue.add (w, satisfied)

proc actionExpr(edges: array[3, array[3, bool]]): string =
  result = "(or"
  for v in 0 ..< 3:
    for w in 0 ..< 3:
      if edges[v][w]:
        result.add " (and (eq pc.0. " & $v & ") (prime pc.0. " & $w & "))"
  result.add ")"

block product_oracle:
  var rng = initRand(71892)
  for sample in 0 ..< 120:
    var t: Tiny
    for v in 0 ..< 3:
      t.goals[v] = rand(rng, 1) == 1
      for w in 0 ..< 3:
        t.next[v][w] = rand(rng, 2) == 0
        for j in 0 ..< 2: t.actions[j][v][w] = rand(rng, 1) == 1
    var goalExpr = "(or"
    for v in 0 ..< 3:
      if t.goals[v]: goalExpr.add " (eq pc.0. " & $v & ")"
    goalExpr.add ")"
    let input = model(actionExpr(t.next), goalExpr,
      "(def :Fair0.0. " & actionExpr(t.actions[0]) & ") " &
      "(def :Fair1.0. " & actionExpr(t.actions[1]) & ")")
    let reach = reachable(t)
    let expected = if not closedWalk(t, false, reach): TNoFairBehavior
                   elif closedWalk(t, true, reach): TLivenessFailure
                   else: TLivePass
    discard agree(input, opts(@["Fair0", "Fair1"]), expected)

block deep_iterative_traversal:
  discard agree(fixture("deep"), opts(@["Step"]), TLivePass, 50001, 100001)

block bounded_product_stress:
  discard agree(fixture("stress"), opts(@["X", "Y", "Z"]), TLivePass, 100000, 400000)

block safety_compatibility:
  for file in ["mutex", "mutex_bug", "atomicarc", "atomicarc_bug", "atomicarc_cursor"]:
    let path = "examples/" & file & ".nif"
    let m = loadModuleFile(path)
    let r = explore(m)
    let p = pexplore(path, jobs = 4)
    doAssert r.ok == p.ok
    doAssert r.statesExplored == p.statesExplored
    doAssert r.message == p.message
    doAssert formatCounterexample(r) == formatCounterexample(p)
    doAssert r.ok == (file in ["mutex", "atomicarc"])
    stdout.writeLine file & ": reference/parallel agree, " & $r.statesExplored &
      " checked states, " & (if r.ok: "pass" else: "invariant failure")

block cli_rejections_and_exit_codes:
  for flags in ["--live:Goal --sym", "--live:Goal --jobs:1", "--live:Goal --jobs:0",
      "--fair:FairProgress", "--live-eval:reference", "--live:Missing", "--live:",
      "--live:Goal --live-eval:unknown", "--live:Goal --fair:"]:
    doAssert execCmdEx("bin/tlanif " & flags & " examples/live_progress.nif").exitCode == 1
  for (flags, code) in [("--live:Goal --fair:FairProgress", 0), ("--live:Goal", 3),
      ("--live:Goal --max-states:1", 4)]:
    doAssert execCmdEx("bin/tlanif " & flags & " examples/live_progress.nif").exitCode == code
  doAssert execCmdEx("bin/tlanif --live:Goal --fair:Outside examples/live_no_fair.nif").exitCode == 5
  doAssert execCmdEx("bin/tlanif examples/mutex_bug.nif").exitCode == 2
  doAssert execCmdEx("bin/tlanif --live:Inv examples/mutex_bug.nif").exitCode == 2
  doAssert execCmdEx("bin/tlanif --max-states:1 examples/mutex.nif").exitCode == 2
  doAssert execCmdEx("bin/tlanif --live:Goal --max-states:bad examples/live_progress.nif").exitCode == 1

stdout.writeLine "liveness assertions passed: fixtures, 120 product-oracle graphs, deep SCCs, safety and CLI"
