## TLA-on-NIF model checker — CLI entry point.

import std / [os, strutils, syncio, tables, cpuinfo]
import loader, explore, pexplore, eval, liveness
when defined(countApply): import value

const Help = """
tlanif — NIF-syntax TLA safety and bounded liveness model checker

Usage:
  tlanif <spec.nif>
  tlanif --max-states:N <spec.nif>
  tlanif --jobs:N <spec.nif>        # parallel BFS with N workers (0 = auto);
                                    # also uses interned state storage
  tlanif --memo-limit:N <spec.nif>  # def-memo entry cap per module (0 = unbounded)
  tlanif --sym <spec.nif>           # safety symmetry reduction
  tlanif --live:GoalA,GoalB --fair:ActionA,ActionB <spec.nif>
                                    # []<> each named goal under weak fairness

Liveness is single-worker; --jobs and --sym are rejected.
Exit: 0 pass, 1 invalid/error, 2 safety failure, 3 liveness failure,
      4 incomplete, 5 no admissible fair behavior.
Safety-only cap hits retain exit 2.

Maintainer verification:
  tlanif --live:Goal --live-eval:reference <spec.nif>
                                    # differential route (default: compiled)

See examples/.
"""

proc main() =
  var maxStates = 100_000
  var symmetry = false
  var jobs = 0          # 0 = --jobs not given: sequential reference explorer
  var memoLimit = -1    # -1 = keep the loader default
  var file = ""
  var goals, fairness: seq[string]
  var liveSeen, fairSeen, evaluatorSeen, jobsSeen: bool
  var reference = false
  for i in 1 .. paramCount():
    let a = paramStr(i)
    if a.startsWith("--max-states:"):
      maxStates = parseInt(a["--max-states:".len .. ^1])
    elif a.startsWith("--jobs:"):
      jobsSeen = true
      jobs = parseInt(a["--jobs:".len .. ^1])
      if jobs <= 0: jobs = countProcessors()
    elif a.startsWith("--memo-limit:"):
      memoLimit = parseInt(a["--memo-limit:".len .. ^1])
    elif a == "--sym":
      symmetry = true
    elif a.startsWith("--live:"):
      liveSeen = true
      goals.add a["--live:".len .. ^1].split(',')
    elif a.startsWith("--fair:"):
      fairSeen = true
      fairness.add a["--fair:".len .. ^1].split(',')
    elif a.startsWith("--live-eval:"):
      evaluatorSeen = true
      let mode = a["--live-eval:".len .. ^1]
      if mode notin ["compiled", "reference"]:
        stderr.writeLine "error: --live-eval must be compiled or reference"
        quit(1)
      reference = mode == "reference"
    elif a in ["-h", "--help"]:
      echo Help
      quit(0)
    elif a.startsWith("-"):
      stderr.writeLine "unknown option: " & a
      quit(1)
    else:
      file = a

  if file.len == 0:
    stderr.writeLine Help
    quit(1)
  if not fileExists(file):
    stderr.writeLine "file not found: " & file
    quit(1)

  try:
    if (fairSeen or evaluatorSeen) and not liveSeen:
      raiseEval("--fair and --live-eval require --live")
    if liveSeen:
      if symmetry or jobsSeen:
        raiseEval("liveness does not support --sym or --jobs")
      let m = loadModuleFile(file)
      if memoLimit >= 0: m.memoLimit = memoLimit
      let r = checkLiveness(m, LiveOptions(goals: goals, fairness: fairness,
        maxStates: maxStates, reference: reference))
      let output = formatLiveness(m, r)
      if r.status == TLivePass: stdout.write output
      else: stderr.write output
      case r.status
      of TLivePass: quit(0)
      of TSafetyFailure: quit(2)
      of TLivenessFailure: quit(3)
      of TIncomplete: quit(4)
      of TNoFairBehavior: quit(5)
    var r: CheckResult
    if jobs >= 1:
      r = pexplore.pexplore(file, maxStates, symmetry, jobs, memoLimit)
    else:
      let m = loadModuleFile(file)
      if memoLimit >= 0:
        m.memoLimit = memoLimit
      r = explore(m, maxStates, symmetry)
      let total = m.memoHits + m.memoMisses
      if total > 0:
        stderr.writeLine "memo: " & $m.memoHits & " hits / " & $total &
          " (" & $(m.memoHits * 100 div total) & "% hit, " &
          $m.memo.len & " entries)"
    when defined(countApply):
      stderr.writeLine "applyCount(main): " & $value.applyCount
    if r.ok:
      echo r.message
      quit(0)
    else:
      stderr.writeLine formatCounterexample(r)
      quit(2)
  except EvalError as e:
    stderr.writeLine "error: " & e.msg
    quit(1)

when isMainModule:
  try:
    main()
  except ValueError as e:
    stderr.writeLine "error: " & e.msg
    quit(1)
