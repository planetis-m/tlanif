## TLA-on-NIF model checker — CLI entry point.

import std / [os, strutils, syncio, tables, cpuinfo]
import tlanif_model, loader, explore, pexplore, eval, value

const Help = """
tlanif — NIF-syntax TLA safety model checker

Usage:
  tlanif <spec.nif>
  tlanif --max-states:N <spec.nif>
  tlanif --jobs:N <spec.nif>        # parallel BFS with N workers (0 = auto);
                                    # also uses interned state storage
  tlanif --memo-limit:N <spec.nif>  # def-memo entry cap per module (0 = unbounded)

See examples/.
"""

proc main() =
  var maxStates = 100_000
  var symmetry = false
  var jobs = 0          # 0 = --jobs not given: sequential reference explorer
  var memoLimit = -1    # -1 = keep the loader default
  var file = ""
  for i in 1 .. paramCount():
    let a = paramStr(i)
    if a.startsWith("--max-states:"):
      maxStates = parseInt(a["--max-states:".len .. ^1])
    elif a.startsWith("--jobs:"):
      jobs = parseInt(a["--jobs:".len .. ^1])
      if jobs <= 0: jobs = countProcessors()
    elif a.startsWith("--memo-limit:"):
      memoLimit = parseInt(a["--memo-limit:".len .. ^1])
    elif a == "--sym":
      symmetry = true
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
  main()
