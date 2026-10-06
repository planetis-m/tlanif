# tlanif
Small TLA+ implementation based on NIF.

Parses a NIF dialect of untyped TLA-style specs (Symbol/SymbolDef names,
operator tags) and checks safety invariants by BFS over finite models.
An opt-in mode also checks named progress predicates under weak fairness.

Build:

```sh
nim c -d:release -o:bin/tlanif src/tlanif.nim
```

Run:
  bin/tlanif examples/mutex.nif
  bin/tlanif examples/mutex_bug.nif

Nim's `--mm:atomicArc` destructor: `nimDecRefIsLast` with the
uniquely-referenced fast path. The three files differ only in the `Decide`
action:

  bin/tlanif examples/atomicarc.nif         # verifies, 40 states
  bin/tlanif examples/atomicarc_bug.nif     # leak: the threading issue 45 shape
  bin/tlanif examples/atomicarc_cursor.nif  # use-after-free: cursor resurrection

Two things that bite when writing specs:

- NIF comments are `#text#` and attach to a token. A standalone `# ...` line
  is not a comment: it swallows the rest of the file and the reader then dies
  with "beginRead with unclosed tags".
- A quantifier-bound local is used WITHOUT the trailing dot (binder `:t.0`,
  use `t.0`). Writing `t.0.` makes it a module-qualified symbol, which fails
  later with a confusing "unbound symbol: t.0.<module>".

Quick overview over the codebase:

| Module        | description        |
|---------------|--------------------|
|  tlanif_model | tags + load helpers |
|  value        | finite values (bool/int/model/set/seq/fun/record) |
|  eval         | expression + action interpreter |
|  loader       | module wiring (constants/variables/models/defs/spec/check) |
|  explore      | BFS explorer + counterexamples |
|  compile      | compiled expression/action evaluation |
|  pexplore     | parallel safety BFS |
|  statecodec   | exact byte encoding + per-variable state interning |
|  liveness     | reachable graph + iterative SCCs + fair witnesses |
|  tlanif       | CLI |

## Bounded liveness

```sh
bin/tlanif --live:Goal examples/live_progress.nif
# fails: the initial state can stutter forever
bin/tlanif --live:Goal --fair:FairProgress examples/live_progress.nif
# passes under weak fairness
bin/tlanif --live:Goal --fair:FairProgress --max-states:1 examples/live_progress.nif
# incomplete: the state bound prevents a conclusion
```

- `--live:A,B` selects progress predicates. Each must hold infinitely often
  on every infinite behavior admitted by the scheduling assumptions (`[]<>Goal`).
- `--fair:A,B` selects weak-fairness action groups: an action that stays enabled
  continuously must occur infinitely often. An `or` or existential action is one
  group, rather than separate assumptions for its branches or instances.
- `--max-states:N` bounds exploration (default 100000). Exhaustion reports
  **incomplete**, never a pass.

Goals and fairness actions are ordinary definitions; their names do not select
them automatically. Safety is checked throughout, and multiple goals share one
reachable graph. Failures show a finite prefix and a repeating fair walk.

Stuttering is allowed at every state, including deadlocks. Fairness counts only
steps that change the full state; no-op actions cannot discharge it. Weak fairness
permits starvation when an action is disabled repeatedly. Impossible fairness
assumptions are reported without claiming progress, and goals with no reachable
false states are marked vacuous.

For a pending bit that persists until resolution, `Goal = not pending` expresses
response progress: a request cannot stay pending forever. Aggregate completion
predicates may still permit an individual operation to starve. A pass establishes
the selected finite model contracts under the stated assumptions, with no guarantee
about production scheduling, real-time bounds, unbounded workloads or memory safety.

Liveness requires a complete stutter tuple and rejects the existing safety options
`--jobs` and `--sym`. General temporal logic and strong fairness are unsupported.

## Maintainer verification

Build the CLI first, then run the native assertions from the repository root:

```sh
nim c -d:release -o:bin/tlanif src/tlanif.nim
nim c -d:release -o:bin/tliveness -r tests/tliveness.nim
```

The suite compares compiled/reference evaluation, searches fair closed walks with
an independent oracle on 120 small models, validates and corrupt-tests witnesses,
checks deep and bounded stress graphs, and compares the existing safety examples
with four-worker exploration. [tests/tliveness.nim](tests/tliveness.nim) contains
the regression cases and expected outcomes.

Liveness defaults to a single compiled worker. Use `--live-eval:reference` for
differential verification:

```sh
bin/tlanif --live:Goal --fair:FairProgress --live-eval:reference examples/live_progress.nif
```

The implementation accepts bare or qualified definition names, rejects unknown,
ambiguous, empty or duplicate selections, and supports at most 64 goals and 64
fairness groups. Actions use the existing evaluator's omitted-variable stuttering
and match transitions by exact full state, retaining overlapping memberships.
Enabledness includes escape edges before goal-false SCC analysis. Every emitted
walk is reference-validated; only the BFS prefix to its chosen entry is shortest.
Strong connectivity joins each group's disabling state or internal action edge
into a fair closed walk; any fair infinite behavior must supply those witnesses
among its recurring states and edges.

| Exit | Liveness result |
|---:|---|
| 0 | Exhaustive bounded pass (vacuous goals are identified) |
| 1 | Invalid input or unsupported option combination |
| 2 | Safety invariant failure |
| 3 | Liveness failure with a fair counterexample |
| 4 | Incomplete exploration |
| 5 | No admissible fair behavior, including empty Init |

The checker also reports reachable states with no fair continuation. Safety-only
exit codes are unchanged, including exit 2 for cap exhaustion. Only the last
`check` form takes effect; combine safety predicates in one invariant.
