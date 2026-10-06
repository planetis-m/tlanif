# Implement native bounded liveness in Tlanif

Start in `~/Projects/tlanif`, on branch `feature/native-liveness`. Implement,
validate and locally commit the work. **Do not push.** The checkout contains
the project setup and this handoff as a committed baseline.

Everything needed for this task is in this workspace or in this prompt.
Implement and verify the model checker's feature itself. Applying the completed
feature to another project's models is a separate task.

Use Tlanif's existing Nim/NIF machinery and dependencies. Do not introduce Brian,
Python, JSON graph interchange or a CLI-output parser. The user chose a native
Tlanif extension and asked for a small, fast implementation. No liveness backend
has been written yet; perform fresh validation rather than relying on earlier
claims about an external checker.

## Outcome

Add an explicit opt-in mode for checking named progress predicates under named
weak-fairness action assumptions. Keep all existing safety-only behavior and
commands working. Produce reproducible pass/failure/incomplete results, and
readable fair counterexamples consisting of a finite prefix and repeating walk.

Implement a bounded `[]<>Goal` contract first: on every admissible infinite
behavior, the selected state predicate becomes true infinitely often. Equivalently,
no fair behavior eventually keeps it false forever. This is not general temporal
logic checking. Some supplied predicates encode response progress because pending
state persists until resolution; describe that interpretation precisely.

A CLI such as `--live:GoalShutdown,GoalOperations` plus
`--fair:FairWorker,FairNetwork,FairConsumer,FairOwner` would avoid new NIF tags.
These option names are suggestions. Make a reasonable implementation choice and
document it; do not stop to ask for preferences. Selecting names must be explicit:
the existing `Fair*` and `Goal*` definitions are ordinary definitions, and not all
of them are required properties. Reject invalid names and unsupported combinations.

An exhaustive finite check establishes the selected bounded model property under
its stated assumptions. It does not prove production workers, libcurl, real-time
bounds, unbounded workloads, OS scheduling or memory safety correct.

## Correctness requirements

1. Explore the full reachable graph using Tlanif semantics and continue checking
   the model's safety invariant. Keep edges needed for cycle analysis, not only
   the BFS discovery tree.
2. Include implicit stuttering from `always-stutter` at every state. A state with
   no enabled state-changing Next step can support an infinite stalled behavior.
3. Implement weak fairness of nonstuttering actions, corresponding to
   `WF_vars(A)` with `<A>_vars`. Returning the same full state does not count as
   a state-changing occurrence or make that nonstuttering action enabled.
4. An action group `or(A B ...)` is one fairness assumption for that disjunction.
   Do not replace it with independent fairness for each action, binder instance,
   operation or connection.
5. Determine enabledness in the full state-space semantics, before restricting
   to goal-false states. An action with only an escape edge to a goal-true state
   is still enabled; forgetting it would incorrectly accept an unfair self-loop.
6. For each goal, analyze SCCs in the reachable goal-false subgraph. A component
   supports a weakly fair infinite walk if, for every selected fairness group,
   it contains either a state disabling that nonstuttering action or an internal
   edge belonging to it. Implicit stuttering also makes singleton components
   candidates. Explain and test why the acceptance criterion is correct.
7. Preserve overlapping action memberships and fairness labels when transitions
   or successor states are deduplicated. Evaluate arbitrary selected action
   expressions correctly; do not silently assume all actions are disjoint labels.
8. Emit an actually fair closed walk. A fair SCC can contain individual simple
   cycles that are unfair. The witness must visit the required disabling states
   or include the required action edges, then return to its loop entry. Validate
   every emitted transition and the fairness of the repeated walk.
9. A state cap is incomplete/unknown, never a pass. Distinguish invalid input,
   invariant failure, liveness failure and incomplete exploration. Report vacuous
   goals with no reachable false states, and surface inconsistent fairness/no
   admissible fair continuation rather than advertising vacuous progress assurance.

Support weak fairness only initially. Do not implement strong fairness accidentally.
Reject liveness with symmetry reduction until preservation of selected properties
and action memberships is established. Do not claim shortest fair cycles if only
the prefix is a shortest BFS path.

## Existing implementation and speed

Nim 2.3.1 is available. `src/nim.cfg` supplies
`/usr/lib64/nimony/src/lib` for NIF libraries. Build from this workspace:

```sh
nim c -d:release -o:bin/tlanif src/tlanif.nim
```

The source interfaces you can reuse are:

- `loader.nim`: `loadModuleFile`, `loadModuleBuffer`, and module definition bodies.
- `eval.nim`: `initialStates`, `successors`, `evalAction`, `checkInvariant`.
- `compile.nim`: `compileModule`, `loadState`, `checkInv`, `runNext`,
  `encodeSuccessor`, `successorState`. Internal `CExpr`, `Cont`, `Ctx`, `Scope`,
  `compileExpr` and `compileAction` are private. A narrow native API to compile
  additional goals/actions against one loaded state can avoid repeated compilation
  and state decoding.
- `pexplore.nim`: exported `encodeState`/`decodeState`; private `Interner`,
  `internState`/`unpackState` already provide exact per-variable interning and
  packed state keys. Reuse or carefully extract them instead of duplicating a
  parser or storing full printed states.
- `value.nim`: values are cursor-backed. Never send `Value` cursors across threads.
  Existing workers own separate modules and exchange encoded strings.

Use compiled evaluation, compact graph storage and iterative SCC traversal.
Evaluate goals and action enabledness while exploring. Reuse the graph for all
selected goals. Format full states only for diagnostics. Measure elapsed time
and peak memory on regression cases and a larger bounded stress case; do not
guess performance numbers.

Keep a reference-evaluator route for differential validation. Existing safety
checks with no `--jobs` use reference semantics, while `--jobs:4` uses compiled
parallel exploration. Establish equivalent agreement checks for liveness.
An initial single-worker compiled liveness mode is acceptable if it is fast and
correct; document it and reject incompatible parallel options rather than
silently ignoring them. Do not rebuild the evaluator from scratch.

## Modeling details

Use the project's existing NIF syntax. Comments attach to tokens as `#...#`,
never as standalone lines. Module-level symbols have trailing dots; binder locals
do not. Init primes every variable. Definitions are acyclic. Next omissions
stutter. Keep complete stutter tuples. `case` is unsupported.

Only the last `(check ...)` currently takes effect. Combine required safety
invariants into one check instead of adding unchecked forms. Preserve that
existing behavior unless a deliberate, tested compatibility change is necessary.

## Concrete regression inputs

These complete specs can be added under `examples/` with suitable names. Add
further small fixtures or standalone assertions for the cases listed afterwards.

### Continuous progress versus unfair stutter

```text
(stmts
  (variables :pc.0.)
  (def :Init.0. (prime pc.0. 0))
  (def :Progress.0. (and (eq pc.0. 0) (prime pc.0. 1)))
  (def :Next.0. Progress.0.)
  (def :Inv.0. (in pc.0. (range 0 1)))
  (def :Goal.0. (eq pc.0. 1))
  (def :FairProgress.0. Progress.0.)
  (spec (always-stutter Init.0. Next.0. (tuple pc.0.)))
  (check Inv.0.))
```

Safety passes with two states. `[]<>Goal` fails without fairness because the
initial state can stutter forever, and passes with `WF(FairProgress)`.
This also tests that an escape edge remains enabled in a goal-false SCC.

### Pending deadlock

```text
(stmts
  (variables :pending.0.)
  (def :Init.0. (prime pending.0. (true)))
  (def :Next.0. (false))
  (def :Inv.0. (true))
  (def :Goal.0. (not pending.0.))
  (spec (always-stutter Init.0. Next.0. (tuple pending.0.)))
  (check Inv.0.))
```

Safety passes with one state. Liveness fails with a one-state stuttering loop.

### Weak fairness permits intermittent starvation

```text
(stmts
  (variables :pc.0.)
  (def :Init.0. (prime pc.0. 0))
  (def :Toggle.0.
    (and (lt pc.0. 2) (prime pc.0. (minus 1 pc.0.))))
  (def :Progress.0. (and (eq pc.0. 1) (prime pc.0. 2)))
  (def :Next.0. (or Toggle.0. Progress.0.))
  (def :Inv.0. (in pc.0. (range 0 2)))
  (def :Goal.0. (eq pc.0. 2))
  (def :FairToggle.0. Toggle.0.)
  (def :FairProgress.0. Progress.0.)
  (spec (always-stutter Init.0. Next.0. (tuple pc.0.)))
  (check Inv.0.))
```

With weak fairness for both groups, liveness still fails: `0,1,0,1,...` takes
Toggle repeatedly and disables Progress repeatedly. A strong-fairness
interpretation would wrongly eliminate that witness.

### A fair walk whose simple cycles are unfair

```text
(stmts
  (variables :pc.0.)
  (def :Init.0. (prime pc.0. 0))
  (def :A.0.
    (and (lt pc.0. 3) (prime pc.0. (if (eq pc.0. 0) 1 3))))
  (def :B.0.
    (and (lt pc.0. 3) (prime pc.0. (if (eq pc.0. 0) 2 3))))
  (def :Return.0.
    (and (in pc.0. (set 1 2)) (prime pc.0. 0)))
  (def :Next.0. (or A.0. B.0. Return.0.))
  (def :Inv.0. (in pc.0. (range 0 3)))
  (def :Goal.0. (eq pc.0. 3))
  (def :FairA.0. A.0.)
  (def :FairB.0. B.0.)
  (spec (always-stutter Init.0. Next.0. (tuple pc.0.)))
  (check Inv.0.))
```

Both A and B are continuously enabled in the bad component `{0,1,2}`, including
at states where their edges leave it. The walk `0,1,0,2,0,...` satisfies both
fairness groups and violates the goal. Either individual simple cycle is unfair.
The emitted witness must satisfy both groups, not merely cite the whole SCC.

Also cover a cycling worker with permanently pending work; overlapping groups
and duplicate edges; no-op actions; unsatisfiable fairness; vacuous goals; multiple
initial states; invalid selected definitions; cap exhaustion; and a deep graph
that verifies iterative SCC traversal. Check each supported evaluator, including
validation of emitted witnesses. Rerun existing mutex and atomicArc examples
and their intentionally failing variants in reference and parallel safety modes.

## Deliver and finish

- Native implementation, CLI help and README usage/semantics.
- Regression examples/assertions with documented commands and expected outcomes.
- A concise validation record here: exact commands, expected and observed outcomes,
  evaluator agreement, state/edge counts, benchmark timing and peak memory, and
  remaining limits. Keep it specific to this feature's tests, not external projects.
- Local commits on `feature/native-liveness`, clean final checkout, no push.
- Remove your temporary variants, source copies, graph dumps and generated
  reports/binaries after validation; preserve unrelated existing files/caches.

Make routine implementation decisions autonomously. Only stop for a genuine
blocking dependency or a permission that the environment requires. End with
a concise account of changes, checks, findings, performance and remaining limits.
