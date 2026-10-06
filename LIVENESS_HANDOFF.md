# Handoff: native Tlanif liveness checking for Relay

Start the agent in **`~/Projects/tlanif`**, on branch **`feature/native-liveness`**.
This is the implementation repository; Relay supplies the models to validate.

```sh
cd ~/Projects/tlanif
```

Implement and validate native, bounded liveness checking in Tlanif, then use it
to check Relay's existing HTTP and WebSocket models. Complete the work rather
than returning only a design. Keep the implementation small and fast, and report
the exact guarantees, assumptions, failures and limitations.

The user selected extending Tlanif instead of maintaining a separate checker in
Relay, and then said to use whatever Tlanif already uses. Do not introduce Brian,
Python, a JSON interchange pipeline, or a wrapper that parses CLI output. Use
Tlanif's Nim/NIF machinery directly. A new JSON feature is not required.

## Read first

- `/home/ageralis/Projects/tlanif/README.md`
- `/home/ageralis/Projects/tlanif/AGENTS.md`
- `/home/ageralis/Projects/relay/AGENTS.md`
- `/home/ageralis/Projects/relay/models/README.md`
- `/home/ageralis/Projects/relay/models/REPORT.md`
- All three Relay `.nif` files, especially their `Fair*` and `Goal*` definitions.

Follow each project's conventions. Tlanif's examples are its regression suite;
it currently has no dedicated tests/CI framework. Relay tests are standalone
Nim programs with `doAssert`, not `unittest`. Use Atlas if dependency setup is
necessary; do not introduce Nimble installation instructions.

## Starting point

No liveness implementation has been written. The previous agent only read the
sources and prepared a temporary source copy. That copy was removed when this
handoff was requested. There is no backend, checker patch or partial result to
recover from it. Earlier statements about a removed external checker are not
current, reproducible validation evidence; perform fresh checks.

Tlanif's current setup/documentation changes and this handoff are committed on
`feature/native-liveness`, giving you a clean starting checkout. The user explicitly
authorized committing that state. Work directly in Tlanif; do not spend time
isolating earlier edits or preparing a separate checker in Relay. Start the agent
with Tlanif as its working directory so its normal workspace permissions apply.

Relay's latest relevant commit is `92a11ba`, following `f2cdf36` and `496e01d`.
Its production HTTP and WebSocket source files were not changed by the modeling work.
Commit completed work locally. **Never push.**

## Required behavior

Keep existing safety-only commands, exit meanings, invariant checking and
counterexamples working. Liveness must be an explicit opt-in mode. Existing
definitions named `Fair*` or `Goal*` currently have no special semantics; do not
silently activate every such definition by name convention.

Provide a documented way to select named state predicates as progress goals and
named action expressions as weak-fairness assumptions. For example, CLI options
such as `--live:GoalShutdown,GoalOperations` and
`--fair:FairWorker,FairNetwork,FairConsumer,FairOwner` would avoid new NIF tags.
The option names are a suggestion, not a requirement. Reject unknown names,
malformed choices and unsupported combinations clearly.

State the exact temporal property. A useful initial contract is to check
`[]<>Goal` for each selected predicate: under the selected weak fairness, a run
cannot eventually keep the goal false forever. This is not general LTL/TLA+
temporal checking. Some supplied goals encode response progress because their
pending state persists until resolution; document that interpretation rather
than claiming arbitrary per-request leads-to properties.

Do not confuse any of these with a liveness proof:

- A safety pass.
- Existence of a path to a goal or reverse reachability from goal states.
- A final broadcast invariant.
- An acyclic or exhausted finite prefix without analysis of infinite behaviors.
- Exploration that hit its state cap.

A complete, finite model check under explicit assumptions establishes that
bounded model property. It does not prove the Nim workers, libcurl, OS scheduling,
unbounded workloads, ARC memory safety or wall-clock deadlines correct.

## Semantics that must be correct

1. Build the complete reachable transition graph using the existing evaluator.
   Continue checking the selected safety invariant. Retain enough edges and
   fairness information to analyze cycles, not only the BFS discovery tree.
2. Account for the implicit stutter step in `always-stutter` at every state.
   A state with no state-changing transitions can still have an infinite run;
   pending work stuck there must not receive a liveness pass.
3. Use weak fairness of **nonstuttering** actions, corresponding to
   `WF_vars(A)` with `<A>_vars`. An action that produces only the same state does
   not impose a state-changing fairness obligation. Compare full states exactly.
4. An action group such as `FairWorker = or(...)` is one disjunctive fairness
   assumption. It is not independent fairness for every constituent action or
   every quantified connection. Preserve that distinction in results.
5. Compute whether fairness actions are enabled from the **full state-space
   semantics**, before restricting to a goal-false subgraph. An escape edge to a
   goal-true state still makes its action enabled. Filtering it out must not
   make an unfair stutter appear fair.
6. For each goal, find strongly connected components in the subgraph of
   reachable goal-false states. With implicit stuttering, singleton components
   can support infinite behavior too. A component supports a weakly fair
   infinite walk if, for every selected fairness group, it contains either a
   state disabling that group's nonstuttering action or an internal transition
   belonging to that group. Explain and test this criterion.
7. Preserve overlapping fairness labels when different action groups can
   describe the same transition. Deduplicating states or edges must not drop
   action membership needed to establish fairness.
8. Report actual fair counterexamples: a reachable finite prefix followed by a
   repeatable closed walk that keeps the goal false and satisfies every selected
   fairness assumption. A convenient simple cycle inside a fair SCC may itself
   be unfair; include the required disabling states or action edges in the
   emitted walk. Validate the emitted transitions and fairness witnesses.
9. Distinguish counterexamples from incomplete exploration and invalid input.
   A cap hit must produce an incomplete/unknown result, never a pass. Report
   vacuous goals that have no reachable false states. Detect or clearly surface
   inconsistent fairness assumptions/no admissible fair continuation so a
   vacuous universal result is not presented as useful progress assurance.

Initially support weak fairness only unless another temporal feature is actually
necessary. Do not silently treat weak fairness as strong fairness. Do not use
symmetry reduction for liveness until its preservation of the selected properties
and action labels is established; rejecting the combination is acceptable.

## Existing APIs and performance guidance

The local toolchain is Nim 2.3.1, with NIF libraries at
`/usr/lib64/nimony/src/lib`. The Tlanif build convention is:

```sh
nim c -d:release -o:bin/tlanif src/tlanif.nim
```

Relevant implementation surfaces:

- `loader.nim`: `loadModuleFile` and `loadModuleBuffer` return a `Module`.
- `eval.nim`: module definitions have `Cursor` bodies; `initialStates`,
  `successors`, `evalAction` and `checkInvariant` provide reference semantics.
- `compile.nim`: `compileModule`, `loadState`, `checkInv`, `runNext`,
  `encodeSuccessor` and `successorState` provide compiled evaluation.
- The compiler internally has `CExpr`, `Cont`, `Ctx`, `Scope`, `compileExpr`
  and `compileAction`. They are currently private. A narrow native API for
  compiling/evaluating additional predicates and action expressions against a
  loaded state would avoid recompiling modules or decoding that state repeatedly.
- `pexplore.nim`: `encodeState` and `decodeState` are exported. Its private
  per-variable `Interner`, `internState` and `unpackState` already reduce state
  storage to packed integer tuples. Reuse or carefully extract that machinery
  rather than inventing another parser or state representation.
- `value.nim`: states/values use NIF cursor-backed storage. Never pass `Value`
  cursors between threads. Existing parallel workers exchange encoded strings
  and own their modules independently.
- `loader.nim` keeps only the last `(check ...)`; multiple invariants must be
  combined into one expression. Do not rely on multiple checks being enforced.

Use compiled evaluation for the fast path, compact graph storage and an iterative
SCC algorithm so a long graph cannot exhaust the call stack. Evaluate goals and
enabledness while exploring; avoid rebuilding the graph for every goal. Encode
or print full states only when needed for counterexamples. Measure real elapsed
time and peak memory on Relay's models before making performance claims.

Keep a reference-evaluator path for differential validation. The existing safety
workflow requires no-`--jobs` reference exploration and `--jobs:4` compiled parallel
exploration to agree. Establish equivalent differential checks for the new
liveness mode. If the first liveness implementation uses a single compiled
worker, document that honestly and reject incompatible `--jobs` choices rather
than silently ignoring them. Do not sacrifice correctness for premature parallelism.

## Regression validation

Use small, readable examples or standalone assertions following Tlanif's project
conventions. At minimum check:

- A progress action continuously enabled: without fairness, stuttering violates
  progress; with its weak fairness, the goal passes.
- Pending work with no enabled Next action: an implicit stutter counterexample.
- A worker cycling forever while work stays pending: a real fair-cycle failure.
- An action enabled only intermittently: weak fairness must still allow its
  starvation; a strong-fairness interpretation would wrongly pass it.
- A goal-false state with an enabled fairness edge leaving the bad SCC: rejecting
  its unfair self-loop is essential.
- Overlapping action groups and duplicate transitions: labels remain correct.
- A fair closed walk requiring several disabling witnesses/action edges, whose
  individual simple cycles are unfair: emitted counterexample is truly fair.
- A no-op action: it cannot satisfy a required nonstuttering occurrence.
- Unsatisfiable fairness, unreachable/vacuous goals, multiple initial states,
  invalid selected definitions and state-cap exhaustion.
- A deep graph demonstrating iterative SCC traversal.

Check both evaluators where supported. Rerun the existing mutex and atomicArc
examples, including their intentionally failing variants, in reference and
parallel safety modes. No existing safety behavior should regress.

## Relay checks to perform

Run native liveness checks for these **required** goals with the relevant
explicit fairness assumptions already annotated in the models:

| Model | Goals | Fairness definitions |
| --- | --- | --- |
| `websocket_lifecycle.nif` | `GoalShutdown`, `GoalCompletions`, `GoalEventWait`, `GoalResultWait` | `FairWorker`, `FairDue`, `FairResult`, `FairEvent`, `FairWaitClock`, as needed per goal |
| `websocket_frames_close.nif` | `GoalClose`, `GoalSends` | `FairCancel`, `FairClose`, `FairClock`, `FairFinish`, `FairSendClock`, as needed per goal |
| `http_lifecycle.nif` | `GoalShutdown`, `GoalOperations`, `GoalResultWait` | `FairWorker`, `FairNetwork`, `FairConsumer`, `FairOwner`, as needed per goal |

Use the minimum justified assumptions for each property. Worker shutdown must
not depend on a consumer eventually draining WebSocket result/event queues.
Completion consumption can legitimately require a willing result consumer;
deadline-related progress requires advancing time. Do not add peer cooperation
to bounded close merely to obtain a pass.

`GoalWaiters` in the WebSocket lifecycle model is **diagnostic**, not a required
goal: an empty result waiter on a running client can legitimately wait forever
when no future work arrives. It is useful as an expected-failure probe. Finite
operation/connection horizons and global waiter predicates limit what these
models establish; inspect the predicates before describing per-caller progress.

HTTP owner abort is allowed to discard unfinished requests. Its `ownerAbort`
ghost provenance and stage 9 encode that contract; `GoalOperations` includes the
allowed discard. The existing `StrictCompletionInv` deliberately demands a
stronger-than-contract publication policy and fails in eight states. This is
not a supported-API defect or a reason to alter the production HTTP worker.
Graceful close and unexpected worker failure still require publication before
stopping. Keep at-most-once, accounting, resource and wakeup safety checks intact.

Current exhaustive safety counts, agreed by reference and compiled parallel
evaluators with cap 400,000, are:

| Scenario | States |
| --- | ---: |
| WebSocket lifecycle default | 91,346 |
| WebSocket frames/close | 58,180 |
| WebSocket reuse | 213,205 |
| WebSocket duplex | 166,938 |
| HTTP one handle | 5,859 |
| HTTP two handles | 7,803 |

The README describes reuse/duplex reductions precisely. Reuse uses two fresh IDs,
one retained slot and no waiter-entry actions. Duplex starts with two open
connections, permits two fresh sends across either connection, and also removes
message publication, close requests and event polling. Do not restrict each send
to a preassigned connection. Do not claim liveness coverage for disabled waiter
entry paths. An unrestricted larger WebSocket exploration previously exceeded
400,000 states and remains incomplete. Keep state-cap outcomes explicit.

Check the defaults first; then HTTP two handles and the documented reduced
WebSocket variations if tractable. If a goal fails, inspect the fair counterexample
and trace the corresponding production code. Distinguish a model bug, an
insufficient or unreasonable fairness assumption, a finite-bound limitation and
a real implementation defect. Do not weaken a property just to force a pass.
Do not change production workers for insignificant internal differences.

## Deliverables and cleanup

- Native Tlanif implementation, clear CLI help/documentation and regression examples.
- Fresh model liveness results, with exact selected goals/fairness, complete state
  and edge counts, elapsed time, and understandable fair counterexamples on failure.
- Updated Relay `models/README.md` and `models/REPORT.md` describing the native
  commands and current conclusions. Keep source/model/tool fingerprints current.
  Existing safety-only limitations should be qualified accurately once the new
  mode exists; do not leave stale claims that the tool can never check liveness.
- Source comments inside `.nif` files must follow NIF suffix-token comment syntax.
  Preserve acyclic definitions, module symbol trailing dots, unqualified bound
  locals, complete Init assignments and explicit stutter variable lists.
- All Relay modeling material belongs under `models/`. Checker implementation
  belongs in Tlanif, not a new Relay script framework.
- Remove temporary model variants, generated graph/JSON/log reports, temporary
  source copies and binaries created for this task. Preserve unrelated existing
  caches and user files. Use ordinary ignored build locations while testing.
- No push. Final response should state changes, validation, findings, performance,
  remaining limits and commit/working-tree state concisely.

The previous runtime validation passed all 14 Relay programs via
`nim test tests/ci.nims`. Its loopback WebSocket protocol test also passed release,
danger and ASan modes with linked libcurl 8.18.0. Those results do not substitute
for the new checker's regression tests or machine-checked model liveness.
