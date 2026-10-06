# AGENTS.md

`tlanif` is a small explicit-state safety and bounded liveness model checker for TLA-style specs written in a
NIF dialect (Nim's NIF s-expression format, from the Nimony project). It parses a spec,
BFSes a finite state space and checks a safety invariant, printing a shortest
counterexample when one exists. Opt-in liveness checks named progress predicates under
weak fairness. Examples and `tests/tliveness.nim` provide regression coverage; there is
no CI or nimble file, and the repo is developed as a single-shot tool.

## Build, run, verify

Build (verified; writes the binary where the README's run commands expect it):

```sh
nim c -d:release -o:bin/tlanif src/tlanif.nim
```

* `src/nim.cfg` adds `/usr/lib64/nimony/src/lib` to the search path, where `nifcore` and
  `nifcoreparse` live (nimony is installed system-wide at `/usr/lib64/nimony`, version
  0.6.3).
* Nim 2.3.1, `--mm:orc`, threads on. `-d:release` matters: the debug default (`opt: none`)
  makes the interpreters several times slower. Note the `examples/atomicarc*.nif` specs
  *model* Nim's `--mm:atomicArc`; tlanif itself is not built with it.

Run / verify safety (exit code 0 = ok, 2 = check failed, 1 = error; violations and limit hits go
to stderr with the counterexample):

```sh
./bin/tlanif examples/mutex.nif              # ok, 3 states, exit 0
./bin/tlanif examples/mutex_bug.nif          # invariant violated, exit 2
./bin/tlanif examples/atomicarc.nif          # ok, 40 states, exit 0
./bin/tlanif examples/atomicarc_bug.nif      # violation (leak), exit 2
./bin/tlanif examples/atomicarc_cursor.nif   # violation (use-after-free), exit 2
./bin/tlanif --jobs:4 examples/atomicarc.nif # parallel BFS; must agree with the above
```

After building the CLI, run native regression assertions from the repo root:

```sh
nim c -d:release -o:bin/tliveness -r tests/tliveness.nim
```

The suite compares compiled/reference liveness, checks 120 generated models against
an independent closed-walk oracle, validates witnesses, exercises deep and bounded
stress graphs, and compares all passing/failing safety examples with four workers.
`tests/config.nims` supplies the source and NIF library paths. Debug and danger builds
are also supported; use separate `--nimcache` directories for concurrent builds.

CLI (the value-taking options are prefix-matched `--flag:value`; `--sym` and `-h`/`--help` match
exactly; unknown options exit 1):

* `--max-states:N` (default 100000) — safety-only exhaustion remains exit 2;
  liveness exhaustion is incomplete/unknown, exit 4, with no pass conclusion.
* `--jobs:N` (0 = all cores) — selects `pexplore` (compiled, parallel). **Omitting the flag
  is the sequential reference explorer; `--jobs:0` is auto-parallel, not sequential.**
* `--sym` — symmetry reduction over the model groups declared by `(models ...)`.
* `--memo-limit:N` — per-module def-memo entry cap (0 = unbounded, default cap 1e6; the
  table is flushed when full, not evicted per entry).
* `--live:GoalA,GoalB` — explicitly select `[]<>Goal` state predicates; safety is still checked.
* `--fair:ActionA,ActionB` — selected weak-fairness groups, requiring `--live`.
* `--live-eval:compiled|reference` — maintainer differential route; default compiled.
  Liveness is single-worker and rejects both `--jobs` and `--sym`. Exit codes:
  0 bounded pass, 1 invalid/error, 2 safety failure, 3 liveness failure,
  4 incomplete, 5 no admissible fair behavior. Empty Init also produces 5.
* `-h`/`--help` — prints the usage block and exits 0.

Debugging defines:

* `-d:countApply` — per-call `applyFun` counters and extra diagnostics to stderr.
* `-d:skipInv` — parallel mode skips invariant checks entirely (everything reports ok).

## Layout and control flow

| Module | Owns |
|---|---|
| `src/tlanif_model.nim` | `TlaTag` enum (the whole dialect's tag ids), tag/entity access helpers, `loadTlaFile`/`loadTlaBuffer`; re-exports `nifcore`/`nifcoreparse` |
| `src/value.nim` | finite values (`null`/bool/int/model/set/seq/fun/record) over NIF token buffers, `Values` factory, `encodeValue`/`decodeValue`, `State` + hashing/ordering |
| `src/eval.nim` | `Module`/`Frame`/`DefInfo`, `EvalError`, expression interpreter, action interpreter, def memoization, `initialStates`/`successors`/`checkInvariant` |
| `src/loader.nim` | top-level form loading: `constants`, `variables`, `models`, `assign`, `def`, `spec`, `check` (`extends` is parsed then skipped) |
| `src/explore.nim` | sequential BFS, symmetry canonicalization, counterexample formatting |
| `src/pexplore.nim` | parallel level-synchronous safety BFS: worker pool and byte-string state handoff |
| `src/statecodec.nim` | shared state encoding/decoding and exact per-variable interning |
| `src/compile.nim` | def-to-closure compiler for `check`, `Next`, selected goals and fairness actions |
| `src/liveness.nim` | full reachable graph, iterative SCC analysis, fair closed walks and reference witness validation |
| `src/tlanif.nim` | CLI, exit codes, stderr diagnostics |

Load path: `loadTlaFile` (`parseFromFile` with a fresh `TlaTag` pool) → `loadModule` builds one
`Module` holding the token buffer, a `defs` table (cursor into the buffer), the grounded
`env` (constants + model values), `constSet`, and the `spec`/`check` cursors. Requirement:
at least one variable, a `(spec ...)` and a `(check ...)`, else `EvalError`.

Two evaluators over the same dialect:

* `eval.nim` is the reference semantics. The **sequential** explorer runs everything
  (Init, Next, check) through it, using `Frame` tables plus a def-value memo.
* `compile.nim` compiles `check` and `Next` into closure trees once at load time (defs
  inlined at their call sites, flat `slots` vector, CPS actions, per-site cross-state def
  caches). The **parallel** explorer uses it in workers. `Init` is still interpreted via
  `evalAction`, and `getDefInfo`/`collectFree` come from `eval.nim`.
  Liveness uses the same compiler with additional goals/actions; its reference mode
  interprets all evaluations, while compiling once to reject unsupported selections.
* The two must stay in sync: they currently handle exactly the same tag set, and
  `--jobs` vs no flag is the standing differential test (same explored-state counts and
  identical counterexamples). When adding a tag, update `TlaTag`, both evaluators, and be
  aware that `collectFree`'s generic `else` branch walks children and over-approximates
  frees for unknown tags (sound, but no memo hits; see below).

BFS: `explore` enqueues `initialStates`, checks the invariant per state, expands
`successors`; `visited: Table[State, int]` plus a parent chain reconstruct the shortest
counterexample. In parallel, the main thread only sees byte-encoded states: per-variable
values are interned into packed 4-byte index tuples (`statecodec.Interner`) and the frontier
is streamed to workers in windows of `jobs * 8192` states.

Liveness uses CSR edges, packed state keys, and 64-bit goal/fairness masks (maximum 64
selections each). Retain overlapping memberships on deduplicated edges. Enabledness
is determined in the full action semantics before restricting to goal-false states.
Every state has an implicit stutter edge; no-op actions are not enabled nonstuttering
actions. A fair SCC provides a disabling state or internal action edge for each group.
Construct a walk covering those witnesses, rather than returning any simple cycle.
Only its BFS prefix is shortest. Report no-fair-continuation states and vacuous goals;
never advertise progress assurance when no admissible fair behavior exists.

## Spec language (things the examples don't make obvious)

Entity names must be `Symbol`/`SymbolDef`; `Ident` is rejected by assertion. Module-level
names (`variables`, `constants`, models, defs) are written with a trailing dot
(`:lock.0.`, `Init.0.`) that expands to the file's module name — the file stem, which is why
counterexamples print `lock.0.atomicarc_bug`. Binder-bound locals are written `:x.0` at the
binder and `x.0` at uses, *without* the trailing dot; adding one turns the use into a
module-qualified symbol and fails later with `unbound symbol: x.0.<module>`.

Comments are `#...#` **suffix decorations on a token**, not free-standing syntax: the opening
`#` must directly follow a token (a tag name, symbol, string/char, or `.`; `)` cannot carry a
suffix) and the closing `#` ends it. Multi-line header comments work when opened right after
`(stmts`. A `#` at the start of a line is read as code, which swallows/mangles the following
text; the usual symptom is `beginRead with unclosed tags`. `examples/yrc.nif` uses that
style (and `obj.0.` module-qualified uses where the binder is `:obj.0`) and currently does
not load at all; treat it as the large unfinished spec for perf work, not as a passing
example.

Form shapes:

```
(stmts
  (constants :Threads.0. :MaxRc.0.)      # names only
  (variables :pc.0. :rc.0.)              # names only
  (models Threads.0. :t1.0. :t2.0.)      # sort name first, then interchangeable elements
  (assign MaxRc.0. 2)                    # constant := expression
  (def :Init.0. body)                    # body is an action or expression
  (spec (always-stutter Init.0. Next.0. (tuple pc.0. rc.0.)))
  (check Inv.0.))                        # a def name or an inline expression
```

Values are written `(false)`, `(true)`, `(null)` (empty tags), `(bool)` = `{false,true}`,
int literals, `(set ...)`, `(seq ...)`, `(fun (mapsto k v) ...)`,
`(record (kv :field v) ...)`. Sets are canonicalized to sorted-unique, and `choose` picks the
first witness in that order, so set canonicalization is observable. Sequences are partial
functions over `1..len`; `apply` on a sequence is 1-based indexing. `except` rewrites a
function and `@` inside an update's RHS is the pre-update value.

Tag inventory (from `TlaTag`): structure `stmts extends constants variables models assign def
spec check always-stutter tuple`; `and or not implies eq neq if let bind`; sets `in notin
subset union intersect setminus card set setcomp range emptyset choose`; quantifiers
`exists forall` (also `setcomp`, `funof`, `choose` — each takes a `:x.0` binder, then the
domain, then the body); funs/records/seqs `fun funof mapsto domain apply except at record kv
field seq emptyseq append concat len`; actions `prime unchanged`; atoms `true false null
bool`; arithmetic/comparison `gt ge lt le plus minus` (ints only). `case` is declared in the
enum but implemented nowhere; it raises `cannot evaluate tag as expression: TCase`.

Actions: `Init` must prime every variable (`Init did not assign <var>` otherwise). In `Next`,
any variable a branch leaves unprimed **stutters implicitly**; the `(tuple ...)` list is
parsed into `stutterVars`. Safety exploration ignores that list; liveness requires a
complete, duplicate-free tuple listing every variable.

Defs are inlined/expanded, so the def graph must be acyclic: a cycle reachable from
`Next`/`check` is invalid. Compilation and `containsPrime` detect cycles on their
traversal paths; other reference expansion can still hit the call-depth limit. Only
`or` whose subtree is prime-free is evaluated as a short-circuiting boolean
guard; other disjunctions in actions enumerate branches.

## Correctness-relevant internals

* Memoization is keyed on a def's *free* symbols excluding module constants
  (`constSet`), so `DefInfo.frees`/`collectFree` must remain an over-approximation; an
  under-approximation would produce unsound hits. `@`/`prime`/`unchanged` set
  `memoizable = false`. `memoLimit` bounds entries and flushes the table (`0` = unbounded).
* `Value` is a `Cursor` into a refcounted token buffer, not a heap ADT. Never let a `Value`
  (or a `State` containing them) cross a thread boundary — `pexplore` workers pass
  `encodeValue` byte strings only, because cursor refcounts are not atomic. `ValueTree` is
  move-only (`=copy` is `{.error.}`).
* All `Values` must share the module's literals `Pool` (`initValues(m.pool)`) or `SymId`s
  will not compare equal.
* Symmetry reduction (`--sym`) builds the product of per-sort permutations, which is
  factorial in the model-group sizes (6+6 objects already means over a million tables);
  `explore`/`pexplore` only enable it when the product has more than one element and print
  the count to stderr.
* `initialStates`/`successors` live in `eval.nim` and are shared by both explorers; the
  parallel safety path compiles only the invariant and Next. Liveness also compiles
  selected predicates/actions and always reference-validates emitted fair witnesses.

## Conventions and housekeeping

* Nim style: 2-space indent, `camelCase`, exported `*` names, `T`-prefixed enum members,
  box-drawing section separators (`# ── Actions ─────`) in the large modules. Errors are
  raised via `raiseEval` as `EvalError`; stderr goes through `syncio`, not `echo`.
* Build artifacts: `nimcache/`, `bin/`, and in-place `src/tlanif*` binaries are gitignored;
  prefer `-o:bin/tlanif` as the README documents.
