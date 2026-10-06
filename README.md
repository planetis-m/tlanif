# tlanif
Small TLA+ implementation based on NIF.

Parses a NIF dialect of untyped TLA-style specs (Symbol/SymbolDef names,
operator tags) and checks safety invariants by BFS over finite models.

Build:
  nim c -o:bin/tlanif src/tlanif.nim

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
|  tlanif       | CLI |
