# Changelog

## v0.1.0

First tagged release of lg — a statically-typed Clojure-flavored Lisp
compiling to OCaml via `Clj_core` data structures.

### Language

- Hindley–Milner inference with `^T` annotations as assertions and the
  absorbing `any`/`dyn` boundary (explicit `^any` entry, checked unboxes,
  `--strict` requiring annotations on heterogeneous literals).
- `defn`/`defmacro` multi-arity bodies with arity dispatch.
- Destructuring (`[a [b c]]` sequential, map `:keys`/`:strs`/`:as`/`:or`)
  in `let`/`fn`/`defn`, nested and `any`-valued.
- `match` on literal/quoted/vector/map/`Some`/`None` patterns over typed
  and `any` scrutinees; `case`, `cond`, `->`, `->>`, `loop`/`recur`,
  `& rest` varargs, named-`fn` self-recursion.
- `defvariant` (real OCaml polymorphic variants), `defrecord`, `declare`.
- Hygienic `defmacro` with syntax-quote and `gensym`.
- Implicit parameters (`^:implicit` trailing params resolved by type at
  call sites).
- Lazy sequences across the stdlib seq API.
- `.lgi` interface files (export control, `:escapes` modes, interface-only
  checking), `.cljc` conditional reads (`:native`/`:js`/`:default`).

### Compiler and tooling

- `lg check|emit|modes|build|lgi|fmt|repl|doc|init|lsp` commands;
  `--backend=ocaml|oxcaml|melange|wasm`; `--strict`; `--byte` bytecode
  builds (~3–5x faster dev loop; native remains the release default).
- Incremental compilation: per-module units under `<exe-dir>/.lg-obj`
  invalidated by source+dep content hashes with per-toolchain stamps.
- OCaml interop: `ocaml.*` requires read `.cmi` signatures directly —
  labeled/optional args, constructors, opaque handles for abstract
  types, `ocaml.pkg/*` findlib package linking.
- `ffi` declarations with `:native`/`:js`/`:default` selects.
- Diagnostics E1xx–E3xx with source locations.

### Codegen and performance

- Emit targets `Clj_core` Vec/Map/Set/List/Seq/Atom; emitted OCaml is
  type-correct by construction (no casts).
- Mode inference drives OxCaml `stack_`/`@ local`/`local_` lowering in
  three tiers (~31% fewer minor-heap words, ~83% fewer minor collections
  on the literal-heavy path).
- FBIP accumulator lowering: single-use collection-update chains and
  self-recursive accumulators emit growable builders + one freeze
  (~2.2x on a 5M `conj` loop).

### Test harness

- `test.sh` lanes: golden `.out` diffs, negative error-class checks
  (`should_fail/`), byte/native parity, emit snapshots, reader
  round-trip, compat corpus, generated builtin×collection-kind matrix,
  compile-speed bench assertions. `test/emit_matrix.py` runs the
  builtin-emission matrix.
