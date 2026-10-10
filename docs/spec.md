# lg language specification (skeleton)

Normative skeleton for the lg v1 language specification. `docs/design.md`
is the design contract and rationale; this document is the eventual
user-facing reference: precise, example-driven, organized for lookup.
Sections marked *(stub)* are placeholders awaiting text.

## 1. Lexical structure and reader *(stub)*

- Forms, atoms, literals (int/float/bool/char/string/keyword/symbol/nil),
  collections (list/vector/map/set), quote/syntax-quote/`~`/`~@`, meta
  `^`, comments, discard `#_`. Reader errors: `E2xx` diagnostics.
- Corresponds to design.md §1.

## 2. Modules and namespaces *(stub)*

- `(ns name (:require [mod :as alias]))`, `ocaml.*` requires,
  `ocaml.pkg/*` package linkage, exports/privacy, module-qualified
  names, `declare` forward declarations.
- Corresponds to design.md §1, §13, §17.

## 3. Special forms *(stub)*

- `ns`, `def`, `defn` (incl. multi-arity), `fn`, `let`, `if`, `do`,
  `when`, `quote`, `syntax-quote`, `loop`/`recur`, `and`/`or`, `cond`,
  `match`, `defmacro` (incl. multi-arity), `defrecord`, `defvariant`,
  `extern-type`, `declare`, `ffi`, `let` destructuring forms.
- Corresponds to design.md §1, §4, §8, §13.

## 4. Type system *(stub)*

- Hindley–Milner inference, `^T` annotations as assertions, rigid
  signature variables, the `any`/`dyn` boundary (boxing, checked
  unboxing, absorbing `seal`), stored-scheme canonicalization
  (`canon_free`), option types, `TSeq` as the universal collection
  interface, variant types, implicit parameters.
- Corresponds to design.md §2, §3, §5.

## 5. Macros and compile-time evaluation *(stub)*

- `defmacro` semantics, argument passing as raw forms, syntax-quote
  template evaluation, hygiene guarantees and the mark model, `gensym`,
  multi-arity dispatch, module resolution of macro-internal names,
  expansion order vs inference.
- Corresponds to design.md §4.

## 6. Standard library *(stub)*

- Builtin functions by domain: arithmetic, comparison, predicates,
  collection construction/inspection/transformation, seq API and
  laziness, strings, atoms, io/system, tuples, higher-order forms.
- Builtin × collection-kind dispatch matrix: which (builtin, coll-kind)
  cells are allowed and which are static errors — normative table
  generated from `test/gen_collmatrix.py` (see also `test/collmatrix`).
- Corresponds to design.md §11.

## 7. Memory model and modes *(stub)*

- Inferred modes (`local`/`shared`/`unique`), borrowing, `stack_`/`local_`
  emission on OxCaml, FBIP accumulator lowering, atom semantics.
- Corresponds to design.md §5.

## 8. Evaluation and runtime semantics *(stub)*

- Strict evaluation except lazy seqs; realization at boundaries;
  runtime contract failures (fail loudly); atom operations; printing
  (`str`/`println` representations per type).
- Corresponds to design.md §11, §12.

## 9. Interoperability *(stub)*

- `ocaml.*` requires: module resolution, labeled arguments, opaque
  handles, constructor calls, `ocaml.pkg/*` auto-linking. `ffi`
  declarations: `:native`/`:js`/`:default` selects, ctypes mapping.
- Corresponds to design.md §17, `docs/ffi.md`.

## 10. Compilation, performance, and incremental semantics *(stub)*

- Pipeline: reader → syntax → types → inference → macro expansion →
  mode inference → emit → OCaml compile/link.
- `lg check|emit|modes|build` commands; `-I` include paths; `-o` output;
  `--byte` (ocamlc bytecode, fast dev loop) vs default ocamlopt native;
  `--backend=melange|wasm`.
- Incremental compilation: `<exe-dir>/.lg-obj` holds one OCaml unit per
  lg module plus `Lg_rt`; a unit rebuilds only when its own emitted
  source or a dependency's unit hash changes (content hash —
  `Digest(source + dep hashes)` — mtime and comments do not force
  rebuilds). Stamps are per (unit, toolchain): `*.ocamlc.stamp` /
  `*.ocamlopt.stamp` so byte and native artifacts never mask each
  other's staleness.
- Performance notes: emitted module size is roughly proportional to
  source; the `Lg_rt` unit compiles once per object directory and is
  shared across modules; single-module cold builds are dominated by
  the OCaml toolchain (frontend <10ms on `test/` programs).
- Corresponds to `bin/lg.ml` build pipeline; see also design.md §6–7.

## 11. Diagnostics *(stub)*

- Error classes `E1xx`–`E3xx`, source locations, suggested fixes,
  `--strict` mode, the `should_fail` negative contract.
- Corresponds to design.md §14.

## 12. Portability and backends *(stub)*

- Native (ocamlopt/ocamlc), OxCaml (`local_`/`stack_` annotations),
  Melange/JS, wasm_of_ocaml; `.cljc` conditional reader keys
  `:native`/`:js`/`:default`.
- Corresponds to design.md §15–16.

## 13. Not part of v1 *(stub)*

- Explicit exclusions: no concurrency model, no try/catch/throw,
  no defprotocol/defmulti, no arbitrary-precision numerics — each with
  the documented reasoning.
- Corresponds to design.md §9, stability.md §10–12.
