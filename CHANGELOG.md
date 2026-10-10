# Changelog

## Unreleased

- **Constructor-pattern catch**: `(catch (Ctor a…) h…)` emits a
  real OCaml `with` pattern alongside `(catch e h…)` —
  `(catch (Not_found) h)` catches `ocaml.*` exceptions by
  constructor, `Failure`/`Invalid_argument`/`Sys_error` payload
  args bind `string`, other ctors' args bind `any`, `_`
  wildcards allowed, and a non-matching exception re-raises
  automatically (true `with` semantics — no catch-all wrapper).
- **Global content-addressed build cache** (`~/.lg/cache`). Unit
  objects and linked binaries are keyed by
  `hash(emitted source + dep hashes + toolchain + compiler mode)`
  and shared across projects — a cold `lg build` with a warm
  cache is file copies only. Measured on an M-series: native
  cold-hit ~85ms (was ~300ms), warm no-op ~30-90ms, `--byte`
  hello ~50ms cold-hit; `lg repl` per-line latency ~50ms
  (was ~1s). Stores are atomic (tmp dir + rename) and the
  `.lg-obj` stamp still validates restored artifacts, so the
  cache can never serve stale objects. The bench lane now
  measures true-cold (cache wiped), cache-hit cold, dep-chain,
  and warm builds against tightened limits.
- **Builtin namespaces** (`lg.str`, `lg.io`, `lg.set`). String,
  io, and set helpers moved out of the bare namespace following
  Clojure conventions: `str/join str/split str/subs str/trim
  str/re-find str/re-replace …`, `io/slurp io/spit io/argv io/env
  io/sh io/now-ms`, `set/union set/intersection set/difference
  set/subset? set/superset? set/select`. Reached via
  `(:require [lg.str :as str] …)` — builtin, no `-I` needed; the
  fully-qualified `lg.str/join` resolves without a require. The
  old bare names are gone: `(join …)` is E102 with a
  did-you-mean hint (`str/join`). New set builtins shipped with
  the namespace: `intersection`, `difference`, `subset?`,
  `superset?`, `select`. `test/nscore.lg` exercises all three
  namespaces end-to-end; `should_fail/bare_ns.lg` pins the E102.
- `nil` is removed from the language.
  `()` is now *the* unit literal — it prints `()`, binds `unit?`,
  and is a static E101 in `if`/`when`/`and`/`or` condition
  position (unit is not a truthiness operand). `None`/`option`
  covers absent values; an empty list is `(list)`/`[]`, never `()`.
  The reader rejects `nil` with E201 plus the replacement hint; the
  `nil?` builtin is renamed `unit?` (it no longer answers `true`
  for `None` — that is `none?`). All corpus uses are rewritten;
  printed representations moved from `nil` to `()`/`None`.
- `lg lgi --check [--all]`: drift gate — an existing `.lgi` must
  agree with its `.lg` exports: a listed def whose signature changed,
  or an entry for a def that no longer exists, is reported and exits 1.
  Unlisted defs are private-by-omission, not drift. Two test.sh lanes
  pin the gate (clean pass + drifted copy caught).
- REPL latency: each line now reuses ONE stable session file plus
  `--byte` (ocamlc) builds — a fresh temp name per line used to defeat
  `.lg-obj` caching entirely. ~85ms per simple line (was ~1s native).
- `qcfuzz`: self-bootstrapped fuzz lane — `test/qcfuzz.lg` uses qc's
  split-seed rng to write 40 random s-expr sources (round-tripped
  through reader/printer via `roundtrip.exe`) plus 12 generated
  well-formed mini programs that must build and run (emit smoke).
- Reader: `\<delim>` char literals (`\(`, `\]`, `\;`, `\<ws>`) now
  parse — a delimiter right after `\` IS the character; only a bare
  `\` at EOF is an empty-literal error. Fuzz-found.
- `(declare ^T f)` forward types now actually constrain self-recursive
  calls: the defn's self-binding uses the declared type instead of a
  fresh var, so recursion under an option-join can't occurs-fail
  before the annotation applies.
- `try`/`catch`/`finally` + `throw`: `(try body… (catch e h…)
  (finally f…))` compiles to a real OCaml `try…with` wrapped in
  `Fun.protect`; `e` binds an opaque `exn` handle with `exn-message`
  (`Printexc.to_string`), `(exn s)` (`Stdlib.Failure s`), and
  `throw` for re-raise. Exceptions raised through `ocaml.*`
  interop (`Not_found`, …) are caught exactly like native ones —
  verified against `ocaml.List`'s `List.find`. The try value joins
  body and handler per the §4 option rules; finally's value is
  discarded. exn-constructor pattern catches are deferred to v0.2.
- Soundness fix in `join_branches`: a unit-typed branch collapsing
  into an option's `None` now still evaluates its side effects
  (`EDo [branch; None]`) — `(if c x (println y))` previously
  dropped the print entirely, and the same hole applied to the new
  `try` catch handler.
- `ocaml.*` interop now compiles and runs under OxCaml: the
  compiler-libs ABI differences (`cmi_sign` staticity pair, arrow
  labels, variant/ctor payload shapes, archive split) are normalized
  in `src/osig_shim*.ml` selected by `%{ocaml_version}`, and
  transparent manifest aliases in cmis (`Stdlib__String.t = string`)
  expand with their `type_params` instantiated — `ocamlinterop` and
  `eiodemo` build+run identically on both toolchains.
- `ocaml.*` honest foreign types: curried arrow chains flatten into
  multi-param functions so lg multi-arg fns feed OCaml HOFs
  (`Hashtbl.fold`); `result`/`array`/`ref`/`bytes` import as opaque
  handles instead of lying as option/list/atom/string; builtin-name
  matching is exact-path (no `M.list` collision); imported handle
  params keep their type variables so OCaml weak-var inference pins
  them per use (`(def h (ht/create 8))` then concrete ops).
- `ocaml.*` deep-cmi semantics extended: optional `?x` params unwrap
  to `~x` semantics on both toolchains (cmi `T option` stripped in
  `decompose`); relative dotted type paths resolve parent-scope-first;
  manifest-alias expansion binds names against the manifest's own
  unit; abstract types keep canonical-unit names; row types/objects/
  univars/packages inside constructor args import as fresh type vars;
  `exn` maps to the opaque `Stdlib.exn` handle. New dogfood lane:
  `examples/eioecho.lg` — a self-terminating TCP echo over
  `Net.listen`/`accept_fork`/`Fiber.fork`/`Flow.single_read`
  (verified on both switches; run lane in test.sh).
- `lg fmt` escapes char literals (`\newline`, `\space`, …) instead of
  emitting raw control bytes; whole-corpus fmt fidelity lanes assert
  form-level equivalence, idempotence, and comment preservation.
- `test.sh` refreshes `bin/lg.exe` before running — a `_build` binary
  left by another opam switch reads the wrong cmi family.

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

## Linear let-chain FBIP (2026-10-10)

- `(let [v2 (conj v1 x) v3 (assoc v2 k y)] …)` where each intermediate
  binder's only use is the next update step now emits ONE mutable
  builder + one freeze — intermediate binders get no OCaml binding at
  all. Roots may be literals or once-used concrete collection locals
  (the builder copies the root once, so persistent semantics hold).
  Escaping collections still take the persistent path. Oxcaml unchanged.

## lg doc HTML site (2026-10-10)

- `lg doc` now emits an odoc-style static site: `docs/api/index.html`
  + one page per module — inferred signatures, defvariant constructors
  with field types, docstrings, `ns/name` cross-links, sidebar module
  tree, pure CSS. `.lgi` files gate which entries render.
- Docstrings captured on `defn`, `def`, and `defvariant` (the
  `"doc"` form after the name was previously parsed and dropped).
- `--format=md` keeps the previous stdout markdown; `--format=html`
  is the default. `lg doc` accepts multiple entry files and merges
  their require closures. `--tutorials <dir>` renders `<dir>/*.md`
  files as tutorial pages (a sidebar section above the module tree
  plus index links, ordered by filename) with a small dependency-free
  markdown renderer.
- `.lgi` entries carry docstrings: `(def n sig "doc")` on any entry,
  `(macro n sig "doc")` documents a `defmacro` (doc-only, never a
  value export; `lg lgi --check` ignores macro entries and
  alpha-normalizes tyvars when comparing signatures). Rendered
  signatures alpha-normalize tyvars ('a713 -> 'a).
- Boxing a user `defvariant` value into `any`/dyn now emits a real
  `Lg_rt.DVariant (name, fields)` via a per-ctor match — previously
  any non-builtin TCon silently fell back to `DStr` and produced
  ill-typed OCaml (compilable-by-construction violation).

## LSP completion + diagnostics (2026-10-10)

- `lg lsp` now pushes `textDocument/publishDiagnostics` on
  didOpen/didChange: the file is inferred and E1xx/E201 errors publish
  with code + range; clean files clear the list.
- `textDocument/completion` serves builtins, the module's own
  topdefs/variant ctors/extern-types/ffi names, and require-alias
  members (`alias/name`, .lgi-gated). A file with errors degrades to
  builtin-only items instead of null.
