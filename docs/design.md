# lg design contract

This document is the authoritative design contract for the lg language
(v2) and its emit-OCaml compiler. Read it before changing the language,
reader, type system, macro system, mode inference, or the emitter.

Language name: **lg**. Repository name: `lg2`. Source files use the `.lg`
extension; the toolchain binary is `lg`; the emitted runtime prelude
module is `Lg_rt`.

## 1. Syntax and reader

The reader produces Clojure-style forms; code is data and the AST is
built from the same literals the language manipulates.

Supported forms:

- **Scalars**: integers, floats, strings, booleans (`true`/`false`),
  `nil`, characters.
- **Symbols**: `name`, `ns/name`, `alias/fn`.
- **Keywords**: `:name`, `:ns/name` — self-evaluating.
- **Lists** `( … )`: calls and special forms.
- **Vectors** `[ … ]`: vector literals and binding vectors.
- **Maps** `{ … }`: map literals.
- **Sets** `#{ … }`: set literals.
- **Metadata** `^T` / `^{ … }`: attaches type annotations or option maps
  to the following form (`^int x`, `^{:sig (fn [int -> int])} f`).
- **Quote** `'form`.
- **Syntax-quote** `` `form `` with `~` (unquote) and `~@`
  (unquote-splicing) — read as data and evaluated by the macro expander.
- **Comments**: `;` to end of line.

Special forms (v2): `def`, `defn`, `defmacro`, `fn`, `let`, `if`, `do`,
`quote`, `syntax-quote`, `ns`, `(:require …)`, `declare`, `defvariant`,
`defrecord`, `match`, `case`, `extern-type`, `ffi`, and atom ops
(`atom`, `deref`/`@`, `reset!`, `swap!`). There is deliberately no
`loop`/`recur` (named `fn` self-recursion + native TCO covers it), no
`set!` (atoms are the only mutable cell), and no `throw`/`try` (§9).

## 2. Implicit modules

- **File = module.** Every `.lg` file is a module; the module name is
  derived from its path relative to the include roots (`util.lg` →
  module `Util`, `hello.lg` → module `Hello` in the emitted OCaml).
- **`(ns name …)` is optional.** A file without an `ns` form takes its
  module name from the path; when present, `ns` may carry `:require`
  clauses, but a bare top-level `(:require [ns :as alias])` form is also
  accepted.
- **Requires** are declared as `(:require [ns :as alias])` (also without
  `:as` for direct references). The compiler resolves them transitively:
  each required `.lg` file is read, expanded, inferred, and emitted to
  its own OCaml module inside the same output file. `-I dir` adds include
  roots.
- **All top-level definitions are public** in v0; a private API surface
  arrives with the `.lgi` sidecar in v1 (§8).
- Emitted reference: `alias/f` in lg becomes a cross-module call
  (`Alias.f`) in OCaml.

## 3. Types: Hindley–Milner + annotations

- Full HM inference over the program: `defn`/`fn` parameters, `let`
  bindings, literals, returns. No annotation is ever required for
  compilation.
- **`^T` annotations** are optional assertions, not requirements:
  `(defn f ^int [x] …)`, `(let [^string s …] …)`. An annotation that
  contradicts inference is a compile error; one that specializes an
  otherwise-polymorphic definition is honored.
- **Rigid variables.** Type variables appearing in a declared signature
  (`^{:sig (fn ['a -> 'a])}`) are rigid static types: they must not be
  materialized as dynamic values for equality, callbacks, zero-argument
  functions, options, collections, or host calls.
- **Heterogeneous literals → `TAny`.** A literal collection mixing
  element types (`[1 "two" :three]`) cannot get a single element type.
  Instead of failing or erasing to `Obj.magic`, it is typed `TAny` and
  boxed into **`Lg_rt.dyn` — a closed variant** (`DInt | DFloat | DStr |
  DBool | DKw | DSym | DVec of dyn vec | …`). Unboxing (`EUnbox`) is
  emitted only where the static type is known, as a checked projection —
  never a blind cast.
- **`Obj.magic` is forbidden** — in compiler, runtime, and emitted code,
  including aliases, wrappers, or generated helpers. Heterogeneity is
  always modeled with closed, statically-typed variants.

## 4. Macros: hygienic `defmacro`

- `defmacro` defines a compile-time function over forms, evaluated by a
  form-level evaluator inside the compiler.
- `syntax-quote` produces forms with `~`/`~@` substitution, exactly as in
  Clojure.
- **Hygiene is automatic.** Macro-introduced `let`/`fn` bindings cannot
  capture user variables. Implementation: a **mark table** tracks which
  symbols each expansion introduced; introduced identifiers are renamed
  with a unique **`__hN` suffix** per expansion site before typechecking
  and emission. `gensym` is exposed for cases that need a fresh name in
  macro output (e.g., avoiding free-variable capture).
- **Reference boundary.** Each mark also records the macro's *defining
  module*. An unqualified symbol inside a `syntax-quote` template —
  whether it names a global function or another macro — resolves in the
  macro's own module first, and only falls back to the caller's module.
  Call-site names can therefore never hijack a macro's internal
  references: `(h/w x)` always calls `hlib`'s `wrap` even when the
  caller defines its own `wrap` or its own `w` macro. Conversely, a
  bare (unmarked, user-written) name only ever resolves in the module
  that wrote it — macro calls are module-scoped, there is no shared
  "last macro wins" fallback. To emit a call to a macro from generated
  code, write it under `syntax-quote` so it carries the origin mark.
- Macros are expanded before inference; expansion is per-module and
  happens after reading, on raw forms. Expansion threads the expanding
  macro's module through a dynamically-bound value (like Clojure's
  `*ns*`), so nested macro calls keep their own boundary.

## 5. Memory model and mode inference (v0)

Three modes, inferred — never annotated:

| Mode | Meaning | v0 backend | Planned OxCaml backend |
|------|---------|------------|------------------------|
| `Local` | value does not escape its region | comment + report | `@local`, stack allocation |
| `Owned` | uniquely referenced, deterministic lifetime | comment + report | `unique`, FBIP/Perceus reuse |
| `Shared` | everything else | ordinary GC heap | ordinary GC heap |

v0 rules (escape analysis after inference, over the typed AST):

- A binding is **`Shared`** if it: is returned from a public `defn`;
  stored into an `atom` or a collection that escapes; captured by a
  closure that escapes; or passed across a module boundary into an
  escaping position.
- A binding is **`Local`** if it is consumed entirely inside its lexical
  scope (never returned, captured, stored, or escaping via an aggregate).
- A binding is **`Owned`** when it is not `Local` but has a single
  threaded reference — the classic candidate for in-place update / early
  reuse.
- Inference is intra-file in v0; cross-module calls conservatively assume
  arguments and results may escape.

Reporting: `lg modes <file.lg>` (a.k.a. the mode report / `--mode-report`
path in the driver) prints every binding with its inferred mode and the
reason it was assigned. On the vanilla OCaml backend the same
information lands in the emitted `.ml` as comments (e.g.
`(* mode: local *)`), so the inference is auditable without an OxCaml
toolchain.

## 6. Emission contract

`lg emit` writes one self-contained `.ml` file:

1. Header `(* generated by lg — do not edit *)`.
2. An embedded **`Lg_rt` prelude module** — printers and small helpers
   (`str`, `print`, `println`, `pr-str`, `str/escaped`, `dyn` +
   box/unbox, `gensym` counter). Collections are **not** reimplemented
   here; they come from `Clj_core`.
3. One OCaml `module X = struct … end` per lg module, in dependency
   order, with `let` bindings in file order.

Name mapping:

- lg locals and parameters are renamed with a fresh **`__N` suffix**
  (`n__1`, `x__7`) so Clojure-legal identifiers never collide with OCaml
  keywords or each other after macro expansion; macro-introduced bindings
  carry `__hN` (§4).
- `alias/f` → `Alias.f`; `/` inside a symbol maps to the module path.

`lg build` compiles the emitted file with
`ocamlfind ocamlopt -package clj-core,rrbvec -linkpkg` (native; falls
back to `ocamlc` for byte). `lg check` runs the front half only
(read → expand → infer → modes) for fast error reporting.

**Incremental compile.** Native `lg build` emits one bare OCaml unit per
lg module — `Lg_rt` once, then each module as `<ocaml_name>.ml` — under
`<exe-dir>/.lg-obj`. A unit's stamp is `hash(emitted source + dependency
unit hashes)`, so a module rebuilds only when its own emitted code or a
transitive dependency changed (comment-only edits are free), and the
runtime unit is compiled once per project. Cross-module references
(`Test.f`) resolve to the dependency's `.cmi`; link order follows the
topological module order. Units are ascription-annotated where a bare
compilation unit would reject the weak type variables a module struct
tolerates (`(atom (Map.of_list []))`). The melange backend still emits a
single merged file into the `melange.emit` workspace.

## 7. Emit → `Clj_core.*` mapping

| lg form | emitted OCaml |
|---|---|
| `[a b c]` | `Clj_core.Vec.of_list [a; b; c]` |
| `(vector …)` / `conj` | `Clj_core.Vec.of_list` / `Clj_core.Vec.conj` |
| `{:k v}` | `Clj_core.Map.of_list [(Keyword.kw ":k", v); …]` |
| `#{…}` | `Clj_core.Set.of_list […]` |
| `(list …)` / `'( … )` | `Clj_core.List.of_list […]` / quoted list literal |
| `:name` | `Clj_core.Keyword.keyword "name"` (`"ns" "name"` when namespaced) |
| `sym` quoted | `Clj_core.Symbol.symbol "name"` |
| `map`/`filter`/`reduce`/`into` etc. | `Clj_core.Vec.map` / `Map`/`Set`/`Seq` counterparts — same names and argument order as `clojure.core` |
| `atom`/`deref`/`reset!`/`swap!` | `Clj_core.Atom.*` |
| `str`/`print`/`println`/`pr-str` | `Lg_rt.str` / `Lg_rt.print` / `Lg_rt.println` / `Lg_rt.pr_str` |
| string lib: `subs` `split` `join` `trim` `triml` `trimr` `upper-case` `lower-case` `blank?` `includes?` `starts-with?` `ends-with?` `replace` | `String.*` / `Lg_rt` literal-string helpers — portable on every backend |
| io/system: `slurp` `spit` `read-line` `argv` `env` `file-exists?` `sh` `now-ms` | native: inline channels/`Sys`/`Unix`; melange: `Lg_node` lazy Node probes; wasm: `env`/`file-exists?` work, `now-ms`/`argv` degraded |
| regex-lite: `re-find` `re-matches` `re-seq` `re-split` `re-replace` | `Str.*` on native, `Js.Re`/`Js.String` on melange; `re-*` take the pattern first, subject second |
| wasm (`--backend=wasm`) | `ocamlc` bytecode → `wasm_of_ocaml compile` → `<exe>.js` + `<exe>.assets/` |
| heterogeneous literal | `Lg_rt.dyn` boxed value + checked `EUnbox` projections |
| `alias/f a b` | `Alias.f a b` (cross-module call) |
| `if`/`let`/`fn`/`do` | OCaml `if`/`let`/`fun`/sequencing, locals `__N`-renamed |

Rules: the emitter must produce `Clj_core.*` calls for all Clojure data
structures — never hand-rolled collections, never vendored copies, never
`Obj.magic`. `Lg_rt` holds only what `Clj_core` does not provide.

## 8. Done in v1

- **Multi-arity `defn`** — `(defn f ([x] …) ([x y] …))` dispatched on
  arity; arities emit as a `let rec .. and ..` group so they can call
  each other.
- **Destructuring** — sequential `[a [b c]]` and map
  `{:keys [..] :strs [..] :as s :or {..}}` / `{sym :kw}` / `{sym "s"}`
  binding forms in `let`/`fn`/`defn`; nested and `any`-valued patterns
  unbox recursively.
- **`match` special form** — literal/quoted/vector/map/`Some`/`None`
  patterns on typed and `any` scrutinees; clauses with `any` results
  widen the match result to `any` and concrete branches deep-box.

## 9. Design decisions (v1+)

- **No `defprotocol`, no `defmulti`.** Static polymorphism goes through
  OCaml modules/functors (free, fully checked); open dispatch on `any`
  goes through `match` dyn-tag arms. A dedicated dyn-dispatch sugar can
  be added later without taking on Clojure protocol semantics.
- **Modular implicits — as a compiler feature, not an OCaml dependency.**
  OCaml mainline (and OxCaml) has no modular implicits. lg can implement
  implicit *parameters* itself: declare implicit args, resolve them at
  call sites by type from the lexical scope, and elaborate to ordinary
  OCaml argument passing (Haskell/Scala-style dictionary passing). That
  is the intended v2 route for protocol-like abstraction.
- **No `try`/`catch`/`throw`.** Error channels are typed: `option` for
  maybe-absent values (`Some`/`None`, `if-let`, `when-let`, `match`) —
  and `Result`-style data when a reason must travel. OCaml exceptions
  still surface for runtime-checked contract failures (`^T` unboxes,
  missing-key `update` (the 4-arg `(update m k f default)` inserts
  `default` instead of failing), `contains?` on a non-coll): those
  are bugs, not control flow, and they stay uncatchable from lg.
- **Keep `dyn` confined.** `any` only enters via explicit `^any` and
  mixed-type literals; it never propagates through unification, and
  every use at the boundary is a checked unbox. A future `--strict`
  mode can require annotations even on hetero literals.

## 10. v2 shipped

All of docs/v2.md landed (detail lives there):

- **`.lgi` interface files** — mli-style sidecars: mode signatures
  (`:escapes`), export control (listed = public, `(private n)` = explicitly
  hidden), `defvariant`/`extern-type`/`ffi`/`implicit` declarations, and
  interface-only module consumption for check/modes. Variant ctors listed
  in a `.lgi` are callable and `match`-able from consumers (qualified
  `ns/ctor` patterns resolve against the ctor's emitting module).
  `lg lgi` merges with the existing file — hand-written entries win,
  `(private n)` entries survive regeneration; `--all` covers the whole
  require closure. Macros cannot be expressed in `.lgi` (they need the
  module's source at expansion time).
- **Implicit parameters** — `^:implicit`/`^{:implicit T}` trailing
  params resolved by type at call sites and elaborated to ordinary
  OCaml arguments; `(:require [ns :implicits true])` merges a module's
  implicit defs; `.lgi` `(implicit …)` entries carry them across files.
- **FBIP builder lowering** — provably single-use collection literals
  (unique-owner chains of conj/assoc/dissoc/pop/update/into/disj) emit
  `Lg_rt` growable builders + one freeze instead of persistent copies.
- **OxCaml emit** — `--backend=oxcaml` is verified end-to-end against a
  real OxCaml (flambda2) switch (test/oxcaml_smoke.sh, 28/28 programs
  compile and run). The conservative lowering: `local_` annotates
  primitive-typed params of top-level defns whose uses stay in
  local-accepting positions (arithmetic builtins, self-recursion, `if`
  conditions) — functions referenced as values are never annotated
  because higher-order callees expect global-param callbacks. `stack_` /
  `unique_` / binding `local_` stay comments: `stack_` only wraps direct
  allocation sites (never a `Vec.of_list` call) and no clj-core API
  declares `@ local` params yet, `unique_` has no expression syntax in
  OxCaml 5.2 and persistent collections are aliased not unique.
- **`--strict`** — heterogeneous literals require `^any`-family
  annotation; every `any` in a program is one the author wrote.
- **Named `fn` self-recursion, `case`, `defrecord` (map-backed ctor +
  predicate), `map?`, `& rest` varargs, `cond`/`->`/`->>`** — covered
  by test/loopcase.lg et al. `(fn f [x] … (f …))` binds `f` to itself
  and emits `let rec`; `loop`/`recur` was deliberately dropped (named
  `fn` covers it; OCaml TCO is native).

Deferred: nominal `TCon` record types (defrecord stays map-backed);
deeper OxCaml coverage needs a clj-core borrow-annotation pass (`@ local`
on non-retaining params) so collection `stack_`/`local_` can flow —
see §OxCaml notes. Building clj-core/rrbvec under OxCaml also requires
stripping their `melange`/`js_of_ocaml` stanzas (the ox patch set) plus
two locality fixes (`Seq.iter` partial-application, `List.mem` mli mode).

## 11. Standard library + semantic notes

- **`lib/test.lg`** — clojure.test in lg: `deftest`/`is`/`testing`/`are`/
  `run-tests`. Registry is annotated `atom`s (`^(atom (vec symbol))` for
  order, `^(atom (map symbol (fn [] unit)))` for cases). No exceptions:
  `is` records `FAIL <name>: <form>` via macro-time `str` of the form.
- **`lib/qc.lg`** — property-based testing. A generator is
  `(tuple (fn [int] (tuple a int)) (fn [a] (seq a)))`: `sample` maps a
  seed to a value plus next seed, `shrinks` enumerates smaller
  candidates. `gen-int`/`gen-bool`/`gen-elem`/`gen-string`/`gen-vec`/
  `gen-list`/`gen-map` build values; `for-all` runs n trials over a
  fixed-seed splittable LCG (deterministic output — golden-testable),
  `for-all2` covers two-generator properties, `shrink-min` walks the
  shrink candidates greedily to a minimal counterexample.
- **`seq` is the universal collection interface.** `TSeq` unifies with
  `TList`/`TVec`/`TSet`/`TMap` in both directions; the emitter realizes
  the conversion (`Seq.of_vec`/`of_list`/`of_set`/`of_map` and
  `Seq.to_list` + re-collection), element-wise when the element type
  also crosses a boundary. Stored signature types govern cross-module
  call boundaries: argument and result conversions use the callee's
  declared scheme (free type variables appear as `dyn`), not the
  call-site instantiation.
- **Predicates.** Tag predicates (`int?` … `coll?`, `nil?`, `some?`,
  `none?`, `fn?`) dispatch on the `Lg_rt.dyn` tag for `any` scrutinees
  and constant-fold statically. `fn?` is always `false` — functions are
  never boxed. Numeric preds (`zero?` … `odd?`) unbox `any` via
  `as_int`/`as_float`.
- **`=`/`not=` are structural.** They dispatch on the operand's static
  type — `Clj_core.Vec.equal`/`Map.equal`/`Set.equal` for collections
  (polymorphic `=` would hit the compare fn carried inside `Map.t` and
  crash), `Lg_rt.dyn_eq` for `dyn` payloads, `=` for scalars.
- **`juxt` returns `vec`.** Homogeneous when branch results unify,
  `vec<any>` otherwise (call-site emit boxes each branch result).
- **Seqable builtins take any collection.** `zipmap`, `sort`, `concat`,
  `apply`, `into`, `mapv`-family unify on the *element* type via
  `with_coll`, and emit listifies with `as_list`.

## Invariants (do not break)

- No `Obj.magic` anywhere; heterogeneity uses the `Lg_rt.dyn` closed
  variant.
- Emitted data structures are `Clj_core.*` only.
- Vanilla OCaml emit is always a working path — OxCaml output is
  additive, never required.
- Mode inference is sound-by-construction: when in doubt, a binding is
  `Shared` (GC), never wrongly `Local`/`Owned`.
- Macro expansion never lets an introduced binding capture a user
  variable (`__hN` + mark table).


## 12. Lazy sequences (M3)

Sequence-producing builtins return `(seq T)` = `'a Clj_core.Seq.t` and
transform lazily; realization happens at `vec`/`set`/`into`/`doall`/
`dorun`/`count`/`reduce`/`first`/`next`/`rest`/`nth`/`str`/`println`.
`cons` accepts any collection and returns `seq`. `(seq c)` returns
`option` — `nil` on empty, matching Clojure. Element types cross the
`any` boundary with `Clj_core.Seq.map` box/unbox adapters at emit time.


## 13. Variants and declare (M4)

`defvariant` declares an OCaml variant type: fields are `[name type]`
vectors, type parameters share `ty_of_form` bindings across ctors, and
ctors register as global functions (or constants for 0 fields). `match`
gains ctor patterns `(ctor p...)` compiled to real OCaml matches via the
`EVariant` IR node. `(declare n)` registers a monomorphic forward
signature so `defn` bodies can call later-defined globals; emit groups
consecutive `tis_fn` tops into `let rec .. and ..`, so declared calls
resolve inside the rec group.


## 14. Diagnostics (M5)

`src/err.ml` renders Elm-style blocks: `error[Ecode]` + `--> loc` +
source line + caret span + `=` hints. Every legacy `Type_error` /
`Compile_error` path renders through it as E100, so old errors get
snippets for free. `Typ.unify` reports E101, unresolved symbols E102
with Levenshtein "did you mean" suggestions over env+globals+builtins,
reader errors E201. `infer_match` records pattern coverage per scrutinee
and warns W401 (variant ctors missing), W402 (option/bool partial) when
there is no `_` or catch-all binder.


## 15. Tooling (M6)

`src/fmt.ml` canonicalizes forms: flat under 90 columns, else vertical
layout. Fidelity is preserved: the reader's `~preserve` mode (fmt only)
reifies `#_`/`#?`/`#?@` as pseudo-lists headed by `"#_"`/`"#?"`/`"#?@"`
symbols so discarded forms and all reader-conditional branches survive;
`;` comments are collected by a string/char-aware scanner and re-attached
to forms by source line (leading, first-line trailing, last-line
trailing, or injected inside a multi-line span at the last line's
indent); blank lines between top-level forms are kept. `lg repl` keeps a session buffer of def forms
and evaluates expressions by appending `(println <expr>)` and rebuilding
— ~1s per line, real compiled semantics. `src/lsp.ml` is a stdio
JSON-RPC server with a hand-rolled field extractor (no JSON dep):
hover walks the typed IR (`tops` + `effects`) for the nearest expr on
the line and shows `string_of_ty`; definition maps the token at point to
top-level `tdef` locations.


## 16. Packages, init, doc, release (M7)

`lg.edn` parses with the lg reader (edn maps are lg maps). `Pkg.find_manifest`
walks up from the source file; `:path` deps add the dir as a module
root, `:git` deps clone to `.lg/deps/<name>` with optional `:sha`
checkout; `lg deps` resolves and writes `lg.lock`. `lg init` scaffolds a
project. `lg doc` prints each top's inferred scheme as markdown —
`.lgi`-gated defs keep their exported signature. `lg version` reports
the embedded version. `tools/release.sh` + `.github/workflows/release.yml`
build os/arch tarballs on `v*` tags.
