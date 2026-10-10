# lg

**lg** is a functional language inspired by OCaml and Clojure. It pairs
Clojure's syntax and data structures with OCaml-style static typing and a
three-layer memory model designed to make most programs allocation- and
GC-free — without Rust-style lifetime annotations.

The compiler is written in OCaml and **emits OCaml source** (`.ml`), so lg
programs ride on the existing OCaml ecosystem: `ocamlopt`/`ocamlc` for
native and byte code, and — through the same emitted source — Melange /
js_of_ocaml / wasm_of_ocaml for JS and Wasm targets.

> Repository name: `lg2` (lg language, v2). The language itself, its file
> extension (`.lg`), toolchain binary (`lg`), and emitted runtime module
> (`Lg_rt`) are all named **lg**.

## Packages

`lg.edn` at a project root declares deps — found by walking up from the
source file:

```clojure
{:name "app" :deps {mylib {:path "../mylib"}
                    other {:git "https://…" :sha "abc"}}}
```

A `:path` dep adds that dir as a module root (no `-I` needed). `:git`
deps clone into `.lg/deps/<name>`; `lg deps` resolves and writes
`lg.lock` (`name url sha` per line).

`lg init <name>` scaffolds `src/main.lg` + `lg.edn` + `.gitignore`.
`lg doc file.lg` prints the module's public API as markdown from
inferred signatures. `lg version` prints the version.
`tools/release.sh [ver]` builds `dist/lg-<ver>-<os>-<arch>.tar.gz`;
push a `v*` tag and CI builds ubuntu+macos tarballs.

## Tools

`lg fmt file.lg` rewrites a file to canonical layout (flat under 90 cols,
else vertical) without losing source text: `;` comments are re-attached
by position (leading / same-line trailing / inside a form's span),
blank lines between top-level forms are kept, `#_` discarded forms are
re-printed, and `.cljc` `#?`/`#?@` blocks keep every branch.

`lg repl` — accumulative session REPL: `def`/`defn`/… forms persist
across inputs; expressions print their value. `:quit` exits.

`lg lsp` — stdio JSON-RPC server: `initialize`, `textDocument/didOpen`,
`didChange`, `hover` (type at position), `definition` (jump to top-level
def), `shutdown`, `exit`.

## Errors

Diagnostics are Elm-style: `error[Ecode]` with a `--> file:line:col`
pointer, the offending source line, a caret span, and `=` hints —
`did you mean \`mapv\`?` on unresolved symbols. `match` on a variant,
option, or bool without covering every case (or a `_`/binder catch-all)
emits `warning[W401/W402]`. Codes: E1xx types (E101 mismatch, E102
unresolved), E2xx reader.

## Features

- **Clojure syntax and data structures.** Code is data: lists, vectors,
  maps, sets, keywords, and symbols, backed by the persistent collections
  of [clj-core](https://github.com/logseq/clj-core)
  (`Vec`/`Map`/`Set`/`List`/`Seq`/`Atom`/`Keyword`/`Symbol`) — itself
  built on [rrbvec](https://github.com/logseq/rrbvec).
- **Hindley–Milner type inference** with optional `^T` annotations on
  bindings and `^{:sig ...}` metadata when you want to pin a contract
  down. Unannotated code is fully inferred.
- **Implicit modules.** Every `.lg` file is a module; the module name is
  derived from the path. An `(ns ...)` form is optional. Cross-file
  dependencies are declared with `(:require [ns :as alias])` and resolved
  transitively via `-I` include dirs.
- **Multi-arity `defn`, destructuring, `match`, variants, records.**
  `(defn f ([x] …) ([x y] …))` dispatches on arity (each arity is its own
  checked definition). `let`/`fn`/parameters destructure vectors
  `[a [b c]]` and maps `{:keys [..] :strs [..] :as s :or {..}}` plus
  explicit `{sym :kw}` / `{sym "s"}` bindings. `match` is a special form:
  literals, quoted literals, `[…]` (arity-checked), `{…}`, `(Some x)` /
  `None`, `_` and symbol binding — on typed *and* `any` scrutinees;
  `case` is literal-dispatch sugar over it. `(declare n)` is a forward
  declaration for mutual recursion; consecutive `defn`s emit as one
  `let rec .. and ..` group. `(defvariant shape (circle [r float])
  (square [w float] [h float]) point)` declares OCaml variant types —
  parameterized via `(defvariant (tree a) …)`, ctors are fns
  `(circle 1.0)`, matchable as `(circle r)` patterns. `(fn f [x] … (f …))`
  binds `f` to itself (emitted `let rec`) — the recursion idiom.
  `(defrecord Point [x y])` generates a map-backed `->Point` constructor
  and a `Point?` predicate. `& rest` varargs on `fn`/`defn`.
- **A confined `any` boundary.** Mixed-type literals and `^any` produce
  `dyn`-boxed values (`Lg_rt.dyn`, a closed variant — no `Obj.magic`).
  `any` never leaks into surrounding inference (it unifies as a no-op);
  `get`, `match`, and `:keys` destructuring do checked unboxing at the
  boundary (`option any` for possibly-missing keys — `if-let` unwraps).
- **Hygienic `defmacro`.** Macros run at compile time on a form-level
  evaluator with the full `syntax-quote` / `~` (unquote) / `~@`
  (unquote-splicing) reader support. Bindings introduced by a macro are
  automatically gensym'd so they cannot capture user variables; `gensym`
  is also exposed for explicit control.
- **Type predicates.** `int? float? bool? char? string? keyword? symbol?
  list? vec? set? map? seq? coll? number? nil? some? none? fn?` dispatch
  on the `dyn` tag for `any` scrutinees and constant-fold on static
  types; `zero? pos? neg? even? odd?` work on ints (unboxing `any`).
- **Structural `=` / `not=`.** Equality dispatches on the static type:
  `Clj_core.Vec.equal` / `Map.equal` / `Set.equal` for collections
  (polymorphic compare would crash — maps carry a compare fn internally),
  `Lg_rt.dyn_eq` at the `any` boundary, `=` elsewhere. `juxt` returns a
  `vec` (hetero branches box to `vec<any>`).
- **Test library (`lib/test.lg`).** clojure.test-style, in lg itself:
  `(ns t (:require [test :as t]))` then `t/deftest`, `t/is`, `t/testing`,
  `t/are`, `(exit (t/run-tests))` — no exceptions, failures are reported
  as `FAIL <name>: <form>` and counted.
- **Property testing (`lib/qc.lg`).** a generator is
  `(tuple sample shrink)` — `sample : int -> (tuple a int)` maps a seed
  to a value + next seed, `shrink : a -> (seq a)` enumerates smaller
  candidates. `qc/gen-int`, `qc/gen-bool`, `qc/gen-elem`, `qc/gen-string`,
  `qc/gen-vec`, `qc/gen-list`, `qc/gen-map` build values; `qc/for-all`
  runs n deterministic trials (fixed-seed LCG) and on failure shrinks to
  a minimal counterexample (`qc/shrink-min`), `qc/for-all2` tests
  two-argument properties.
- **Three-layer memory model — `Local` / `Owned` / `Shared`.**
  - `Local`: values that never escape their region — eligible for
    stack/region allocation (OxCaml `@local`).
  - `Owned`: uniquely-referenced values — deterministic destruction and
    FBIP-style reuse (OxCaml `unique` / Perceus).
  - `Shared`: everything else — falls back to the ordinary OCaml GC heap.
  - An escape analysis pass infers the mode of every binding. On the
    vanilla OCaml backend modes are emitted as comments and surfaced by
    `lg modes` (a per-binding report). The OxCaml backend lowers `Local`
    to real `@ local` parameters, `local_` binders, and `stack_`
    allocation sites, re-checked by the OxCaml typechecker; `Owned`'s
    `unique_` remains a comment (OxCaml 5.4 has no expression syntax for
    it).
- **`.lgi` interface files (mli-style).** A per-module sidecar lists each
  exported definition's type and per-parameter `:escapes` modes, plus
  `defvariant`/`extern-type` declarations. What a `.lgi` lists is the
  module's export surface (unlisted = private); consumers can
  `check`/`modes` against an interface without the `.lg` implementation
  — including calling and `match`-ing its variant constructors
  (`v/node …` patterns). `lg lgi` merges with the existing file:
  hand-written entries win, `(private n)` entries survive, and
  `lg lgi --all` regenerates every module in the require closure.
- **Implicit parameters (modular-implicit-style).** Trailing
  `^:implicit` / `^{:implicit T}` params are resolved by type at call
  sites and elaborated to ordinary OCaml arguments — dictionary passing
  with zero runtime cost. `(:require [ns :implicits true])` merges a
  module's exported implicit dicts. Signature-level
  `^(fn [a (implicit (fn [a] string))] string)` ties the dict to the
  argument's type var — call-site-type dispatch (see
  `examples/impdemo/`).
- **FBIP builder lowering.** Provably single-use collection literals —
  unique-owner `conj`/`assoc`/`dissoc`/`pop`/`update`/`into`/`disj`
  chains — emit `Lg_rt` growable builders plus a single freeze instead
  of persistent-structure copies. Everything else stays persistent.
- **OxCaml emit (`--backend=oxcaml`).** Verified end-to-end on an
  OxCaml (flambda2, `ocaml-variants.5.4.0+ox`) switch — emit →
  `ocamlfind ocamlopt` → run, 28/28 test programs green
  (test/oxcaml_smoke.sh). Lowering, in three tiers: `(param @ local)`
  on non-escaping params; `let x @ local` binders whose uses stay in
  borrow positions (strict consumers pick `Seq.*_local`/`Vec.*_local`
  twins by argument mode; lazy producers select their `_local` twins
  when the call's own mode is Local); and `stack_` on direct
  allocation sites (vec/list literals, tuples, `Some`, cons cells).
  Requires the `ox` branches of clj-core/rrbvec (`@ local` borrow
  annotations on non-retaining readers); `unique_` stays a comment.
  Vanilla `ocaml` stays the default backend.
- **wasm (`--backend=wasm`).** `ocamlc` bytecode → `wasm_of_ocaml`
  → `<exe>.js` + `<exe>.assets/*.wasm`, runnable under `node`. Verified:
  pure language, collections, lazy seqs, `println`, `env`,
  `file-exists?`. Degraded stubs: `now-ms`, `argv`, `re-*` (no clock /
  process args / `Str` in the wasm runtime); `slurp`/`spit`/`sh` are
  untested — io via Node belongs on the `melange` backend.
- **Melange (`--backend=melange`).** JS via `melange.emit`: produces
  `<exe>.js` (CommonJS + a `node_modules` symlink) for `node`. io and
  `re-*` work through `Lg_node`'s lazy Node probes — browser bundles
  load fine and fail only if a Node-gated builtin is invoked.
- **`--strict` mode.** Heterogeneous literals require an explicit
  `^any`-family annotation — every `any` in a program is one the author
  wrote down.
- **FFI (`ffi`, `extern-type`).** `(ffi f [:int] :int {:native "abs"})`
  binds a C symbol through ctypes (`:library` for a shared object);
  `{:ocaml "stub"}` emits a typed OCaml `external` for runtime stubs;
  `(extern-type h)` declares an opaque handle type. Bindings are
  first-class typed values that cross modules and `.lgi` exports.
  `any` never crosses the boundary. See `docs/ffi.md`.
- **OCaml interop (`ocaml.*` requires, native/oxcaml only).** Require any
  OCaml module or findlib package and call its values directly, with
  labeled/optional arguments mapped onto trailing `:kw v` pairs:

  ```clojure
  (ns app (:require [ocaml.String :as str]
                    [ocaml.Unix :as unix]
                    [ocaml.String :refer [uppercase_ascii]]
                    [ocaml.pkg/eio]))     ; package only — adds eio to -linkpkg

  (str/starts_with "hello" :prefix "he") ; → String.starts_with ~prefix:"he"
  (unix/ADDR_UNIX "/tmp/x")              ; constructors qualify too
  ```

  Signatures are read from `.cmi` files (wrapped stdlib units, findlib
  package dirs, and dune-wrapped `pkg__Mod` units all resolve). Types that
  lg cannot express — abstract types, objects, records — fail at compile
  time with `type not expressible in lg`. Unknown package, value, or label
  is a plain compile error listing what is available.

## Pipeline

```
lg source (.lg)
  → reader          (forms: lists, vectors, maps, sets, literals, syntax-quote)
  → macro expansion (hygienic defmacro)
  → HM inference    (types; ^T annotations; TAny for heterogeneous literals)
  → mode inference  (escape analysis → Local / Owned / Shared)
  → emit            (OCaml source: module per lg file, Clj_core.* calls,
                     embedded Lg_rt prelude, modes as comments)
  → ocamlfind ocamlopt / ocamlc -package clj-core,rrbvec -linkpkg
```

## CLI

```
lg check  <file.lg> [-I dir]   # parse + macro-expand + typecheck, no output
lg emit   <file.lg> [-I dir]   # write the emitted .ml next to the source
lg modes  <file.lg> [-I dir]   # print the Local/Owned/Shared mode report
lg lgi    <file.lg> [-I dir]   # regenerate the module's .lgi interface file
lg build  <file.lg> [-I dir]   # emit + compile with ocamlfind (native, byte fallback)
```

Flags: `--backend=ocaml|oxcaml|melange|wasm` selects the emit backend; `--strict`
requires `^any` on heterogeneous literals.

`-I dir` adds an include directory used to resolve `:require`d modules.

Emitted programs are self-contained `.ml` files: a header
`(* generated by lg — do not edit *)`, an embedded `Lg_rt` prelude
(printers and small helpers — collections come from `Clj_core`), then one
OCaml module per lg module (`module Util = struct … end`,
`module Hello = struct … end`).

## Example

`examples/hello.lg` (with `examples/util.lg` as a required sibling module)
exercises the v0 surface:

- implicit modules: `hello` requires `util` and calls `util/fib` — the
  emitter maps each file to an OCaml module and each `alias/fn` call to a
  cross-module reference (`Util.fib`);
- `(defn …)` top-level functions, including self-recursion (`fib`);
- anonymous fns, `let`, `if`, integer arithmetic and comparison;
- vector literals `[1 2 3 4 5]` and higher-order `clojure.core`-style
  functions (`map` → `Clj_core.Vec.map`);
- keywords, strings, and `println`/`str` from the `Lg_rt` prelude.

## Dependencies

The compiler builds with dune on an OCaml 5.5.0 switch and needs two opam
pins for the emitted-code runtime:

```
opam pin add rrbvec   https://github.com/logseq/rrbvec.git
opam pin add clj-core https://github.com/logseq/clj-core.git
```

`clj-core` builds for `native`, `byte`, and `melange`, which is what makes
the non-native OCaml backends reachable later.

## Layout

```
bin/        lg CLI entry point
src/        compiler: syntax → reader → macro → infer → modes → emit
runtime/    Lg_rt prelude (printers/helpers) embedded into emitted files
lib/        standard library in lg (test/ test framework, qc/ property tests)
examples/   hello.lg+util.lg, features.lg, csv.lg, json.lg (ADT encoder),
            jsonp.lg (recursive-descent parser), stopwatch.lg (ffi),
            wfreq/ (multi-module CLI), impdemo/ (implicit params)
test/       golden tests (.lg + .out); should_fail/ negative tests
test.sh     runner: check → build → run → diff
test/emit_matrix.py
            self-host matrix: every builtin x type combo `lg check`
            accepts must emit well-typed OCaml (CI enforces 0 FAILs)
.github/    CI: opam 5.5.0 + clj-core/rrbvec pins + melange + node
docs/       design contract, research report
```

See [`docs/design.md`](docs/design.md) for the design contract and
[`docs/research-report.html`](docs/research-report.html) for the ownership
& locality research that motivates the memory model.
