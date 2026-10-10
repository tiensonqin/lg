# lg core stability plan

Working document: what it takes to call the lg v1 core "stable", what is
frozen today, what needs one change first, and what stays experimental.
Read alongside docs/design.md (the design contract) and docs/v2.md (the
forward plan). Line references are to `src/` as of the v1 commit.

**What "stable" means here:** a program that `lg check` accepts today keeps
compiling with the same observable behavior; a program it rejects keeps
being rejected. Error *message text* is not stable; error *classes* are.

Classification: **(a)** frozen-now — semantics verified in code, keep as
is; **(b)** needs one change before freeze — underspecified, mismatched
with docs, or emits ill-typed OCaml today; **(c)** experimental — may
change or be removed without a major bump.

## 1. Freeze surface

### 1.1 Reader

`src/reader.ml` accepts the following. `(a)` unless noted.

| Element | Class | Notes |
|---|---|---|
| `,` as whitespace | a | |
| `;` line comment | a | |
| `#_` discard next form | a | |
| `( )`, `[ ]`, `{ }` (even forms required), `#{ }` | a | |
| `'f` quote | a | hetero-quote inconsistency is §1.2 `quote` |
| `` `f `` `~x` `~@xs` | a | read everywhere; **evaluated only inside `defmacro` bodies** — in ordinary code `syntax-quote` is an unresolved-symbol error. Freeze that restriction. |
| `^meta` | a | which meta keys mean what: §1.4 |
| `@x` → `(deref x)` | a | |
| `\c`, `\newline …`, `\uXXXX`, `\oNNN` | a | `\u0041`→A, `\o101`→A (byte-wide, >255 is a read error). |
| `"…"` escapes `\n \t \r \\ \" \b \f` | a | unknown escapes are E201 read errors. |
| int literals: `±d`, `0x` hex | a | |
| float literals | a | `[+-]?(d+(.d*)?|.d+)(e[+-]?d+)?` — `1e3` `5.` `.5` `1.5e-3` all read as float. |
| `true` `false` `nil` (`nil` ≡ `unit`) | a | |
| `:kw`, `:ns/name` | a | |
| symbols `name`, `ns/name` | a | `name` may also carry `-` `?` `!` `*` `+` `<` `>` `=` `.` |
| `#(` fn literal, `#'` var quote, tagged literals, regex `#"…"` | c | absent; adding later is non-breaking |

### 1.2 Special forms

Dispatched in `infer_call` (src/infer.ml). `(a)` unless noted.

| Form | Class | Notes |
|---|---|---|
| `if` (2- and 3-ary) | a | strict `bool` condition; `any` condition → `Lg_rt.dyn_truthy`. No truthiness coercion on static types — a deliberate divergence from Clojure, spec it. |
| `do` | a | |
| `let` | a | sequential (later bindings see earlier); binding forms may destructure (§1.2.1) |
| `fn` | a | `(fn name [ps] …)` binds `name` to itself — emits `let rec` (self-recursion is the only recursion primitive). |
| `when` | a | returns `any` — the body value or `nil` (dyn punning, same as 1-branch `if`). |
| `and`, `or` | a | value-returning; mid args may be `bool`, `any` (dyn truthiness), or any concrete type (statically truthy); a non-`bool` last arg makes the result `any` (value\|false/true union). |
| `cond` | a | fallthrough is `nil` (`any`), consistent with `if`/`when`. |
| `->`, `->>` | a | special forms (not macros); insert first/last arg |
| `match` | a | first-match order; variant/option/bool scrutinees get W401/W402 inexhaustive warnings (`_`/binder silences); fallthrough keeps the `no-match` trap for open types. |
| `(Some x)` / `None` | a | option constructor / pattern; bare `Some` unapplied is unresolved — spec |
| `if-let`, `when-let` | a | binds the payload of an `option`; `when-let` else is `nil` (unit) |
| `quote` | a | heterogeneous quoted literals degrade to `any`, same as bracket literals. |
| `(:k m)`, `(:k m d)` | a | keyword in call position = `get` |
| `loop`/`recur`, `set!`, `throw`/`try` | a | **absent by design** (design.md §1) — calls parse as applications and fail at symbol resolution (E102); that rejection is the frozen behavior. |

#### 1.2.1 Binding/destructuring forms — `(a)`

In `let`, `fn`, `defn` params and `match` vector/map patterns:

- sequential vector patterns `[a [b c]]` — arity-checked via `nth`
- map patterns `{:keys [..] :strs [..] :as s :or {..}}`, `{sym :kw}`,
  `{sym "s"}`, `{:kw pat}` entries
- `nil` pattern binds nothing
- patterns on `any` rhs unbox first (`EUnbox` to `TVec TAny` /
  `TMap (TAny,TAny)`); `:keys` results are `option` (missing key → `None`),
  `:or` default unwraps it — the source of `if-let`'s usefulness
- `^T` annotation on a pattern unifies with the rhs type — enforced

Resolved: `:or` keys by the bound symbol across every entry form —
`{s :kw}`, `{s "s"}`, `{:kw s}`, `{"s" s}` (previously the two sym-key
forms looked the default up by the key's name, so `{s :kw} :or {s d}`
silently missed). A non-symbol sub-pattern (`{:kw [a b]}`) defaults by
the key's own name (`:or {q [..]}`).

### 1.3 Modules: `ns` / `:require`

| Element | Class | Notes |
|---|---|---|
| file = module; name from path or `(ns name …)` | a | entry basename or explicit `ns`; `foo.bar` → `foo/bar.lg`, `foo_bar.lg`, `foo.bar.lg` search per `-I` root + requiring file's dir |
| `(ns name (:require [ns] [ns :as a] …))` | a | `:require` is the only clause |
| bare top-level `(:require …)` | a | routed through `require_spec` + `scan_ns` — loads deps, registers aliases. |
| `alias/f`, `full.ns/f` references | a | first `/` splits ns from name |
| dep-first load order, transitive requires | a | |
| top-level defs public unless `.lgi`-unlisted | a | `.lgi` shipped (v2) — listed = exported, unlisted = private |
| `:refer` / `:use` / `:import` | c | absent; adding is non-breaking |

Resolved: ns `foo-bar` and `foo_bar` both munge to OCaml module `Foo_bar` —
`compile_path` now rejects the collision (and a repeated ns name across
files) with E100 naming both namespaces.

### 1.4 `^meta`

`split_meta` (src/infer.ml) reads metadata. Malformed `^{:sig …}` forms
and unknown `^{:key …}` keys are compile errors with carets — nothing is
silently dropped.

| Meta | Class | Notes |
|---|---|---|
| `^T` on `let`/`fn`/`defn` binding or param | a | assertion — unifies with inferred type |
| `^{:sig (fn [t …] r)}` / `^{:sig (fn [t …] -> r)}` on `def`/`defn` name | a | enforced; `'a` inside is rigid |
| `^{:sig (fn [int -> int])}` | a | malformed sigs are compile errors with caret (no silent drop); the inside-vector arrow form stays rejected. |
| `^(fn [t …] r)` bare type on defn arglist | a | honored — a `List` meta parses as a type and unifies against the fn. |
| `^T` on `defn` name | a | non-`fn` `^T` annotates the return type (Clojure convention); `^(fn …)` annotates the whole fn. |
| `^:local` `^:owned` `^:shared` | a | topdef-only — on `let` binders they are a compile error. |
| `^any`, `^(option T)` on an `any` expr | a | checked `EUnbox`/`EUnboxOpt` (`as_*` raises `invalid_arg` on wrong tag) |
| unknown meta keys `^{:foo …}` | a | compile error — only `:sig :implicit :local :owned :shared` are keys. |

### 1.5 Builtins

127 `reg` calls register the builtin table (src/infer.ml) plus the
numeric/comparison batches; `is_special_builtin` has 112 entries.
`kw-get` is the one special *not* in `builtin_table` — internal, emitted
by destructuring; `dyn-eq` and `no-match` are internal too and never
user-visible — they stay unfrozen.

Both systemic hazards are **resolved**:

1. **`any` operands → defined dyn operations.** `(= x y)` on `any`
   emits `Lg_rt.dyn_eq`; `not` routes through `dyn_truthy`; the ordering
   ops `<` `<=` `>` `>=` on `any` use `dyn_cmp` (handles mixed
   int/float, fails loudly on non-scalars); `int`/`float`/`name` on a
   non-convertible *static* type is a compile error (E100), on `any` a
   checked `as_*` unbox.
2. **Builtins as first-class values.** 116 builtins emit real dispatch
   closures (see `emit_builtin_value`): `(map first [[1 2] [3 4]])`
   compiles and runs. Any other special builtin in value position is a
   static error (E100 `cannot be used as a first-class value`) —
   enforced by `check_builtin_values` in infer.ml, never a runtime
   `failwith`.

Per-builtin classification (`(a)` = frozen-now):

**(a) — frozen-now (66):**

- arithmetic: `+ - * /` (int; promote to `.` float ops on float args;
  variadic folds left; unary `-`/`-.` negate), `+. -. *. /.`, `inc dec
  mod abs` — note `/` is truncating int division, `mod` is OCaml `mod`
- `identity`, `constantly`
- `list cons concat range` (`range` → `int list`, 1- or 2-ary)
- `atom deref reset! swap!` (+ `@` sugar)
- `str print println pr-str` (variadic; printers per static type)
- `keyword symbol` (from string)
- `keys vals` (map → list), `merge dissoc assoc` (map/vec), `conj`
  (vec-append, list-prepend, set, `[k v]` pair → map), `disj union` (set),
  `peek pop` (list/vec ends → option)
- `map filter reduce mapv filterv mapcat` (f-first arg order; `reduce` is
  3-ary only), `every?` (pred → `bool`), `take-while drop-while` (list
  only), `zipmap` (lists → map), `group-by frequencies` (list → map),
  `interpose distinct second last butlast` (list), `reverse` (list;
  on vec → vec)
- `vec set` (seq → collection)
- `nth` (2-ary: raises on OOB; 3-ary default)
- `some? none?`, `(Some …)`, `None`
- `comp juxt` (2-ary only), `partial` (n fixed + 1 trailing)
- `empty? count` (all collection kinds + string)

**(b) — all resolved; the rows below record the landed semantics:**

| Builtin(s) | Frozen semantics |
|---|---|
| `=` `not=` | `dyn_eq` on `any`/mixed reprs; `Vec/Map/Set.equal` per kind; `=` on scalars — all checked in `test/parity.lg` |
| `not` | `dyn_truthy` on `any`; `not` on bool; statically-truthy otherwise |
| `<` `<=` `>` `>=` | numeric only statically (int or float); `any` operands → `Lg_rt.dyn_cmp` (mixed int/float OK, `invalid_arg` on non-scalars) |
| `get` | `option` on map (`Map.get`), vec (`Vec.get`), list (`List.nth_opt`), set (`Some x`/None); `any`/het-key maps via dyn-nest; OOB → `None` — spec'd in design.md §11 |
| `update` | 3-ary missing key → `failwith` (no nil to feed f — deliberate divergence); 4-ary inserts default — spec'd in §11 |
| `take` `drop` | return `(seq elem)` on every kind (lazy seq semantics, §12) |
| `seq` | returns `option` — `None` on empty, `Some seq` else (`if-let` works) |
| `first` `next` `rest` | on map yield `(k v)` tuples in the map's key order (the `Clj_core.Map` compare order) |
| `into` | dst-driven; `any` dst is a static error (E100) |
| `int` `float` `name` | convertible static set only (numeric/char/string for `int`/`float`; keyword/symbol/string for `name`), else E100; `any` → checked `as_*` unbox |
| `contains?` | string → static error; others per-kind `mem`/`contains_` |
| `apply` | 2-ary, fixed-arity callee; multi-arity name → static error |
| `get-in` `assoc-in` `update-in` `select-keys` | work on typed and dyn maps; semantics spec'd in design.md §11 |
| `sort` `sort-by` | 1-ary `sort` ascends via `Stdlib.compare`; 2-ary comparator is `fn[a a -> int]` returning compare-sign (negative = a first); `sort-by` compares key-fn results via `Stdlib.compare` |
| `min` `max` | int-or-float only; other static types are compile errors (E101) |
| `some` | returns `bool` (`Seq.exists` — not Clojure's first-truthy); **kept + spec'd** |

**(c) — experimental / dead (4 + syntax):**

Resolved: `vector`/`hash-map`/`hash-set` dead dispatch cut (infer, emit,
modes tables); literals cover them. `kw-get` stays — it is the internal
builtin destructuring compiles down to.

`& rest` varargs moved to (a): implemented (`rest : 'a list`, call sites
wrap extras in a list literal) and spec'd in README/design §10.

Note §6 argues ~18 of the (a) names (`second butlast interpose distinct
frequencies group-by zipmap mapcat juxt comp partial take-while
drop-while every? reverse last peek pop`) should be *implemented* as a
shipped `core.lg` library instead of emitter special-cases — but with
identical semantics that move is invisible to users, so they can still
be (a) now.

### 1.6 Macros (`defmacro`)

| Element | Class | Notes |
|---|---|---|
| `(defmacro name [params & rest] body…)` | a | form-level evaluator; args arrive as raw forms; returns a form |
| hygiene via `__hN` marks + mark table | a | introduced binders can't capture user vars — invariant in design.md |
| `gensym` | a | macro-time only |
| macro eval subset: `if do let fn quote` + eval builtins | a | `map mapv filter reduce apply meta with-meta not` implemented over mvals; the advertised list now matches the implementation. |
| cross-module macros via `ns/m` | a | unqualified lookup restricted to the expanding macro's own module — no last-wins global fallback. |
| `defmacro` multi-arity / docstring | c | absent |
| macro must be defined textually before use | a | spec the ordering rule |

### 1.7 Top-level semantics

| Element | Class | Notes |
|---|---|---|
| `def` `defn` `defmacro` at top level only | a | nested `def` is unsupported — spec |
| def-with-docstring `(def name "doc" v)`, `(defn name "doc" …)` | a | `defmacro` lacks docstring — add or spec |
| **effect ordering** | a | `TEffect` rides in `tops` — effects emit at source position; they split `let rec .. and ..` groups (correct: a crossing effect breaks the cycle). |
| `f` multi-arity name as a *value* | a | static error — "call it with a matching argument count". |
| `__aN` arity-mangled globals | a | internal; freeze only that `f__aN` is reserved |

## 2. Stability policy

Version the **language** (`lg` version, stamped by `lg version`)
separately from the compiler build.

- **MAJOR**: removing/renaming anything in §1's frozen set; grammar
  changes that reject previously-accepted programs; type-rule changes
  that reject previously-accepted programs (e.g. making hetero literals
  an error); builtin semantic changes (arg order, return type incl.
  option-ness, failure modes, printer output shape); `Lg_rt.dyn` tag
  changes; `.lgi` format changes once frozen.
- **MINOR**: new builtins, new special forms, new `ns` clauses, new meta
  keys, new reader macros, loosening a static error into acceptance.
- **PATCH**: bug fixes that don't change accept/reject or observable
  behavior; emitted-`.ml` text; `Lg_rt` internals; munging schemes;
  mode report format (until modes freeze); error message wording.

**Not covered by compat:** the emitted `.ml` file is internal — anything
observable through it (module names except as seen by `ns/name`
references, `__N`/`__hN`/`__aN` renamings, embedded prelude) may change.
Programs must not `open Lg_rt` or depend on emitted names; OCaml-level
interiority is the escape hatch and is explicitly unstable until an FFI
story exists.

**Experimental gating:** the `-Xname` flag mechanism described here was
never implemented — shipped features (`--strict`, implicit params,
`--backend=oxcaml`) landed as ordinary flags/backends instead. If a
gating mechanism is added later, a `-X` flag may turn on reader
extensions, new forms, or looser typing and carries no compat promise;
`^{:experimental …}` meta is *not* the gate — meta can't guard reader
syntax.

## 3. Spec skeleton (normative spec for lg v1 core)

Writable **now**: sections 1–9 and 11–12 (`.lgi` and implicit params
shipped in v2). Section 10 stays informative until OxCaml settles.

1. Reader grammar — literals, delimiters, comments, `^`/`'`/`` ` ``/`~`/`@`/`#_`. ← reader.ml is the de facto grammar; write it down including the open items in §1.1.
2. Forms and the `form`/`mval` data model — what macros see. ← syntax.ml.
3. Types — `ty` table (typ.ml), type-expression grammar (`ty_of_form`), rigid vars, `TAny` no-op unification, occurs check.
4. Special forms — per form: shape, typing rule, desugar/lower target, failure modes. ← §1.2 of this doc.
5. Binding/destructuring — the `bind_pattern` matrix incl. `:keys/:strs/:as/:or`, `option` results, `any` unboxing.
6. Builtin table — per builtin: arities, arg order, per-collection-kind dispatch, return type, missing-key/OOB/empty behavior. This is the largest normative table; generate it from `builtin_table` + `infer_special` + tests.
7. `any`/`dyn` boundary — when `any` enters (`^any`, hetero literals), `Lg_rt.dyn` tags, checked unbox sites, `dyn_truthy`, dyn equality (once §1.5's `=` decision lands).
8. Modules — file=module, `ns` form, `:require` shapes, search order, visibility (all-public in v1).
9. Macros — `defmacro` grammar, eval subset, hygiene guarantees, expansion order, error behavior.
10. Modes — **informative**: `Local` lowers to real OxCaml annotations
    (design.md §10 three tiers); `Owned`/`unique_` has no expression
    syntax in OxCaml 5.4. Spec section stays non-normative until the
    OxCaml surface settles.
11. `.lgi` interface files — shipped (v2): listed = exported, unlisted
    = private, `(private n)` preserved across `lg lgi` regeneration.
12. Implicit parameters — shipped (v2): `^:implicit`/`^{:implicit T}`
    resolved by type at call sites, elaborated to ordinary OCaml args.

The spec for 1–9 can be written against current behavior + the §1
decisions; sections 10–12 should exist as stubs that say "not part of the
v1 core."

## 4. Regression / compat harness

Today `test.sh` runs `check → build → run → diff` over `test/*.lg` +
`*.out`, and `should_fail/*.lg` assert exit-status only. To certify a
release:

1. **Emitted-OCaml typecheck gate — DONE.** `test/emit_matrix.py`
   compiles every `lg check`-accepted builtin×type combo through OCaml
   (386 cases, CI enforces 0 emit FAILs), and `test.sh` builds+runs
   every golden. The five verified instances (`=`/`not`/cmp on `any`,
   `take`/`drop` on set & string, `int`/`name` identity fallthrough,
   `Some`-pattern on `any`, builtin-as-value) are all fixed: `any` ops
   go through `dyn_*` helpers or are static errors, `take`/`drop`/`seq`
   return lazy seqs, `int`/`float`/`name` reject non-convertible
   static types, builtins lacking value closures are E100.
2. **Builtin × collection-kind matrix.** `map`/`first`/`count`/`get`/`conj`/`take`/`drop`/`into`/`seq`/`reverse`/`sort`/`contains?` dispatch by static coll type (vec/list/set/map/string) — golden-test each cell that's allowed and assert each forbidden cell is a static error, not a build failure.
3. **Emit snapshots.** `lg emit` output diffed per test — catches codegen
   regressions invisible to `.out` diffs. Requires deterministic emit
   (binder counters are process-global; single-process emit is
   deterministic today — spec it).
4. **Negative-message classes.** `should_fail` stays exit-code, but add a
   `.err` glob check per feature (arity, mismatch, unbound, private-ref
   post-`.lgi`, macro arg misuse, `TAny`-leak sites) so a regression that
   fails for the wrong reason is caught.
5. **Macro corpus — DONE.** `test/hyg.lg` (hygiene/capture attempts),
   `test/macros.lg` (defmacro incl. `~@`/nested squote), and
   `test/_hyglib.lg` (cross-module macro module) run in `test.sh`.
6. **Cross-backend parity.** `lg build` already falls back ocamlopt →
   ocamlc; run the same `.out` diffs on native *and* byte, and add a
   melange/js_of_ocaml lane when the runtime is wired (clj-core already
   builds `melange`). Byte-identical program output across backends is
   the parity claim.
7. **Compat corpus.** `test/compat/` frozen at v1.0: programs are only
   added, never edited; every release must run them green. Distinct from
   `test/` which may evolve.
8. **Wire `examples/` into the suite** or move its coverage into `test/`.
9. **Reader round-trip:** parse → `form_to_string` → parse → equal forms
   (form-level equality exists in macro.ml for `=`).

## 5. Sequencing vs v2.md

Order that freezes the core fastest:

**Phase 0 — reconcile code ↔ docs (unblocks everything).** All §1 (b)
items: fix silent meta drops, pick `when`/`cond`/`seq`/`get`/`update`
semantics, kill ill-typed emissions, decide `loop`/`set!`/`throw` vs
design.md, `(:require)` top-level, `vector`/`hash-map`/`hash-set`,
named-`fn` self-recursion, hetero quote, `macro_by_name` fallback,
def/effect ordering, multi-arity value-use. These are all small diffs;
none require v2 machinery.

**Phase 1 — freeze reader + special forms + type rules + builtin table →
v1.0-rc.** Syntax and types freeze first because every later feature
(implicits, `.lgi`, OxCaml) is expressed in them. The §3 spec sections
1–9 get written in the same pass — writing the normative table *is* how
the remaining underspecification gets found.

**Phase 2 — `.lgi` (v2 #2).** Lands *before* implicits because implicits'
`:implicits true` clause and dictionary export rules ride on the
interface file. `.lgi` is compatible with a frozen v1: it only adds the
*ability to hide* — a program valid at v1 stays valid with a complete
`.lgi`. Freeze the `.lgi` format at v1.1.

**Phase 3 — implicit parameters (v2 #1) behind `-Ximplicits`.**
Graduate when the dictionary-resolution rules have real usage; the
frozen core never notices (elaboration is additive).

**Phase 4 — modes.** Keep advisory forever on the vanilla backend; do
*not* freeze mode semantics in v1 — they become real (and
checked-by-OxCaml) only with v2 #3. Freeze only the `lg modes` report
*format* if we promise anything at all. FBIP (v2 #4) and the OxCaml
backend themselves are emitter-internal — additive, no compat surface.

**Phase 5 — `--strict` (v2 #6), records/loop/cond-macros (v2 #7).** All
additive; `--strict` is itself the model for `-X` gating.

Rationale: freeze what's load-bearing (grammar, types, builtins) while
it's small; let every later feature arrive as a MINOR on top.

## 6. Kill list

Argued from the code:

1. **`loop`/`recur`, `set!`, `throw`/`try`** — claimed by design.md §1,
   absent from the implementation. Cut from the v1 surface explicitly:
   self-recursive `defn` + OCaml TCO covers loops; there is no `set!`
   target semantics worth freezing; exceptions deserve a designed story,
   not a half-port. Re-adding is a MINOR.
2. **`vector`/`hash-map`/`hash-set`** — done: dead dispatch entries cut;
   `[…]`, `{…}`, `#{…}` literals cover them. Register later only if
   `apply`-style use cases appear.
3. **Most seq/HOF builtins → `core.lg`.** `second butlast interpose
   distinct frequencies group-by zipmap mapcat juxt comp partial
   take-while drop-while every? reverse last peek pop` are each ~5 lines
   over `defn`+destructure. Shipping them as a *library* file (that lg itself
   compiles) instead of frozen emitter special-cases shrinks the
   certified surface and lets the stdlib grow in MINORs. Keep frozen only
   the ones the emitter de-sugars into (`first`/`nth`/`get`/`kw-get`,
   `count`, `=`, printers, atom ops, `Some`/`None`/`option`).
4. **`get-in`/`assoc-in`/`update-in`/`select-keys` on dyn maps** — the nest-map
   bridging in emit.ml (~80 lines: `nest_map_of`, `box_nest`,
   `dyn_map_*`, `Lg_rt.dyn_map_of_nest_map`) is the heaviest machinery
   for the narrowest use, and it forces `(map keyword any)` widening.
   Cut to keyword-literal get/set only, or defer to records (v2 §7).
5. **Mode hints `^:local`/`^:owned`/`^:shared`** — advisory-only,
   silently dropped on `let` binders, and the real version is OxCaml
   annotations (v2 §3). Drop the syntax now; return it as the OxCaml
   lowering's surface later.
6. **`macro_by_name` global fallback** — a bare macro name resolves to
   the last-registered macro with that name *across all loaded modules*.
   Restrict unqualified macro lookup to same-module; cross-module always
   via `ns/m`. Removes a silent collision.
7. **Value-use of multi-arity names** — `greet` silently means
   `greet__a1`. Make it a static error at freeze (relaxation is a MINOR).
8. **`some`** — keep the name but spec that it returns `bool`
   (`List.exists`), not Clojure's first-truthy-value; or rename to
   `exists?` before freeze since renames after are MAJOR. (Open question
   — flag for maintainer.)

## Open questions

- `dyn` equality: OCaml `=` on `Lg_rt.dyn` compares clj-core internals
  (RRB-tree shape), not logical content — two equal vecs may differ.
  Need `Lg_rt.dyn_eq` walking `Clj_core` equality before `=`/match-literal
  on `any` is correct.
- `Map.seq` iteration order is unspecified → `keys`/`vals`/`first` on
  maps and map printing inherit it. Golden tests currently pin whatever
  order falls out — spec needs a stated order or an explicit
  "unspecified, don't rely" clause (the latter still needs deterministic
  *within a run* for tests).
- `foo-bar`/`foo_bar` module-name collision into `Foo_bar`.
- Does `check` passing but `build` failing on ill-typed OCaml count as a
  compile error? (Yes — close the gap via the emit-typecheck harness
  item, then spec "check implies buildable".)
- `nil` is `unit`, `()` is also `TList` of nothing (`EListLit []`) — same
  value, two readings. `(= nil '())`? spec.
- Effect/def ordering (§1.7) — fix or spec the two-phase rule.
- Float printer `%g` format is part of observable output — golden tests
  already depend on `3.` printing as `3.`; pin the format or document it
  as unstable.
