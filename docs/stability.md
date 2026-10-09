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
| `loop`/`recur`, `set!`, `throw`/`try` | c | **listed in design.md §1 but not implemented** — calls silently parse as applications and fail at symbol resolution. Cut from the v1 surface (§6) or implement. |

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

Open: `:or` defaults apply only to `:keys`/`:strs`/symbol-key entries, not
to `{:kw pat}` form — spec.

### 1.3 Modules: `ns` / `:require`

| Element | Class | Notes |
|---|---|---|
| file = module; name from path or `(ns name …)` | a | entry basename or explicit `ns`; `foo.bar` → `foo/bar.lg`, `foo_bar.lg`, `foo.bar.lg` search per `-I` root + requiring file's dir |
| `(ns name (:require [ns] [ns :as a] …))` | a | `:require` is the only clause |
| bare top-level `(:require …)` | a | routed through `require_spec` + `scan_ns` — loads deps, registers aliases. |
| `alias/f`, `full.ns/f` references | a | first `/` splits ns from name |
| dep-first load order, transitive requires | a | |
| all top-level defs public | a | until `.lgi` lands (v2 §2) — `.lgi` is additive, not breaking |
| `:refer` / `:use` / `:import` | c | absent; adding is non-breaking |

Open: ns `foo-bar` and `foo_bar` both munge to OCaml module `Foo_bar` —
collision, currently unhandled.

### 1.4 `^meta`

`split_meta` (src/infer.ml) reads metadata. The traps below are verified:
an unparseable annotation is **silently dropped** instead of erroring.

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

95 names are registered in `builtin_table` (src/infer.ml): 74 via `reg`
calls plus two `List.iter` batches (the 12 numeric/comparison ops and
`first next rest seq get nth conj range apply`). `is_special_builtin`
has 59 entries; four of them — `vector`, `hash-map`, `hash-set`,
`kw-get` — are *not* in `builtin_table`, so `(vector 1 2)` fails
`unresolved symbol vector`. `kw-get` is internal (emitted by
destructuring); `dyn-eq` and `no-match` are internal too and never
user-visible — they stay unfrozen.

Two systemic hazards cut across the table:

1. **Ill-typed emission on `any` operands.** `check` accepts, `build`
   fails in OCaml. Verified: `(= x 3)` on `x : any` emits `dyn = int`;
   `(not x)` on `any` emits `not dyn`; `<` etc. on `any` unbox `as_int`
   only (`DFloat` → `invalid_arg` at runtime); `Some`/`None` match
   patterns on an `any` scrutinee emit `match dyn with Some …`. Freeze
   requires: each `any`-touching builtin either does a defined dyn
   operation or is a static error — never ill-typed output.
   `(int :a)`, `(name 5)`, `(float #{})` are the same class: the emit
   fallthrough returns the arg unchanged while claiming `int`/`string`.
   Fix: static error or explicit `failwith`, never identity.
2. **Collection dispatch is per-call-site.** `map`/`first`/`count`/… pick
   an implementation by the *static* type of the coll argument. Used as
   a first-class value (`(map first vecs)`), builtins take the
   `emit_builtin_value` fallback — which is list-shaped at best
   (`first` as a value only matches OCaml lists) or
   `failwith "builtin as value"` for ~55 names. Verified:
   `(map first [[1 2] [3 4]])` checks OK, fails at build. Freeze
   requires: per-builtin decision — generate a real dispatch closure or
   statically reject non-call use.

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

**(b) — needs one change before freeze (29 builtins):**

| Builtin(s) | Issue |
|---|---|
| `=` `not=` | on `any` operand → ill-typed OCaml; also OCaml `=` on `dyn` collections compares internal RRB-tree shape, not logical content — needs a defined `dyn` equality (or static rejection). Also verify rigid-var args can't materialize as dyn (design.md §3). |
| `not` | `any` operand → ill-typed OCaml |
| `<` `<=` `>` `>=` | `any` operand assumed `as_int` — a `DFloat` fails at runtime; variadic form chains correctly but spec it |
| `get` | 2-ary returns `option` on map (`Map.get`), vec (`Vec.get`), list (`List.nth_opt`), set; on `any`/het-key maps routes through dyn-nest — spec each kind's missing-key behavior |
| `update` | `(update m k f)` **failwith on missing key** — verified emission `failwith "update: missing key"`. Clojure calls `f nil`. Decide: keep fail-fast (spec it), take a default arg, or return `option`. |
| `take` `drop` | return declared as *same type as input* but on set/string emit a list — ill-typed OCaml. Fix type to `(list elem)` or restrict to vec/list. |
| `seq` | returns `TList`, never `option` — empty is `[]` not `nil`, so `(if-let [x (seq c)] …)` is a type error. Spec the `[]`-is-empty convention vs switching to `option`. |
| `first` `next` `rest` | on map yield `(k v)` tuples in `Map.seq` order — spec that order's guarantees (unspecified today) |
| `into` | dst-driven; on `any` dst assumes vec; spec |
| `int` `float` `name` | identity fallthrough on wrong input → ill-typed OCaml (hazard 1) |
| `contains?` | on string → runtime `failwith`; make static error or implement |
| `apply` | 2-ary only, callee fixed-arity or list-last — spec; `apply` on a multi-arity name is open |
| `get-in` `assoc-in` `select-keys` | require/force `(map keyword any)` — calling them on a *typed* map widens the result to `any`-valued. Spec the widening or restrict to dyn maps. |
| `sort` `sort-by` | `sort`'s 2-ary comparator takes `fn[a a -> int]` — spec the sign convention (`Stdlib.compare`) and which kinds are sortable |
| `min` `max` | int-or-float only; on other types unify forces int → `Stdlib.min` on non-numeric is a type lie. Restrict statically. |
| `some` | returns `bool` (`List.exists`), not Clojure's first-truthy value — keep + spec, or rename `exists?` before freeze (a rename after is MAJOR). Flag for maintainer. |

**(c) — experimental / dead (4 + syntax):**

| Item | Reason |
|---|---|
| `vector` `hash-map` `hash-set` `kw-get` | in `is_special_builtin` but not `builtin_table` — unreachable as symbols; literals cover the first three and `kw-get` is internal. Cut the dead dispatch. |
| `& rest` variadic defn | implemented (`rest : 'a list`, call sites wrap extras in a list literal) but v2.md §7 still lists varargs as future work — mark experimental until spec'd. |

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

Version the **language** (`lg` version, stamped by `lg --version` — flag
currently absent, add it) separately from the compiler build.

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

**Experimental gating:** features in flight land behind `-Xname`
compiler flags (e.g. `-Xstrict`, `-Ximplicits`, later `-Xoxcaml`). A
`-X` flag may turn on reader extensions, new forms, or looser typing;
using a gated feature without its flag is a defined error at the phase
that introduces it (read-time for syntax, infer-time for semantics).
`-X` features carry no compat promise; graduating a feature removes the
flag in a MINOR bump. `^{:experimental …}` meta is *not* the gate —
meta can't guard reader syntax.

## 3. Spec skeleton (normative spec for lg v1 core)

Writable **now**: sections 1–9. **Blocked** on v2 work: 10–12.

1. Reader grammar — literals, delimiters, comments, `^`/`'`/`` ` ``/`~`/`@`/`#_`. ← reader.ml is the de facto grammar; write it down including the open items in §1.1.
2. Forms and the `form`/`mval` data model — what macros see. ← syntax.ml.
3. Types — `ty` table (typ.ml), type-expression grammar (`ty_of_form`), rigid vars, `TAny` no-op unification, occurs check.
4. Special forms — per form: shape, typing rule, desugar/lower target, failure modes. ← §1.2 of this doc.
5. Binding/destructuring — the `bind_pattern` matrix incl. `:keys/:strs/:as/:or`, `option` results, `any` unboxing.
6. Builtin table — per builtin: arities, arg order, per-collection-kind dispatch, return type, missing-key/OOB/empty behavior. This is the largest normative table; generate it from `builtin_table` + `infer_special` + tests.
7. `any`/`dyn` boundary — when `any` enters (`^any`, hetero literals), `Lg_rt.dyn` tags, checked unbox sites, `dyn_truthy`, dyn equality (once §1.5's `=` decision lands).
8. Modules — file=module, `ns` form, `:require` shapes, search order, visibility (all-public in v1).
9. Macros — `defmacro` grammar, eval subset, hygiene guarantees, expansion order, error behavior.
10. Modes — **blocked**: current modes are advisory comments; freezing semantics before OxCaml would bake in guesswork. Spec section stays "informative" until v2 §3.
11. `.lgi` interface files — **blocked**: format lands with v2 §2.
12. Implicit parameters — **blocked**: v2 §1.

The spec for 1–9 can be written against current behavior + the §1
decisions; sections 10–12 should exist as stubs that say "not part of the
v1 core."

## 4. Regression / compat harness

Today `test.sh` runs `check → build → run → diff` over `test/*.lg` +
`*.out`, and `should_fail/*.lg` assert exit-status only. To certify a
release:

1. **Emitted-OCaml typecheck gate (the big one).** Every test must
   additionally pass `ocamlc -c` on its emitted `.ml` — today
   `lg check` green + `ocamlfind` red is a real failure class (five
   instances verified: `=`/`not`/cmp on `any`, `take`/`drop` on set &
   string, `int`/`name` identity fallthrough, `Some`-pattern on `any`,
   builtin-as-value). This is the single highest-value harness change.
2. **Builtin × collection-kind matrix.** `map`/`first`/`count`/`get`/`conj`/`take`/`drop`/`into`/`seq`/`reverse`/`sort`/`contains?` dispatch by static coll type (vec/list/set/map/string) — golden-test each cell that's allowed and assert each forbidden cell is a static error, not a build failure.
3. **Emit snapshots.** `lg emit` output diffed per test — catches codegen
   regressions invisible to `.out` diffs. Requires deterministic emit
   (binder counters are process-global; single-process emit is
   deterministic today — spec it).
4. **Negative-message classes.** `should_fail` stays exit-code, but add a
   `.err` glob check per feature (arity, mismatch, unbound, private-ref
   post-`.lgi`, macro arg misuse, `TAny`-leak sites) so a regression that
   fails for the wrong reason is caught.
5. **Macro corpus.** No golden test exercises `defmacro` today (the only
   one lives in `examples/hello.lg`, which `test.sh` doesn't run) —
   hygiene capture attempts, nested `squote`, `~@`, cross-module macros,
   gensym collisions.
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
2. **`vector`/`hash-map`/`hash-set`** — dead dispatch entries; `[…]`,
   `{…}`, `#{…}` literals cover them. Cut the dead code; register later
   only if `apply`-style use cases appear.
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
