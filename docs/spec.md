# lg language specification

Normative reference for the lg v1 language. `docs/design.md` is the
design contract and rationale; this document is the user-facing
reference: precise, example-driven, organized for lookup. Every
section anchors its claims in `test/` programs so behavior can be
reproduced end to end (`lg build test/<name>.lg -o <dir>/<name>`,
or `./test.sh` for the whole suite).

## 1. Lexical structure and reader

**Forms.** Code is data: the reader produces the same literals the
language manipulates.

- **Scalars**: integers (`42`, `0x2A`, `-7`), floats (`1.5`),
  booleans (`true`/`false`), unit `()`, characters (`\a`, `\n`,
  `\space`, `\newline`, `\tab`, `\return`, `\backspace`,
  `\formfeed`; `\uXXXX` up to byte range — `read_char` rejects
  code points > 255).
- **Strings**: `"…"` with escapes `\n \t \r \\ \" \b \f`.
  Unterminated strings and unknown escapes are reader errors.
- **Symbols**: `name`, `ns/name`, `alias/fn`. Delimiters are
  whitespace, `,`, `()[]{}`, `"`, `;`, `'`, `` ` ``, `~`, `^`, `@`.
- **Keywords**: `:name`, `:ns/name` — self-evaluating; also callable
  as functions (`(:k m)`, `(:k m default)`).
- **Collections**: `( … )` lists (calls and special forms), `[ … ]`
  vectors (literals and binding vectors), `{ … }` maps, `#{ … }` sets.
- **Metadata**: `^T` or `^{…}` attaches a type annotation or option
  map to the following form (`^int x`, `^:implicit`, `^{:sig …}`).
- **Quote** `'form`; **syntax-quote** `` `form `` with `~` unquote
  and `~@` unquote-splicing — read as data, evaluated by the macro
  expander (§5).
- **Comments**: `;` to end of line.
- **Discard** `#_form`: the next form is read and dropped.
- **Reader conditionals** (`.cljc` files only): `#?(:native f :js g
  :default h)` selects the first branch whose keyword matches the
  compile target; `#?@` splices a list/vector branch into the
  enclosing collection. Keys are exactly `:native`, `:js`, and
  `:default` — no others exist.

**Edge behavior.** Reader failures are `E2xx` diagnostics with a
source location (`--> file:line:col`). `fmt` runs the reader in
`preserve` mode which reifies `#_`/`#?`/`#?@` as pseudo-lists headed
by `"#_"`/`"#?"`/`"#?@"` symbols so discarded forms and all
conditional branches survive formatting (see §15 of design.md).

**Anchors**: `test/reader.lg`, the `roundtrip` lane (`lg fmt` over
60+ files — every form must read back identically),
`should_fail/*.err` reader-error classes.

## 2. Modules and namespaces

**File = module.** Every `.lg` (or `.cljc`) file is a module. The
module name derives from the path relative to the include roots
(`util.lg` → OCaml module `Util`); `(ns name …)` is optional and may
carry `:require` clauses — a bare top-level `(:require …)` form is
equally accepted.

**Requires.** `(:require [ns :as alias])` (or without `:as` for
direct references). The compiler resolves them transitively: each
required file is read, expanded, inferred, and emitted as its own
OCaml unit in dependency order. `-I dir` adds include roots. A
reference `alias/f` emits a cross-module call `Alias.f`.
`ocaml.*` requires (OCaml libraries) are covered in §9.

**Export surface.** Top-level defs are public unless a `.lgi`
sidecar limits them: an `.lgi` lists exported names; `(private n)`
hides one explicitly. `lg lgi` regenerates the sidecar while
preserving hand-written entries; `--all` covers the require
closure. `defvariant` ctors listed in a `.lgi` are callable and
`match`-able from consumers (qualified `ns/ctor` patterns).
Macros cannot appear in `.lgi` (expansion needs source).

**`declare`.** `(declare n)` or `(declare ^T n)` — exactly one
symbol — registers a monomorphic forward signature so bodies can
call later-defined globals (mutual recursion). Emit groups
consecutive function tops into `let rec .. and ..` so declared
calls resolve inside the rec group. Declaring a name that is never
forward-referenced can pin an over-specific type — declare only
what is needed.

**Anchors**: `test/lgi.lg`, `test/_lib.lg`/`test/testlib.lg`
(multi-module require chains), `test/mutrec.lg` (declare-driven
mutual recursion), `test/_privdep.lg`+`.lgi` (private surface).

## 3. Special forms

| Form | Shape | Semantics |
|---|---|---|
| `ns` | `(ns name (:require [m :as a]))` | module header, optional (§2) |
| `def` | `(def name expr)` | binds a global; returns the value |
| `defn` | `(defn name [params] body…)` or `(defn name ([x] …) ([x y] …))` | function; multi-arity dispatches on argument count, arities emit as one `let rec .. and ..` group |
| `fn` | `(fn [params] body…)` or `(fn name [params] …)` | lambda; a named fn is self-recursive (`let rec`) |
| `&` rest | `[x y & rest]` in params/binding vectors | extra args collected as a list; a call with exactly the fixed count binds rest to `[]`; `[p… & r]` destructuring binds `r` to `(drop n v)` as `(seq el)` |
| `let` | `(let [b1 e1 b2 e2 …] body…)` | sequential bindings; supports vector/map destructuring (§4) |
| `if` | `(if c t [e])` | missing `else` reads as `()`; `any` conditions use dyn truthiness |
| `do` | `(do e…)` | sequencing; value of last; empty `(do)` is `()` |
| `when` | `(when c e…)` | `(if c (do e…) ())` |
| `and`/`or` | short-circuit | `false` falsy, non-`()` truthy; a literal `()` operand is E101 |
| `cond` | `(cond c1 e1 c2 e2 … (:else en))` | nested `if`; `:else` keyword terminates |
| `try` | `(try body… (catch e h…) (catch (Ctor a…) h…) (finally f…))` | OCaml exceptions; symbol `e` binds an opaque `exn` handle, a `(Ctor a…)` pattern is an OCaml `with` match (non-match re-raises); result = join(body, handler); finally's value is discarded |
| `quote` | `'form` | literal data |
| `syntax-quote` | `` `form `` | template for macros (§5) |
| `match` | `(match s pat1 e1 pat2 e2 …)` | §4 patterns |
| `case` | `(case s lit1 e1 lit2 e2 … default)` | literal dispatch — last clause is the default; literals become `match` patterns |
| `if-let` | `(if-let [b src] then [else])` | `Some` destructuring over `(option t)` |
| `when-let` | `(when-let [b src] e…)` | `if-let` + `do`, else `()` |
| `->`/`->>` | threading | rewrite to nested calls (first/last arg position) |
| `defmacro` | `(defmacro m ([x] …) ([x y] …))` | §5 |
| `defvariant` | `(defvariant name (ctor [f T]…) …)` | §4 |
| `defrecord` | `(defrecord Name [f1 f2])` | map-backed ctor `->Name` + predicate `Name?` |
| `declare` | `(declare ^T? n)` | §2 |
| `extern-type` | `(extern-type n)` | opaque foreign handle type |
| `ffi` | `(ffi n [:argtys] :ret {:native "sym" \| :ocaml "fn" \| :js …})` | §9 |
| atom ops | `(atom v)` `@a` `(deref a)` `(reset! a v)` `(swap! a f)` | `Clj_core.Atom` cells |

**Deliberately absent**: `loop`/`recur` (named `fn` + OCaml TCO
covers it), `set!` (atoms are the only mutable cell),
`throw`/`try` (§13), `defprotocol`/`defmulti` (§13).

**Edge behavior.** `(defn f ([x]…) ([x y]…))` — each arity is an
independent body; a `& rest` clause accepts at least its fixed
count; arities may call each other. `match`/`case` with a missing
catch-all warns (W401/W402). `->`/`->>` desugar at read of the
form — `(-> x (f a) (g b))` is `(g (f x a) b)`.
`(let [x (cond …)])` joins branch types per §4 option rules.
Keyword call `(:k m)` unifies `m` to a keyword-keyed map; the
2-ary form returns `option`, the 3-ary a default value.

**Exceptions.** `(try body… (catch e h…) (finally f…))` compiles to a
real OCaml `try…with` wrapped in `Fun.protect` — exceptions raised
through `ocaml.*` interop (`Not_found`, `Invalid_argument`, …) are
caught exactly like native ones. `e` binds an opaque `exn` handle:
`exn-message : exn -> string` renders it via `Printexc.to_string`,
`(exn s)` constructs `Stdlib.Failure s`, `(throw e)` re-raises a
handle. The try's value joins body and handler per §4 — a
difference is E101; finally always runs and its value is dropped.
A unit branch collapsing to `None` still evaluates its side
effects first (`EDo [branch; None]`). A constructor-pattern
catch `(catch (Ctor a…) h…)` emits an OCaml `with` pattern:
`Failure`/`Invalid_argument`/`Sys_error` args bind `string`,
other ctors' args bind `any`, `_` wildcards allowed, and a
non-matching exception re-raises automatically.
**Anchor**: `test/try.lg` (a real `Not_found` from `ocaml.List`
`List.find`, plus `(catch (Not_found) …)`/`(catch (Failure m) …)`
patterns), `should_fail/try_{join,binder,throw_type,pat}`.

**Anchors**: `test/core.lg`, `test/control.lg`,
`test/loopcase.lg` (case/named fn), `test/destructure.lg`, `test/checkedkeys.lg`,
`test/match.lg`, `test/multiarity.lg`, `test/varargs.lg` (`&`
edges), `test/lispi.lg` (large program exercising all of the
above).

## 4. Type system

**Inference.** Full Hindley–Milner over `defn`/`fn` parameters,
`let` bindings, literals, returns — no annotation is ever
required. `^T` is an assertion: it must agree with inference
(mismatch → E101) but may specialize an otherwise-polymorphic
definition.

**Type grammar** (`^T` positions): `int float bool char string
keyword symbol unit any`, `(vec T) (list T) (seq T) (map K V)
(set T) (atom T) (option T) (tuple T…)`, `(fn [argtys…] ret)`, a
`defvariant`/`extern-type`/`defrecord` name, and type variables —
a bare one-character symbol or a `'`-prefixed symbol (`'a`, `x`).

**Rigid variables.** Type variables in a declared signature are
rigid static types — they must not materialize as dynamic values
for equality, callbacks, zero-arg fns, options, collections, or
host calls.

**The `any`/`dyn` boundary.** `any` enters only via explicit
`^any` and heterogeneous literals (`[1 "two" :three]`). A dyn
value is `Lg_rt.dyn` — a closed variant (`DInt | DVec of dyn vec |
DMap of (dyn,dyn) Map.t | DOpt | DUnit | …`). Unboxing (`EUnbox`)
is emitted only where the static type is known, as a checked
projection — never a blind cast; `Obj.magic` is forbidden
everywhere.

**`seal` (absorbing `any`).** When `any` unifies with a composite
type, every free variable the composite still exposes is bound to
`any` — a dyn value promises nothing, so sibling positions
sharing the variable cannot claim a concrete type. Rigid `^T`
vars are exempt.

**Scheme canonicalization (`canon_free`).** At the `def`/`defn`
boundary the stored scheme is canonicalized: a free type variable
that survives unconstrained *inside a collection argument* is
recorded as `any` (the emitter really does box that position).
Bare variables — the whole result type or a direct fn
domain/codomain — stay quantified. Cross-module call boundaries
convert args/results against the callee's stored scheme.

**Option joins.** `if`/`match` arms unify via `join_branches`:
`unit` against a concrete `t` widens to `(option t)` with
`Some`/`None` emitted per arm; `any` wins and non-`any` arms are
`EBox`-boxed to `dyn`; equal types pass through. `(if c x)` is
`(option <x>)`. There is no `nil` literal: `()` is `unit` and
`None` is the absent option — `(let [x (cond … :else ())])` produces an option the
type checker tracks — `(+ x 1)` on it is a static E101. A `unit`
value is not a condition operand: `(if () …)` is E101; truthiness
is `bool`/`dyn` only.

**`match` patterns.** Literal atoms (int/float/bool/char/string/
keyword/`()`), `_`/symbol (bind), `[p…]` vectors (count-guard +
destructure), `{…}` map patterns, `(Some p)`/`None` on options,
variant ctor patterns `(ctor p…)` and bare 0-field ctors —
including `ns/ctor` qualification. **Edge**: variant pattern
fields are *flat symbols or `_` only* — nested ctor patterns like
`(vcons (vsym p) ps)` are E100; write staged matches. Vector
patterns may end `& r` (§3). Non-exhaustive matches on known
variant/option/bool scrutinees warn W401/W402; missing arms fall
through to a runtime `no_match` failure.

**`defvariant`.** `(defvariant name (c1 [f T] …) (c2) …)` declares
an OCaml variant: fields are `[name type]` pairs, type params
share `ty_of_form` bindings across ctors, and ctors register as
globals (functions, or constants for 0 fields). **Edges**: a
single-character variant name is parsed as a type variable in
field position — name variants ≥2 chars; a variant/type name that
is an OCaml keyword (`val`, `type`, `match`, …) is munged with a
trailing `_` so emitted code parses.

**Tuples.** `(tuple a b …)` builds a `TTuple` value; `nth`
accesses by index. Tuples are **not** destructurable in `let` or
`match` patterns — they are for multi-value returns consumed via
`nth`, or for map entries.

**Implicit params.** `^:implicit`/`^{:implicit T}` trailing params
are resolved by type at call sites and elaborated to ordinary
arguments; `(:require [ns :implicits true])` merges a module's
implicit defs. **Destructure**: `let`/`fn`/`defn` binding
positions accept `[a [b c]]` vectors and `{:keys [..] :strs [..]
:syms [..] :as s :or {..}}`/`{sym :kw}`/`{sym "s"}`/`{:kw bf}` maps;
nested and `any`-valued patterns unbox recursively.

**Result directives.** Beyond `:as` (the raw map), three directives
bind processed views of the map after `:or` defaults are merged in:
`:select s` binds `s` to the sub-map of only the destructured keys
(`select-keys (merge defaults m)`), `:all s` binds `s` to
`(merge defaults m)` (the whole map with defaults filled in),
`:excess s` binds `s` to the map minus every destructured key —
nesting a map pattern under `:excess` merges the inner excess into
the outer one — and `:missing s` collects the keys a `!`-checked
binding failed to find (`soft` semantics: the local binds None, `s`
gains `key → ()`).

**Namespaced keys.** `:ns/keys [a]` / `:ns/strs [s]` / `:ns/syms [s]`
bind `a`/`s` to the qualified key `:ns/a`/`"ns/s"`/`'ns/s`; entry
form `{x :ns/k}` looks up the qualified `:ns/k`.

**Seq coercion.** Destructuring a seq source coerces it to a map:
`(k v k v…)` pairs, empty → `{}`, a single map element → that map —
a non-pair seq is a type error.

**`:or` + `!`.** Supplying a default for a required key is a compile
error `Can't supply default value for required key: :k` — the
default could never hide a missing required key.

**Checked keys.** The `!` variants `:keys!`/`:strs!`/`:syms!` make a
missing key an error instead of an option: when the source map is a
literal with a known keyset a miss is a compile-time E101 with a
did-you-mean suggestion; over opaque/`any` maps each key emits a
runtime check that raises `missing key :k` (a `Failure` exn, catchable
via `try`/`catch`). The same three levels exist
outside destructuring: `get` returns `(option v)`, `req!` returns the
bare `v` or raises, and `!` destructuring checks. `{:req! [[pat :k]
…]}` applies required-check semantics to entry-style bindings. `&`
may appear once in a `:keys`-style list; keys after it are doc-only —
they bind nothing but are verified the same way (static miss → E101,
opaque map → runtime raise). `&` is never a valid binding name (E100),
and a binding symbol after `&` is an error.

**Anchors**: `test/polydyn.lg`, `test/dyn.lg`,
`test/collmatrix.lg` (builtin×coll-kind matrix incl. `any`
edges), `test/dynmatch.lg` (dyn-arm join coercion),
`test/destructure.lg`, `test/checkedkeys.lg`, `test/implicit.lg`,
`test/sigimplicit.lg`, `test/keywords.lg` (keyword identifiers),
`should_fail/cm_*.err` (static rejections), `should_fail/marity.lg`, `should_fail/ckeys_*.err`, `should_fail/amp_*.err`.

## 5. Macros and compile-time evaluation

`defmacro` defines a compile-time function over *raw forms*,
evaluated by a form-level evaluator inside the compiler.
Expansion happens per-module, after reading and before inference;
a dynamically-bound "current macro module" (like Clojure's `*ns*`)
threads through nested expansions.

- **`syntax-quote`** templates evaluate `~`/`~@` exactly as in
  Clojure.
- **Hygiene is automatic**: macro-introduced `let`/`fn` bindings
  cannot capture user variables — a mark table renames them
  `__hN` per expansion site before typechecking.
- **Reference boundary**: every mark records the macro's defining
  module. An unqualified symbol inside a `` ` `` template resolves
  in the macro's module first, then the caller's — call-site names
  can never hijack a macro's internal references. Conversely an
  unmarked (user-written) name resolves only in the module that
  wrote it — macro calls are module-scoped, no shared fallback.
- **`gensym`** produces a guaranteed-fresh name in macro output.
- **Multi-arity** `(defmacro m ([x]…) ([x y]…))` selects the
  clause whose arity accepts the call's count — independent
  bodies, `& rest` accepts at least its fixed count, a clause may
  expand into the same macro at another arity, and an unprovided
  arity is a compile error (E-class, see `should_fail/marity.lg`).

**Anchors**: `test/macros.lg` (multi-arity + dispatch),
`test/hyg.lg` + `test/_hyglib.lg` (hygiene + module boundary),
`test/lispi.lg` is macro-free on purpose — it is the language's
own dogfood.

## 6. Standard library

Builtins are grouped by domain; names and argument order follow
`clojure.core` unless noted.

**Builtin namespaces.** Like Clojure, string/io/set helpers live in
builtin namespaces — `lg.str`, `lg.io`, `lg.set` — reached only via
`(:require [lg.str :as str] [lg.io :as io] [lg.set :as set])` (no `-I`
needed; they are virtual modules, `lg.*` is reserved). Qualified
calls are `str/join`, `io/slurp`, `set/union`; the fully-qualified
`lg.str/join` also resolves without a require. The bare names are
not in scope — `(join …)` is E102 with a `did you mean` hint.

- **Arithmetic/comparison**: `+ - * / mod` (int), `+. -. *. /.`
  (float), `inc dec abs min max`, `= < <= > >=` — `=`/`not=` are
  *structural* and dispatch on the operand's static type
  (`Clj_core.Vec.equal`/`Map.equal`/`Set.equal`, `dyn_eq` for
  `dyn`, `=` for scalars).
- **Predicates**: tag predicates `int? float? bool? char? string?
  keyword? symbol? number? coll? unit? some? none? fn? map? vec?
  list? set? seq?` dispatch on the `dyn` tag for `any` scrutinees
  and constant-fold statically (`fn?` is always `false` —
  functions are never boxed). Numeric `zero? pos? neg? even? odd?`
  unbox `any` via `as_int`/`as_float`.
- **Collections**: `count nth first rest next second nthrest conj
  cons assoc dissoc get req! get-in keys vals select-keys merge update
  update-in assoc-in contains? empty? seq vec list set zipmap
  into` — see the dispatch matrix below and `test/parity.lg` for
  Clojure-parity edge rules (`get-in` 2-ary `None` on missing
  path, 3-ary default; `update-in` 3-ary on missing key *fails
  loudly* — no nil-equivalent exists to feed the callback; `(update m k f
  d)` inserts `d`; `nth` 2-ary raises out-of-bounds, 3-ary
  default; `assoc-in` creates intermediates persistently).
- **Seq API (lazy, §8)**: `map filter filterv mapv map-indexed
  mapcat remove keep filter-map reduce reductions fold take drop
  take-while drop-while take-nth take-last drop-last last butlast
  split-at split-with range repeat repeatedly iterate cycle
  interleave interpose concat reverse sort sort-by group-by
  frequencies partition partition-all distinct dedupe into doall
  dorun lazy-seq some every? juxt comp partial identity
  constantly apply`.
- **lg.str** (`str/…`): `subs split join trim triml trimr
  upper-case lower-case blank? includes? starts-with? ends-with?
  replace` + regex-lite `re-find re-matches re-seq re-split
  re-replace` (pattern first, subject second). `subs` is 2- or
  3-ary; `join` is `(str/join coll)` or `(str/join sep coll)`.
- **lg.io** (`io/…`): `slurp spit read-line argv env file-exists?
  sh now-ms` — sh/read-line/now-ms are native-only.
- **lg.set** (`set/…`): `union intersection difference subset?
  superset? select` — clojure.set semantics.
- **Atoms**: `atom deref @ reset! swap!`.
- **Misc**: `tuple`, `int`/`float`/`str`/`name` coercions,
  `println print pr-str`, `exit`, `gensym` (macro context).
- **Exceptions**: `exn` (opaque handle type), `(exn s)`,
  `throw`, `exn-message` — see §3.
- **Dispatch matrix.** The builtin × collection-kind table — which
  `(builtin, {vec,list,seq,map,set,any})` cells are allowed, and
  which are static errors — is generated from
  `test/gen_collmatrix.py` into `test/collmatrix.lg` (67 allowed
  golden cells) plus 29 `should_fail/cm_*` negative lanes.
  Normative asymmetry: the 12 core coll builtins reject `any`
  statically, while `update`/`merge`/`select-keys` accept `any`
  and dispatch on the runtime tag.
- **Libraries**: `lib/test.lg` (`deftest is testing are
  run-tests`), `lib/qc.lg` (property-based testing with
  deterministic LCG seeds + shrinking).

**Anchors**: `test/builtins.lg`, `test/seqs.lg`,
`test/lazyseq.lg`, `test/strings.lg`, `test/atoms.lg`,
`test/iolib.lg`, `test/parity.lg`, `test/hof.lg`,
`test/collmatrix.lg`, `test/qclib.lg`, `test/testlib.lg`.

## 7. Memory model and modes

Three inferred modes — never annotated:

| Mode | Meaning | ocaml backend | OxCaml backend |
|------|---------|------------|----------------|
| `Local` | value does not escape its region | comment + report | real `@ local` params, `local_` binders, `stack_` allocations |
| `Owned` | uniquely referenced | comment + report | comment only — `unique_` has no expression syntax in OxCaml 5.4 |
| `Shared` | everything else | ordinary GC heap | ordinary GC heap |

Rules: `Shared` if returned from a public `defn`, stored in an
atom or escaping collection, captured by an escaping closure, or
passed across a module boundary; `Local` if consumed entirely
inside its lexical scope; `Owned` otherwise with a single
threaded reference. Inference is intra-file; cross-module calls
conservatively assume escape. In doubt → `Shared`
(sound-by-construction).

`lg modes <file>` prints every binding's mode + reason; on
vanilla OCaml the same lands as `(* mode: … *)` comments.

**FBIP.** Provably single-use collection literals (unique-owner
chains of `conj/assoc/dissoc/pop/update/into/disj`) emit `Lg_rt`
growable builders + one freeze. A self-recursive `(fn go [i acc]
…)` whose coll param is only ever the root of an update chain or
a bare result also runs as a mutable builder — requires a fully
concrete coll type and no escapes. ~2.2x measured on a 5M `conj`
loop.

**Anchors**: `test/oxlocal.lg` (tier-2/3 mode chain),
`test/fbip.lg` + `snapshot-fbip` (builder emit), `lg modes`
lanes in `test.sh`.

## 8. Evaluation and runtime semantics

- **Strict evaluation everywhere except lazy seqs.** Sequence
  producers (`map`/`filter`/`take`/`rest`/`range`/`iterate` …)
  return `(seq T)` = `'a Clj_core.Seq.t` and transform lazily;
  realization happens at `vec`/`set`/`into`/`doall`/`dorun`/
  `count`/`reduce`/`first`/`next`/`rest`/`nth`/`str`/`println`.
  `cons` accepts any collection and returns `seq`; `(seq c)` is
  `(option (seq t))` — `None` on empty, matching Clojure.
- **`seq` is the universal collection interface.** `TSeq`
  unifies with `TList`/`TVec`/`TSet`/`TMap` in both directions;
  the emitter realizes the conversion (`Seq.of_vec`/`of_list`/
  `of_set`/`of_map`, `Seq.to_list` + re-collection) element-wise
  when element types also cross a boundary.
- **Runtime contracts fail loudly.** Checked `^T` unboxes, a
  missing-key 3-ary `update-in`, `contains?` on a non-coll, and
  `no_match` fallthroughs raise OCaml exceptions — catchable via
  `try` (§3) but treated as bugs, not control flow.
- **Atoms** are `Clj_core.Atom` cells (`deref`/`reset!`/`swap!`).
- **Printing**: `str`/`println`/`pr-str` render per static type —
  dyn values render via their runtime tag (`DVec` → `(1 2)`,
  `DMap` → `{:k v}`); fns print as `#<closure>`.
- **Heterogeneous literals** box element-wise into `dyn`
  collections; `DMap` payloads are flat `(dyn,dyn)` maps
  everywhere except the `get-in`/`assoc-in`/`update-in`/
  `select-keys` family which converts at clj-core's nested-map
  boundary.

**Anchors**: `test/lazyseq.lg`, `test/seqs.lg`, `test/atoms.lg`,
`test/dyn.lg`, `test/lispi.lg` (a full evaluator written in lg —
its own runtime semantics ride on these rules).

## 9. Interoperability

**`ocaml.*` requires** (native + oxcaml backends only — melange/
wasm reject them with E100): `src/ocaml_sig.ml` reads installed
`.cmi` files so any OCaml module or findlib package is callable.

- `[ocaml.Mod :as m]` / `[ocaml.Mod.Sub :as m]` — `m/f` calls
  emit `Mod.f`/`Mod.Sub.f`.
- `[ocaml.Mod :refer [f g]]` — imports bare `f`, `g`.
- `[ocaml.pkg/name]` — package registration only: `ocamlfind
  query` the package for cmi dirs and add it to `-package
  -linkpkg`. A module require that resolves through a package
  adds that package automatically.
- **Calls**: `lookup` returns `(params, labels, result, is_ctor)`;
  trailing `:kw v` pairs match `OLbl`/`OOpt` params by name —
  unknown/duplicate labels and missing `~lbl`s are E100/E102.
  A curried arrow chain flattens into one multi-param `TFun`, so
  `(fn [k v acc] ...)` feeds OCaml's `'a -> 'b -> 'acc -> 'acc`
  higher-order params (`Hashtbl.fold` and friends); a 1-ary lg
  function is still required where the callee takes one arg.
  Optional params `?x:T` are *omittable by-value* arguments —
  identical to `~x`: omitting uses the OCaml-side default, and a
  supplied `:x v` emits `~x:v` with `v` unwrapped (the cmi stores
  `T option`; the option is stripped in the shared `decompose`,
  so `?` and `~` behave the same on both toolchains). Positional
  args arity-check; a trailing `unit` param synthesizes `()`;
  under-application returns the remaining `TFun`. Constructors
  emit `Mod.Ctor` calls with exact field count.
- **Types**: `ty_of_te` maps cmi `type_expr`s onto lg types.
  A constructor path whose declaration carries a *transparent
  manifest* (`type t = string`, `type 'a t = 'a list`) expands
  through its own cmi — OxCaml cmis spell `string` as
  `Stdlib__String.t` where upstream writes the primitive —
  with the declaration's `type_params` instantiated by the
  constructor args, bounded at depth 8. Names inside the
  manifest bind against the manifest's *own* unit, so
  `type 'a t = 'a inner` expands `inner` under its home
  module. A relative dotted path (`Net.t` inside `Eio.Stdenv`)
  resolves parent-scope-first (`Eio.Net.t`), then absolute.
  Abstract types name themselves by the resolved canonical
  unit rather than the textual alias, keeping
  `Eio__core__Switch.t`/`Eio__Std.Switch.t` spellings on one
  type. `exn` maps to the opaque `exn` handle type (not
  `string`) — the same handle `try`/`throw`/`exn-message` use. The builtin table binds on the exact primitive path
  (`list`/`Stdlib.list`): `list`→`TList` and `option`→`TOption`
  are the only mapped containers — `result`, `array`, `ref`,
  `bytes` import as opaque named handles (`Stdlib.result`, …),
  never silently as option/list/atom/string, because emitted code
  must stay type-correct (a `Result.map` cannot see an option).
  Cross the boundary explicitly (`Option.to_result`,
  `Result.to_option`, `Array.of_list`, `Bytes.to_string`).
- **Record labels** are projections, not values: after the
  `Sig_value`/ctor lookup misses, `(x/lbl r)` resolves `lbl` against
  the module's `Type_record` declarations and emits `r.lbl` (never
  `Mod.lbl r`). Applied once it projects the field; unapplied it is a
  first-class fn `(fun r -> r.lbl)`. The record type unifies with the
  argument (`(std/contents 99)` → E101). Mutation (`r.lbl <- v`) is
  not surfaced — OCaml records are conventionally immutable.
  **Anchor**: `test/ocamlinterop.lg` (`std/contents` applied,
  fn-valued, and through `List.map`), `should_fail/ocaml_lbl`.
  Handle params are not boxed on import: `(def h (ht/create 8))`
  stores the generic `('a,'b) Hashtbl.t` scheme, and OCaml
  weak-var inference pins one instantiation per use — a def that
  is never used concretely (or only used generically) fails at
  emit with OCaml's non-generalizable-variable diagnostic.
  Constructor *arguments* whose forms lg cannot
  express — polymorphic-variant rows, objects, univars,
  first-class packages, row fields — become fresh type vars
  inside the enclosing `Tconstr`, so eio's
  `[> 'tag ty] r`/`[< 'tag] connection_handler` row bounds
  import as open handles. Unresolved or inexpressible
  *top-level* manifests become opaque `TCon` handles qualified
  by owning unit (dune-wrapped spellings canonicalize to the
  flat unit). The compiler-libs ABI surface (`Cmi_format`,
  `Types`, arg labels, constructor payloads) is normalized by
  `src/osig_shim*.ml` — dune selects the upstream or OxCaml
  implementation by `%{ocaml_version}`, so `dune build` works
  under either switch and an ox-built lg reads ox cmis
  natively. cmi files remain toolchain-bound — a `.cmi` from
  a different OCaml toolchain is reported as such, not
  misparsed.
- **Mode analysis** treats every `EOCamlCall` argument as
  escaping (cmi carries no borrow metadata).

**`ffi`**: `(ffi name [:argtys…] :rettype {:select value})` binds
a foreign symbol. Selects: `:native` resolves a C symbol via
ctypes in the process image; `:ocaml` emits a typed `external`;
`:js` (melange only). `(extern-type n)` declares the opaque
handle type for `rettype`/arg positions.

**`.cljc`**: reader conditionals `#?`/`:native`/`:js`/`:default`
(§1) select code per backend at read time.

**Anchors**: `test/ocamlinterop.lg`, `test/ffi.lg`,
`test/ffimod.lg`, `test/_ffilib.lg`, `examples/eiodemo.lg`
(eio + fiber + socket via `ocaml.*`), `examples/eioecho.lg`
(self-terminating TCP echo: `Net.listen`/`accept_fork` +
`Fiber.fork` client + `Flow.single_read` + `Cstruct`),
`test/melio.lg` (melange io).

## 10. Compilation, performance, and incremental semantics

**Pipeline**: reader → syntax → types → macro expansion →
inference → mode inference → emit → OCaml compile/link.

**Commands**: `lg check` (front half only: read→expand→infer→
modes), `lg emit` (one self-contained `.ml`: header + `Lg_rt`
prelude + one OCaml `module X` per lg module), `lg build`
(emits then compiles; default `ocamlopt` native, `--byte` for
`ocamlc` bytecode — ~3x faster cold, ~5x faster relink, runtime
3–10x slower; dev-loop tool), `lg modes` (mode report),
`lg fmt` (canonical layout), `lg repl` (per-line rebuild, ~1s),
`lg lsp`, `lg deps`/`init`/`doc`/`lgi`/`version`. Flags: `-I dir`
include roots, `-o` output (`lg build -o` requires the output
*directory* to exist), `--strict`, `--backend {ocaml|oxcaml|
melange|wasm}`, `-j N` (parallel unit compilation, topological
layers; default 4).

**Incremental compilation** (design.md §18): `<exe-dir>/.lg-obj`
holds one OCaml unit per lg module plus `Lg_rt`. A unit's stamp
records `Digest(emitted source + direct dep hashes)` — content
only; mtimes and comment-only edits never force rebuilds.
Rebuilding module M restamps M and recompiles M's downstream on
the next build. Stamps are per (unit, toolchain):
`*.ocamlc.stamp`/`*.ocamlopt.stamp` so `--byte` and native never
mask each other's staleness.

**Measured** (macOS arm64, OCaml 5.5.0, this repo's `test.sh`
bench lane — asserted every run with env-tunable bounds
`LG_BENCH_*_MS`): lg frontend <10ms per module; single-module
cold native build ~250–310ms (ocamlopt dominates ~95%); warm
relink ~120–140ms; `--byte` cold ~90ms, warm ~20ms; `Lg_rt`
compiles once per object directory (~60–80ms) and is shared.

**Emitted-file mapping** (design.md §7): collections →
`Clj_core.Vec/Map/Set/List/Seq`, atoms → `Clj_core.Atom`,
keywords → `Clj_core.Keyword.keyword`, locals `__N`-renamed
(macro-introduced `__hN`), `alias/f` → `Alias.f`, heterogeneous
literals → `Lg_rt.dyn` boxes.

**Anchors**: `test.sh` bench lane, `test/oxcaml_smoke.sh`
(28+ cases end-to-end on real OxCaml), emit snapshots
`test/*.emit.ml`.

## 11. Diagnostics

`src/err.ml` renders Elm-style blocks: `error[Ecode]` +
`--> file:line:col` + source line + caret span + `=` hints.

- `E1xx` inference: E100 (malformed/unsupported form),
  E101 (type mismatch via `Typ.unify`), E102 (unresolved symbol —
  Levenshtein "did you mean" over env+globals+builtins).
- `E2xx` reader: unterminated collections/strings, bad chars,
  stray delimiters.
- `E3xx` misc (macro-expansion and higher errors).
- Warnings: W401 (non-exhaustive variant match), W402 (partial
  option/bool match).
- `--strict` additionally requires `^any`-family annotations on
  heterogeneous literals (every `any` must be author-written).
- The `should_fail/` contract pins negative behavior: each
  `<name>.lg` must fail its class, `<name>.err` records the
  expected diagnostic — CI checks the error *class* and line.

**Anchors**: `should_fail/*.lg`+`.err`, `test.sh` `ERE` lanes.

## 12. Portability and backends

- **native** (default): `ocamlopt` (`--byte` for `ocamlc`).
- **oxcaml**: `--backend=oxcaml` emits `local_`/`stack_`/
  `@ local` annotations verified against a real
  `ocaml-variants.5.4.0+ox` switch (`test/oxcaml_smoke.sh` — all
  smoke lanes run emitted binaries). Tier 1 `@ local` params on
  borrow-safe positions; tier 2 `local_` binders + `*_local`
  clj-core variants; tier 3 `stack_` on direct allocation sites.
  Measured (design.md §10): −31% minor words, −83% minor
  collections on the literal-heavy path; wall time flat.
- **melange** (`--backend=melange`): single merged `.ml` →
  `melange.emit` workspace → `.js` run under node. `ocaml.*`
  requires are rejected (E100); `io`/system fns use lazy
  `[%mel.raw]` Node probes — browser-safe at load.
- **wasm** (`--backend=wasm`): `ocamlc` bytecode →
  `wasm_of_ocaml compile` → `<exe>.js` + `<exe>.assets/`.
  `env`/`file-exists?` work; `now-ms`/`argv` degraded.
- **`.cljc` files** share source across backends via reader
  conditionals (§1).

**Anchors**: `test/oxcaml_smoke.sh`, `test/oxcaml.lg`,
`test/oxlocal.lg`, `test/melio.lg`, melange/wasm lanes in
`test.sh`.

## 13. Not part of v1

Explicit exclusions — each is a documented design position
(design.md §9), not an oversight:

- **No concurrency model** — no fibers/threads/parallel
  collections in the language (eio is reachable via `ocaml.*`
  interop for programs that need it, e.g.
  `examples/eiodemo.lg`).
- **`try` exists but exn-pattern matching is deferred** —
  `(catch e …)` binds the whole `exn` handle only; discriminating
  on the constructor (`(catch (Not_found) h)`) is a v0.2 item.
  Typed error channels (`option`, Result-style data) stay the
  default; `try` is for real exceptional paths including
  `ocaml.*` raises.
- **No `defprotocol`/`defmulti`** — static polymorphism via
  OCaml modules/functors (interop) and implicit parameters;
  open dispatch via `match` dyn-tag arms.
- **No arbitrary-precision numerics** — `int` is machine int,
  `float` is IEEE double.
- **No `loop`/`recur`, `set!`** — named `fn` + native TCO, and
  atoms as the sole mutable cell (§3).
- **No `nil`** — a deliberate deviation from Clojure: `()` is
  `unit` (printed `()`), `None`/`option` covers absent values, and
  an empty collection is `[]`/`(list)`. `nil` is a
  reader error (E201) with the replacement hint; `nil?` is renamed to
  `unit?`; `none?` stays. A `()` value in `if`/`and`/`or` position
  is a static E101 — unit is not a truthiness operand.
- **Nominal `TCon` record types** are deferred — `defrecord`
  stays map-backed.
- **`unique_` lowering** is deferred — no expression syntax in
  OxCaml 5.4.
