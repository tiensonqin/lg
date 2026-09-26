# LG inference redesign: constraint-based HM-style inference

Status: design proposal. Companion to `report.md` (current-state findings).

## Goals

Make LG an agent-first language: idiomatic code compiles without type
annotations, inference is order-independent and terminating, compile latency is
low enough to keep the authoring loop interactive, and generated OCaml does not
inflate through per-use-site artifacts.

## Non-goals

- Changing source syntax or the public surface of the runtime.
- Removing the witness-pair ABI or the `Semantic_ir` → `Ocaml_ir` lowering
  pipeline in the first pass.
- Type classes / ad-hoc overloading as a language feature (capabilities stay
  compiler-internal evidence, not user-facing polymorphism).

## Background: how OCaml does it

OCaml's checker (typing/ctype.ml) is not textbook Algorithm W; the relevant
ideas to adopt:

1. **Metavariables are mutable.** A `Tvar` carries a mutable binding cell;
   unification links in O(1) and `repr` follows links with path halving.
   There is no substitution map being applied to whole trees.
2. **Levels drive generalization.** Each type node has a level; entering a
   `let`/`fun` raises the current level. Generalization quantifies variables
   whose level exceeds the binding level — no environment scan, no
   name-generation, correct by construction.
3. **Unification never invents structure**; conflicts are errors at the point
   of unification, not deferred to a backend.
4. **Ambiguity is resolved at scope boundaries**, not mid-expression: variables
   that escape generalization are either generalized (let-bound lambdas,
   subject to the value restriction) or reported once with a precise span.
5. **Deferred/ambiguous machinery** exists for non-principal features (GADTs,
   polymorphic variants, `wrap_partial_apply`). The equivalent in LG is the
   capability constraints: they are deferred requirements discharged at
   generalization, which is where today's `(xs__seq, xs)` witness pairs come
   from — that mechanism stays, only its *construction* changes.

## Target architecture

```text
Ast.form
  -> constraint-generating traversal (once per form, order-free)
       every expression node gets a fresh meta;
       uses emit equations (t1 = t2) and requirements (seqable t, ...)
  -> solver (union-find + levels)
       term equations unify destructively;
       capability requirements accumulate on the metvar
  -> boundary resolution (let / fn / loop / defn)
       generalize by level + value restriction;
       surviving requirements become witness parameters (today's ABI);
       genuinely ambiguous metas are errors *at the binding site*
  -> Semantic_ir (same as today)
```

### What changes concretely

- `Type_solver`: substitution map → union-find over `TMeta` with levels.
  `unify` stops threading `substitutions`; `bind` is O(1). `TVar` (declared,
  rigid) is excluded from binding — structural, not conventional.
- `TUnknown` is split: `TMeta` (unknown, will be solved) vs. error on
  "unifies with everything".
- Capability constraints stay encoded as `TConstraint`/`TOcaml_app` spellings
  in `ty` *for now* (lowering consumes them), but they are produced by
  constraint solving, not by pairwise `refine_type` merges.
- `refine_type` is deleted. Where two candidate types meet, the outcome is
  `unify` or a deterministic lattice join with a total order — never
  "prefer the left".
- `infer_params` is a single constraint-collection pass; the internal
  `stabilize` re-walk loop and the outer 16-pass `stabilize_typecheck` go away.
- Anonymous structural rows become a hash-consed open row type keyed by
  (sorted) field set; identical shapes share one type identity instead of a
  fresh nominal `..._rowN` per use site.
- Unconstrained collection parameters are deferred constraints (e.g.
  `map<K,V>` evidence), never `Runtime_dynamic.get` fallbacks.

## Acceptance criteria

Benchmarks and the eval harness live in `test/inference_eval/`.

| # | Criterion | Baseline (a784f453) | Target |
|---|---|---|---|
| A1 | Hint-free compile rate on the idiomatic-snippet corpus (`test/inference_eval/snippets`, currently 50 forms) | 38/50 = 76% | ≥ 98% (49/50; `apply` on an unannotated higher-order param may legitimately still demand a signature) |
| A2 | No internal names in diagnostics (`param/gN`, `__lg_*`, `TMeta` ids) | leaks in ≥ 4 messages | 0 occurrences |
| A3 | Single-pass elaboration: `LG_COMPILE_TIMINGS=1` shows exactly one stabilization pass for every file; no `typecheck stabilization pass 2+` | multi-pass on recursive/changed declarations | pass 1 only; `did not stabilize` unreachable |
| A4 | stdlib full compile (22 files, 14k lines) wall time | ~2.5 s warm | ≤ 1.0 s |
| A5 | Small-file chunk compile, cold | ~0.55 s | ≤ 0.3 s |
| A6 | Write amplification: generated `.ml` lines ÷ source `.cljc` lines, per-chunk mode, prelude excluded | ~3.7× on t3 sample (45/12) | ≤ 2.0× |
| A7 | Zero anonymous record types emitted for pure keyword reads on structural values | 3 types per 12-line file | 0 (structural rows deduped/shared or eliminated) |
| A8 | Full gate green: `dune build @runtest` + `@test/clojure_suite/clojure-test-suite-smoke` + footprint gates | green at base | green |
| A9 | chat@f83c217 corpus (111 files / 35k lines) compiles with type annotations stripped | unknown (needs baseline) | ≥ 90% of files compile with all `^:` param annotations removed |
| A10 | No `Runtime_dynamic.get`/pack fallbacks emitted for statically solvable values | `get-in` on plain param emits `Runtime_dynamic.get` | 0 in eval corpus |

## Eval harness

`test/inference_eval/run.sh`:

- compiles each snippet with `--compile-files-chunk-from stdlib.state`,
- classifies each failure (missing hint, internal-name leak, LG4000 leak,
  dynamic fallback, genuine type error),
- reports pass rate, per-file .ml line counts, and wall time;
- writes `baseline.json` vs current `results.json` for diff review.

A stripped-hint corpus variant of the lg-era chat sources (chat@f83c217,
111 `.cljc` files) is produced mechanically: remove `^:` type metadata from
defn/let/fn params while keeping `:private`/`:dynamic` flags. Success = file
compiles to OCaml without new errors vs. the annotated baseline.

## Migration plan (each step lands green behind the full test suite)

1. **Eval harness + report** (this PR): corpus, baseline metrics, no compiler
   changes yet.
2. **Solver core**: union-find metavars + levels inside `Type_solver`,
   keeping the `substitutions` API as a façade (empty map token) so callers
   migrate incrementally. Rigid `TVar` binding becomes a type error.
3. **Demand-driven constraints**: when a call/builtin observes an unresolved
   meta, install the callee's requirement as a pending constraint on the meta
   instead of erroring (fixes concat/select-keys/comp class).
4. **Deterministic merge**: replace `refine_type` arbitrary picks with unify
   or explicit join; conflicts become located errors.
5. **One-pass elaboration**: remove `infer_params` re-walk and
   `stabilize_typecheck` outer loop; recursive groups get HM-style
   "bind scheme at group boundary" handling.
6. **Codegen**: hash-consed structural rows; drop per-site `*_rowN` records;
   suppress redundant casts and identity wrappers in emitted OCaml.
7. **Diagnostics**: errors render source spans + user-facing type names only.

## Risks

- Step 2 changes sharing/mutation assumptions across every `ty` consumer;
  mitigate by keeping `apply`-style resolution read-only at boundaries.
- `call_elaborator.ml` (23.8k lines) consumes constraint-encoded `ty`s
  everywhere; steps 3–4 must keep that encoding shape until lowering is
  updated.
- Recursive/overloaded ABI (`row_param_types`, `overload_targets`,
  `return_param_index`) is serialized into saved state — the state format
  bumps; old `.lg-cache` invalidates.
- `defrecord` polymorphism (fields inferred per use site today) interacts with
  structural rows; keep `defrecord` nominal, only anonymous rows change.
