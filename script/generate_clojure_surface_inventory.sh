#!/bin/sh
set -eu

if test "$#" -lt 1 || test "$#" -gt 3; then
  echo "usage: $0 LG_ROOT [LOGSEQ_ROOT] [CLOJURESCRIPT_ROOT]" >&2
  exit 2
fi

lg_root=$(CDPATH= cd -- "$1" && pwd)
logseq_root=${2-}
if test -n "$logseq_root"; then
  logseq_root=$(CDPATH= cd -- "$logseq_root" && pwd)
fi
clojurescript_root=${3-}
if test -n "$clojurescript_root"; then
  clojurescript_root=$(CDPATH= cd -- "$clojurescript_root" && pwd)
fi
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

call_elaborator="$lg_root/src/call_elaborator.ml"
expression_elaborator="$lg_root/src/expression_elaborator.ml"
type_inference="$lg_root/src/type_inference.ml"
core_namespaces="$lg_root/src/core_namespaces.ml"

if ! test -f "$call_elaborator" \
  || ! test -f "$expression_elaborator" \
  || ! test -f "$type_inference" \
  || ! test -f "$core_namespaces"; then
  echo "LG_ROOT must contain the compiler elaborators and src/core_namespaces.ml" >&2
  exit 2
fi

upstream_commit=$(sed -n 's/.*:commit "\([0-9a-f][0-9a-f]*\)".*/\1/p' \
  "$lg_root/stdlib/upstream.edn" | head -1)
printf 'meta\tclojurescript-commit\t%s\n' "$upstream_commit"

if test -n "$clojurescript_root"; then
  checkout_commit=$(git -C "$clojurescript_root" rev-parse HEAD)
  printf 'meta\tclojurescript-checkout-commit\t%s\n' "$checkout_commit"
  if test "$checkout_commit" != "$upstream_commit"; then
    echo "ClojureScript checkout does not match stdlib/upstream.edn: expected $upstream_commit, found $checkout_commit" >&2
    exit 1
  fi
fi

# Parse the OCaml AST and select the largest `match name with` expression. This
# avoids treating string patterns from nested type/argument matches as public
# compiler dispatch names.
ocaml -I +compiler-libs ocamlcommon.cma \
  "$lg_root/script/extract_ocaml_string_dispatch.ml" "$call_elaborator" \
  >"$tmp/compiler-calls"

dispatch_count=$(wc -l <"$tmp/compiler-calls" | tr -d ' ')
if test "$dispatch_count" -ne 263; then
  echo "compiler call dispatch changed: expected 263 names, found $dispatch_count" >&2
  echo "review and classify every added or removed name before updating the count" >&2
  exit 1
fi

awk '
  BEGIN {
    split("binding with-open with-out-str reify assert delay set! throw instance? satisfies?", xs)
    for (i in xs) special[xs[i]] = 1
    special_reason["instance?"] = "compiler-owned-static-type-or-protocol-witness-elaboration"
    special_reason["satisfies?"] = "compiler-owned-static-type-or-protocol-witness-elaboration"
    split("assoc-in doall drop filter get-in keep map map-indexed mapcat max merge min next rand repeatedly rest select-keys some take update-in vals", xs)
    for (i in xs) blocked[xs[i]] = 1
    split("assoc-in get-in update-in", xs)
    for (i in xs) blocked_reason[xs[i]] = "nested-map-paths-require-dependent-key-and-value-types"
    split("map", xs)
    for (i in xs) blocked_reason[xs[i]] = "variadic-multi-collection-arities-and-lazy-or-transducer-cases-are-not-source-expressible"
    split("drop filter keep map-indexed mapcat repeatedly take", xs)
    for (i in xs) blocked_reason[xs[i]] = "upstream-lazy-sequence-or-transducer-behavior-is-not-source-expressible"
    split("doall", xs)
    for (i in xs) blocked_reason[xs[i]] = "sequence-realization-and-effect-order-remain-a-compiler-runtime-boundary"
    split("max min", xs)
    for (i in xs) blocked_reason[xs[i]] = "variadic-comparable-types-and-key-callback-overloads-are-not-source-expressible"
    blocked_reason["merge"] = "variadic-map-and-record-shape-unification-is-not-source-expressible"
    blocked_reason["rand"] = "same-arity-int-and-float-bound-overloads-cannot-share-one-source-function-type"
    split("next rest", xs)
    for (i in xs) blocked_reason[xs[i]] = "nil-versus-empty-sequence-semantics-remain-a-collection-capability-boundary"
    blocked_reason["select-keys"] = "map-or-record-key-projection-requires-a-dependent-result-shape"
    blocked_reason["some"] = "nullable-first-truthy-result-needs-a-generic-witness-through-the-sequence-loop"
    blocked_reason["vals"] = "map-and-structural-record-value-projection-needs-a-closed-value-sum"
    split("clj->js current-time-millis enable-console-print! ex-info future-call pr-sequential-writer pr-str pr-writer print println prn raise requiring-resolve resolve uuid weak-clear! weak-deref weak-ref", xs)
    for (i in xs) host[xs[i]] = 1
    split("inc dec __lg_int __lg_long __lg_double quot rem mod bit-and bit-or bit-xor bit-not bit-shift-left bit-shift-right", xs)
    for (i in xs) primitive[xs[i]] = 1
    split("__lg_nullable-value __lg_symbol-value __lg_keyword-value __lg_int-value __lg_string-value __lg_number-value __lg_fn-value __lg_instance-value __lg_not-symbol-value __lg_not-keyword-value __lg_not-string-value __lg_not-int-value __lg_not-fn-value __lg_not-instance-value", xs)
    for (i in xs) narrowing[xs[i]] = 1
    internal_abi["__lg_ex-message"] = "static-exception-message-extraction-primitive"
    internal_abi["__lg_format"] = "closed-static-format-argument-domain"
    internal_abi["__lg_flush_output"] = "typed-output-flush-primitive"
    internal_abi["__lg_not"] = "typed-static-truthiness-negation-primitive"
    internal_abi["__lg_ex-cause"] = "static-optional-exception-cause-primitive"
    internal_abi["__lg_ex-data"] = "documented-exception-info-data-dynamic-boundary"
    internal_abi["__lg_re-pattern"] = "validated-static-regex-construction-primitive"
    internal_abi["__lg_re-matcher"] = "documented-stateful-regex-matcher-host-boundary-with-static-matcher-type"
    internal_abi["__lg_re-find"] = "documented-regex-match-dynamic-boundary-with-static-optional-result-specialization"
    internal_abi["__lg_re-matches"] = "documented-regex-match-dynamic-boundary-with-static-optional-result-specialization"
    internal_abi["__lg_re-seq"] = "documented-regex-sequence-dynamic-boundary-with-clojurescript-match-shape"
    internal_abi["__lg_exec-tap-fn"] = "documented-tap-executor-callback-dynamic-boundary"
    internal_abi["__lg_add-tap"] = "documented-tap-registry-callback-dynamic-boundary"
    internal_abi["__lg_remove-tap"] = "documented-tap-registry-callback-dynamic-boundary"
    internal_abi["__lg_tap"] = "documented-tap-value-dynamic-boundary"
    internal_abi["__lg_flatten"] = "typed-homogeneous-seqable-layer-flatten-primitive"
    internal_abi["__lg_protocol-value"] = "typed-closed-protocol-witness-narrowing-primitive"
    internal_abi["__lg_reify_fn"] = "typed-reified-function-closure-construction-primitive"
    internal_abi["__lg_cljs-test-report"] = "documented-cljs-test-multimethod-report-event-dynamic-boundary"
    internal_abi["__lg_multimethod-methods"] = "documented-runtime-multifn-dynamic-method-table-introspection-boundary"
    internal_abi["__lg_multimethod-get-method"] = "documented-runtime-multifn-dynamic-method-handle-introspection-boundary"
    internal_abi["__lg_multimethod-dispatch-fn"] = "documented-runtime-multifn-dynamic-dispatch-function-handle-boundary"
    internal_abi["__lg_multimethod-remove-method"] = "documented-runtime-multifn-dynamic-method-table-mutation-boundary"
    internal_abi["__lg_multimethod-remove-all-methods"] = "documented-runtime-multifn-dynamic-method-table-mutation-boundary"
    internal_abi["__lg_multimethod-default-dispatch-val"] = "documented-runtime-multifn-dynamic-default-dispatch-boundary"
    internal_abi["__lg_multimethod-prefer-method"] = "documented-runtime-multifn-dynamic-preference-table-mutation-boundary"
    internal_abi["__lg_multimethod-prefers"] = "documented-runtime-multifn-dynamic-preference-table-introspection-boundary"
    internal_abi["__lg_sort"] = "typed-stable-sequence-sort-primitive"
    internal_abi["__lg_sort-by"] = "typed-key-projection-and-stable-sequence-sort-primitive"
    internal_abi["__lg_reductions"] = "typed-reducer-arity-and-seqable-adaptation-primitive"
    internal_abi["__lg_reduce-kv"] = "typed-empty-accumulator-and-collection-inference-primitive"
    internal_abi["__lg_reduce"] = "typed-reduced-short-circuit-and-collection-specialization-primitive"
    internal_abi["__lg_run"] = "typed-effectful-sequence-traversal-and-reduced-short-circuit-primitive"
    internal_abi["__lg_unreduced"] = "typed-parameterized-reduced-payload-extraction-primitive"
    internal_abi["__lg_ensure-reduced"] = "typed-conditional-parameterized-reduced-wrapper-primitive"
    internal_abi["__lg_force"] = "typed-lazy-force-or-static-identity-primitive"
    internal_abi["__lg_apply"] = "typed-dependent-fixed-arguments-and-final-sequence-application-primitive"
    internal_abi["__lg_rand"] = "typed-int-or-float-random-bound-specialization-primitive"
    internal_abi["__lg_max"] = "typed-numeric-extrema-specialization-primitive"
    internal_abi["__lg_min"] = "typed-numeric-extrema-specialization-primitive"
    internal_abi["__lg_into"] = "typed-target-collection-representation-and-transducer-specialization-primitive"
    internal_abi["__lg_mapv"] = "typed-variadic-multi-collection-vector-map-specialization-primitive"
    internal_abi["__lg_concat"] = "typed-mixed-storage-sequence-concatenation-specialization-primitive"
    internal_abi["__lg_interleave"] = "typed-mixed-storage-lazy-sequence-interleave-specialization-primitive"
    internal_abi["__lg_juxt"] = "typed-unary-direct-call-juxtaposition-specialization-primitive"
    internal_abi["__lg_comp"] = "typed-unary-direct-call-composition-specialization-primitive"
    internal_abi["__lg_fnil"] = "typed-default-substitution-function-specialization-primitive"
    internal_abi["__lg_bound-fn"] = "typed-dynamic-var-binding-capture-and-function-wrapper-specialization-primitive"
    internal_abi["__lg_partial"] = "typed-fixed-argument-function-specialization-primitive"
    internal_abi["__lg_name"] = "typed-concrete-name-coercion-and-generic-inamecoercion-protocol-elaboration-primitive"
    internal_abi["__lg_namespace"] = "typed-consumer-state-inamed-protocol-elaboration-primitive"
    internal_abi["__lg_builtin-name"] = "typed-built-in-keyword-and-symbol-name-extraction-primitive"
    internal_abi["__lg_builtin-keyword"] = "typed-string-keyword-symbol-and-optional-namespace-keyword-construction-primitive"
    internal_abi["__lg_builtin-symbol"] = "typed-string-keyword-symbol-and-optional-namespace-symbol-construction-primitive"
    internal_abi["__lg_builtin-namespace"] = "typed-built-in-keyword-and-symbol-namespace-extraction-primitive"
    internal_abi["__lg_write"] = "typed-writer-buffer-effect-primitive"
    internal_abi["__lg_pprint"] = "typed-readable-value-and-buffer-writer-pprint-primitive"
    internal_abi["__lg_str"] = "typed-per-argument-display-rendering-primitive"
    internal_abi["__lg_print_str"] = "typed-space-separated-per-argument-display-rendering-primitive"
    internal_abi["__lg_pr_str"] = "typed-space-separated-per-argument-readable-rendering-primitive"
    internal_abi["__lg_print_output"] = "typed-static-string-output-primitive"
    internal_abi["__lg_print_output_line"] = "typed-static-string-output-with-boolean-newline-and-flush-primitive"
    internal_abi["__lg_print_values"] = "typed-display-values-to-bound-writer-or-standard-output-primitive"
    internal_abi["__lg_pr"] = "typed-readable-values-to-bound-writer-or-standard-output-primitive"
    internal_abi["__lg_render_display_values"] = "typed-homogeneous-display-printer-witness-sequence-rendering-primitive"
    internal_abi["__lg_render_readable_values"] = "typed-homogeneous-readable-printer-witness-sequence-rendering-primitive"
    internal_abi["__lg_render_readable_values_with_opts"] = "typed-homogeneous-readable-printer-witness-sequence-rendering-with-print-length-options-primitive"
    internal_abi["__lg_pr-writer"] = "typed-readable-printer-witness-and-buffer-output-primitive"
    internal_abi["__lg_print-map"] = "typed-static-map-printer-with-independent-key-value-witnesses-and-namespace-lifting"
    internal_abi["__lg_print-prefix-map"] = "typed-static-prefix-map-printer-with-independent-key-value-witnesses"
    internal_abi["__lg_print-meta?"] = "typed-closed-edn-metadata-presence-and-meta-option-primitive"
    internal_abi["__lg_repl-result"] = "typed-repl-static-result-rendering-and-publication-primitive"
    internal_abi["__lg_equal"] = "typed-static-generic-equality-primitive"
    internal_abi["__lg_add"] = "typed-static-numeric-addition-primitive"
    internal_abi["__lg_subtract"] = "typed-static-numeric-subtraction-primitive"
    internal_abi["__lg_multiply"] = "typed-static-int-float-or-arbitrary-precision-decimal-multiplication-primitive"
    internal_abi["__lg_divide"] = "typed-native-exact-ratio-or-static-numeric-division-primitive"
    internal_abi["__lg_divide-melange"] = "typed-melange-floating-numeric-division-primitive"
    internal_abi["__lg_numeric-equal"] = "typed-static-numeric-equality-primitive"
    internal_abi["__lg_less"] = "typed-static-numeric-less-than-primitive"
    internal_abi["__lg_less-equal"] = "typed-static-numeric-less-than-or-equal-primitive"
    internal_abi["__lg_greater"] = "typed-static-numeric-greater-than-primitive"
    internal_abi["__lg_greater-equal"] = "typed-static-numeric-greater-than-or-equal-primitive"
    internal_abi["__lg_assoc"] = "typed-associated-map-vector-and-record-shape-primitive"
    internal_abi["__lg_dissoc"] = "typed-map-and-record-shape-removal-primitive"
    internal_abi["__lg_contains"] = "typed-key-index-and-membership-capability-primitive"
    internal_abi["__lg_find"] = "typed-map-entry-lookup-capability-primitive"
    internal_abi["__lg_keys"] = "typed-map-key-projection-primitive"
    internal_abi["__lg_subvec"] = "typed-vector-slice-primitive"
    internal_abi["__lg_array"] = "typed-homogeneous-array-construction-primitive"
    internal_abi["__lg_hash"] = "typed-hashable-capability-primitive"
    internal_abi["__lg_compare"] = "typed-single-domain-comparable-capability-primitive"
    internal_abi["__lg_fn-to-comparator"] = "typed-return-directed-int-comparator-or-boolean-predicate-normalization-primitive"
    internal_abi["__lg_make-array"] = "typed-homogeneous-array-allocation-primitive"
    internal_abi["__lg_aget"] = "typed-array-index-capability-read-primitive"
    internal_abi["__lg_aset"] = "typed-array-index-capability-write-primitive"
    internal_abi["__lg_atom"] = "typed-reference-allocation-primitive"
    internal_abi["__lg_add-watch"] = "typed-keyword-reference-watch-registration-primitive"
    internal_abi["__lg_remove-watch"] = "typed-keyword-reference-watch-removal-primitive"
    internal_abi["__lg_get-validator"] = "typed-reference-validator-read-primitive"
    internal_abi["__lg_set-validator!"] = "typed-reference-validator-install-or-clear-primitive"
    internal_abi["__lg_reset-meta!"] = "typed-reference-closed-edn-metadata-reset-primitive"
    internal_abi["__lg_swap!"] = "typed-contextual-reference-swap-primitive"
    internal_abi["__lg_volatile!"] = "typed-volatile-reference-allocation-primitive"
    internal_abi["__lg_weak-deref"] = "typed-weak-reference-read-primitive"
    internal_abi["__lg_weak-clear!"] = "typed-weak-reference-clear-primitive"
    internal_abi["__lg_abs"] = "typed-static-numeric-absolute-value-primitive"
    internal_abi["__lg_dec"] = "typed-static-numeric-decrement-primitive"
    internal_abi["__lg_bigint"] = "typed-integer-reader-and-conversion-primitive"
    internal_abi["__lg_bigdec"] = "typed-floating-decimal-conversion-compatibility-primitive"
    internal_abi["__lg_nan-predicate"] = "typed-floating-point-nan-predicate-primitive"
    internal_abi["__lg_decimal-predicate"] = "typed-static-decimal-representation-predicate-primitive"
    internal_abi["__lg_ratio-predicate"] = "typed-static-ratio-representation-predicate-primitive"
    internal_abi["__lg_with-precision"] = "typed-arbitrary-precision-decimal-math-context-thunk-primitive"
    internal_abi["__lg_array-map"] = "typed-alternating-key-value-array-map-construction-primitive"
    internal_abi["__lg_hash-map"] = "typed-alternating-key-value-hash-map-construction-primitive"
    internal_abi["__lg_hash-set"] = "typed-homogeneous-hash-set-construction-primitive"
    internal_abi["__lg_list"] = "typed-homogeneous-list-construction-primitive"
    internal_abi["__lg_list-star"] = "typed-fixed-prefix-and-final-seqable-list-construction-primitive"
    internal_abi["__lg_vector"] = "typed-homogeneous-vector-construction-primitive"
    internal_abi["__lg_assoc-in"] = "typed-dependent-nested-association-primitive"
    internal_abi["__lg_get-in"] = "typed-dependent-nested-lookup-primitive"
    internal_abi["__lg_get-in-step"] = "typed-nested-lookup-step-with-closed-edn-and-non-associative-short-circuiting"
    internal_abi["__lg_update-in"] = "typed-dependent-nested-update-primitive"
    internal_abi["__lg_select-keys"] = "typed-dependent-map-key-projection-primitive"
    internal_abi["__lg_vals"] = "typed-map-value-projection-primitive"
    internal_abi["__lg_conj"] = "typed-collection-preserving-conjoin-primitive"
    internal_abi["__lg_cons"] = "typed-seqable-prepend-primitive"
    internal_abi["__lg_count"] = "typed-counted-or-seqable-count-primitive"
    internal_abi["__lg_first"] = "typed-seqable-first-element-primitive"
    internal_abi["__lg_next"] = "typed-seqable-optional-successor-primitive"
    internal_abi["__lg_rest"] = "typed-seqable-rest-primitive"
    internal_abi["__lg_seq"] = "typed-seqable-sequence-adaptation-primitive"
    internal_abi["__lg_get"] = "typed-map-vector-set-or-record-lookup-primitive"
    internal_abi["__lg_nth"] = "typed-indexed-or-seqable-access-primitive"
    internal_abi["__lg_map"] = "typed-lazy-map-and-transducer-specialization-primitive"
    internal_abi["__lg_merge"] = "typed-variadic-map-shape-unification-primitive"
    internal_abi["__lg_memoize"] = "typed-fixed-arity-function-memoization-primitive"
    internal_abi["__lg_with_redefs"] = "typed-var-root-temporary-rebinding-primitive"
    internal_abi["__lg_watch_redef"] = "typed-development-root-replacement-observer-primitive"
    internal_abi["__lg_set"] = "typed-seqable-to-set-conversion-primitive"
    internal_abi["__lg_some"] = "typed-nullable-first-truthy-sequence-search-primitive"
    internal_abi["__lg_complement"] = "typed-contextual-fixed-arity-predicate-negation-primitive"
    internal_abi["__lg_constantly"] = "typed-contextual-constant-function-construction-primitive"
    internal_abi["__lg_update"] = "typed-map-vector-or-record-update-primitive"
    internal_abi["__lg_with-meta"] = "typed-closed-edn-metadata-conversion-primitive"
    internal_abi["__lg_transient"] = "typed-persistent-to-transient-collection-primitive"
    internal_abi["__lg_persistent!"] = "typed-transient-to-persistent-collection-primitive"
    internal_abi["__lg_assoc!"] = "typed-transient-association-primitive"
    internal_abi["__lg_conj!"] = "typed-transient-conjoin-primitive"
    internal_abi["__lg_dissoc!"] = "typed-transient-map-removal-primitive"
    internal_abi["__lg_complete_transformed"] = "typed-transducer-completion-primitive"
    internal_abi["__lg_reduce_transformed"] = "typed-transducer-reduction-primitive"
    internal_abi["__lg_transformer_sequence"] = "typed-transducer-lazy-sequence-primitive"
    internal_abi["__lg_regex-predicate"] = "typed-regex-boolean-match-primitive"
    internal_abi["__type-hint"] = "compiler-internal-static-type-constraint-marker"
    split("None Some Ok Error", xs)
    for (i in xs) typed_reason[xs[i]] = "closed-option-or-result-constructor-elaboration"
    split("array-of list-of set-of vector-of", xs)
    for (i in xs) typed_reason[xs[i]] = "explicit-homogeneous-collection-type-constructor"
    split("as-ordering ordering-compare uncurried-compare", xs)
    for (i in xs) typed_reason[xs[i]] = "typed-static-comparator-capability-elaboration"
    split("record tuple tuple-get", xs)
    for (i in xs) typed_reason[xs[i]] = "typed-record-or-tuple-construction-and-projection-elaboration"
    split("seq-flat-map seq-flat-map-rev seq-uncons seq-unfold seq-unfold-chunks seq-unfold-unmemoized", xs)
    for (i in xs) typed_reason[xs[i]] = "typed-lazy-sequence-construction-primitive"
    typed_reason["uncurried-call"] = "typed-static-uncurried-callback-application-primitive"
    typed_reason["IllegalArgumentException."] = "typed-native-invalid-argument-compatibility-constructor"
    split("unsafe-aget unsafe-aset", xs)
    for (i in xs) typed_reason[xs[i]] = "typed-host-array-index-access-primitive"
    host_reason["."] = "host-member-invocation-syntax-boundary"
    split(".compareTo .containsKey .entryAt .equals .getBytes .getClass .getName .getTime .map .toByteArray .toString .valAt .write", xs)
    for (i in xs) host_reason[xs[i]] = "explicit-host-method-interop-boundary"
    host_reason[".replace"] = "explicit-host-string-replacement-method-boundary"
    host_reason["Object."] = "native-host-object-constructor-boundary"
    host_reason["System/getProperty"] = "native-host-system-property-read-boundary"
    host_reason["__deftype-field-set!"] = "mutable-host-field-assignment-boundary"
    host_reason["clj->js"] = "recursive-static-value-to-javascript-host-conversion-boundary"
    host_reason["current-time-millis"] = "target-specific-system-clock-boundary"
    host_reason["ex-info"] = "open-exception-data-and-host-stack-boundary"
    split("js/Date. js/Error.", xs)
    for (i in xs) host_reason[xs[i]] = "javascript-host-constructor-boundary"
    split("js/isNaN js/parseInt js/performance.now", xs)
    for (i in xs) host_reason[xs[i]] = "javascript-global-function-boundary"
    host_reason["raise"] = "host-exception-raising-boundary"
    host_reason["class"] = "runtime-class-inspection-conflicts-with-lg-closed-static-types"
    host_reason["type"] = "runtime-class-inspection-conflicts-with-lg-closed-static-types"
    split("requiring-resolve resolve", xs)
    for (i in xs) host_reason[xs[i]] = "compiler-namespace-resolution-boundary"
    host_reason["weak-ref"] = "target-specific-weak-reference-allocation-boundary"
    split("__lg_nil-predicate __lg_true-predicate __lg_false-predicate __lg_int-predicate __lg_number-predicate __lg_string-predicate __lg_keyword-predicate __lg_symbol-predicate __lg_list-predicate __lg_seq-predicate __lg_fn-predicate __lg_ifn-predicate __lg_ratio-predicate __lg_rational-predicate __lg_float-predicate __lg_double-predicate __lg_zero-predicate __lg_pos-predicate __lg_neg-predicate __lg_char-predicate __lg_identical-predicate __lg_array-predicate __lg_array-value-predicate __lg_reduced-predicate __lg_uuid-predicate __lg_delay-predicate", xs)
    for (i in xs) type_predicate[xs[i]] = 1
  }
  {
    classification = "typed-primitive"
    reason = "static-elaboration-or-minimal-runtime-abi"
    if (special[$0]) {
      classification = "special-form"
      reason = special_reason[$0]
      if (reason == "") reason = "compiler-owned-syntax-or-control-flow"
    } else if (blocked[$0]) {
      classification = "blocked-static-typing"
      reason = blocked_reason[$0]
      if (reason == "") {
        print "missing concrete blocker reason for " $0 > "/dev/stderr"
        exit 1
      }
    } else if (narrowing[$0]) {
      classification = "typed-primitive"
      reason = "static-guard-narrowing-primitive"
    } else if ($0 in internal_abi) {
      classification = "typed-primitive"
      reason = internal_abi[$0]
    } else if (type_predicate[$0]) {
      classification = "typed-primitive"
      reason = "internal-static-type-predicate-primitive"
    } else if ($0 in typed_reason) {
      classification = "typed-primitive"
      reason = typed_reason[$0]
    } else if (primitive[$0]) {
      classification = "typed-primitive"
      reason = "static-scalar-primitive"
    } else if ($0 in host_reason) {
      classification = "host-boundary"
      reason = host_reason[$0]
    } else if (host[$0] || $0 ~ /^\./ || $0 ~ /^js\// || $0 ~ /^__/ || $0 ~ /^-/) {
      classification = "host-boundary"
      reason = "host-interop-or-runtime-effect-boundary"
    }
    print "compiler-call\t" $0 "\t" classification "\t" reason
  }
' "$tmp/compiler-calls" >"$tmp/compiler-status"

cat "$tmp/compiler-status"

# Public forms can also be dispatched before call elaboration. Extract only
# symbols in the head position of FList patterns so generated forms and nested
# pattern syntax do not masquerade as public compiler routes.
ocaml -I +compiler-libs ocamlcommon.cma \
  "$lg_root/script/extract_ocaml_form_symbol_patterns.ml" \
  "$expression_elaborator" "$type_inference" \
  >"$tmp/compiler-forms"

form_dispatch_count=$(wc -l <"$tmp/compiler-forms" | tr -d ' ')
if test "$form_dispatch_count" -ne 174; then
  echo "compiler form dispatch changed: expected 174 names, found $form_dispatch_count" >&2
  echo "review and classify every added or removed form before updating the count" >&2
  exit 1
fi

awk -F '\t' '
  BEGIN {
    form_reason["->Eduction"] = "typed-eduction-record-constructor-elaboration"
    form_reason["IDeref/-deref"] = "typed-reference-dereference-protocol-elaboration"
    form_reason["IReset/-reset!"] = "typed-reference-reset-protocol-elaboration"
    form_reason["IVolatile/-vreset!"] = "typed-volatile-reset-protocol-elaboration"
    form_reason["__lg_if-let"] = "private-source-static-truthy-binding-expansion"
    form_reason["__lg_when-let"] = "private-source-static-truthy-binding-expansion"
    form_reason["__lg_if-some"] = "private-source-static-non-nil-binding-expansion"
    form_reason["__lg_when-some"] = "private-source-static-non-nil-binding-expansion"
    form_reason["__lg_some-thread"] = "private-source-static-non-nil-threading-expansion"
    form_reason["__lg_quote"] = "private-compiler-owned-quote-normalization-marker"
    form_reason["__lg_logical-and"] = "private-source-static-short-circuit-and-expansion"
    form_reason["__lg_logical-or"] = "private-source-static-short-circuit-or-expansion"
    form_reason["__lg_second"] = "private-source-static-tuple-or-seqable-second-element-elaboration"
    form_reason["__lg_reify_fn"] = "private-typed-reified-function-closure-inference-primitive"
    form_reason["__lg_defer_seq"] = "private-typed-lazy-sequence-thunk-and-recursive-result-inference-primitive"
    form_reason["__lg_not"] = "private-typed-static-truthiness-negation-inference-primitive"
    form_reason["__lg_dec"] = "private-typed-static-numeric-decrement-inference-primitive"
    form_reason["__lg_constantly"] = "private-typed-contextual-constant-function-inference-primitive"
    form_reason["__lg_name"] = "private-typed-inamecoercion-name-inference-primitive"
    form_reason["__lg_namespace"] = "private-typed-inamed-namespace-inference-primitive"
    form_reason["new"] = "typed-host-constructor-application-elaboration"
    form_reason["#uuid"] = "compiler-owned-tagged-uuid-reader-literal-elaboration"
    form_reason["#inst"] = "compiler-owned-validated-tagged-instant-reader-literal-elaboration"
    form_reason["__lg_with-precision"] = "private-typed-arbitrary-precision-decimal-math-context-inference-primitive"
    form_reason["tag"] = "lg-extension-statically-typed-polymorphic-variant-construction"
    form_reason["pack-module"] = "lg-extension-static-first-class-module-packaging"
    form_reason["let-module"] = "lg-extension-lexically-scoped-module-unpacking"
    form_reason["letfn"] = "compiler-owned-recursive-local-function-binding-elaboration"
  }
  FNR == NR {
    if ($1 == "compiler-call") {
      call_status[$2] = $3
      call_reason[$2] = $4
    }
    next
  }
  {
    name = $0
    canonical = name
    sub(/^(clojure|cljs)\.core\//, "", canonical)
    status = "typed-primitive"
    reason = "static-form-elaboration-or-compiler-internal-form"
    if (canonical in form_reason) {
      reason = form_reason[canonical]
    } else if (canonical == "case" || canonical == "condp") {
      status = "special-form"
      reason = "compiler-owned-source-control-flow-expansion"
    } else if (canonical == "__lg_doseq") {
      status = "special-form"
      reason = "private-source-doseq-binding-modifier-and-loop-control-expansion"
    } else if (canonical == "for") {
      status = "special-form"
      reason = "compiler-owned-binding-modifier-and-lazy-sequence-expansion"
    } else if (canonical == "dotimes") {
      status = "special-form"
      reason = "compiler-owned-bounded-loop-expansion"
    } else if (canonical ~ /^(catch|finally|do|if|let|let\*|loop|recur|fn|quote|try|syntax-quote|match|let-some)$/) {
      status = "special-form"
      reason = "compiler-owned-syntax-or-control-flow"
    } else if (canonical in call_status) {
      status = call_status[canonical]
      reason = call_reason[canonical]
    }
    print "compiler-form\t" name "\t" status "\t" reason
  }
' "$tmp/compiler-status" "$tmp/compiler-forms" >"$tmp/compiler-form-status"

cat "$tmp/compiler-form-status"

bb "$lg_root/script/extract_stdlib_manifest_status.clj" \
  "$lg_root/stdlib/upstream.edn" >"$tmp/manifest-status"

if test -n "$clojurescript_root"; then
  : >"$tmp/upstream-vars"
  bb "$lg_root/script/extract_clojurescript_public_vars.clj" cljs.core \
    "$clojurescript_root/src/main/cljs/cljs/core.cljs" \
    "$clojurescript_root/src/main/clojure/cljs/core.cljc" \
    >>"$tmp/upstream-vars"
  for namespace_and_source in \
    'clojure.string|src/main/cljs/clojure/string.cljs' \
    'clojure.core.protocols|src/main/cljs/clojure/core/protocols.cljs' \
    'clojure.set|src/main/cljs/clojure/set.cljs' \
    'clojure.data|src/main/cljs/clojure/data.cljs' \
    'clojure.walk|src/main/cljs/clojure/walk.cljs' \
    'clojure.edn|src/main/cljs/clojure/edn.cljs' \
    'cljs.reader|src/main/cljs/cljs/reader.cljs' \
    'cljs.math|src/main/cljs/cljs/math.cljs' \
    'cljs.pprint|src/main/cljs/cljs/pprint.cljs' \
    'cljs.test|src/main/cljs/cljs/test.cljs' \
    'cljs.spec.alpha|src/main/cljs/cljs/spec/alpha.cljs' \
    'clojure.zip|src/main/cljs/clojure/zip.cljs'; do
    namespace=${namespace_and_source%%|*}
    source=${namespace_and_source#*|}
    bb "$lg_root/script/extract_clojurescript_public_vars.clj" "$namespace" \
      "$clojurescript_root/$source" >>"$tmp/upstream-vars"
  done
  bb "$lg_root/script/extract_clojurescript_public_vars.clj" cljs.pprint \
    "$clojurescript_root/src/main/cljs/cljs/pprint.cljc" \
    >>"$tmp/upstream-vars"
  bb "$lg_root/script/extract_clojurescript_public_vars.clj" cljs.test \
    "$clojurescript_root/src/main/cljs/cljs/test.cljc" \
    >>"$tmp/upstream-vars"
  LC_ALL=C sort -u "$tmp/upstream-vars" -o "$tmp/upstream-vars"
  upstream_var_count=$(wc -l <"$tmp/upstream-vars" | tr -d ' ')
  if test "$upstream_var_count" -ne 1058; then
    echo "ClojureScript public var surface changed: expected 1058 entries, found $upstream_var_count" >&2
    echo "review the pinned upstream files and classifications before updating the count" >&2
    exit 1
  fi

  : >"$tmp/source-vars"
  bb "$lg_root/script/extract_clojurescript_public_vars.clj" cljs.core \
    "$lg_root/stdlib/clojure/core.cljc" >>"$tmp/source-vars"
  for namespace_and_source in \
    'clojure.string|stdlib/clojure/string.cljc' \
    'clojure.core.protocols|stdlib/clojure/core/protocols.cljc' \
    'clojure.set|stdlib/clojure/set.cljc' \
    'clojure.edn|stdlib/clojure/edn.cljc' \
    'cljs.reader|stdlib/cljs/reader.cljc' \
    'cljs.math|stdlib/cljs/math.cljc' \
    'cljs.pprint|stdlib/cljs/pprint.cljc' \
    'cljs.test|stdlib/cljs/test.cljc' \
    'clojure.data|stdlib/clojure/data.cljc' \
    'clojure.walk|stdlib/clojure/walk.cljc' \
    'clojure.zip|stdlib/clojure/zip.cljc'; do
    namespace=${namespace_and_source%%|*}
    source=${namespace_and_source#*|}
    bb "$lg_root/script/extract_clojurescript_public_vars.clj" "$namespace" \
      "$lg_root/$source" >>"$tmp/source-vars"
  done
  LC_ALL=C sort -u "$tmp/source-vars" -o "$tmp/source-vars"

  awk -F '\t' '
    BEGIN {
      split("seq first rest next some conj juxt comp fnil partial", names, " ")
      for (i in names) source_inference[names[i]] = 1
    }
    FILENAME == ARGV[1] && $1 == "compiler-call" {
      compiler_call[$2] = 1
      next
    }
    FILENAME == ARGV[2] && $1 == "compiler-form" {
      name = $2
      sub(/^(clojure|cljs)\.core\//, "", name)
      compiler_form[name] = 1
      next
    }
    FILENAME == ARGV[3] && $1 ~ /^cljs\.core\// {
      name = $1
      sub(/^cljs\.core\//, "", name)
      if ((name in compiler_call) ||
          ((name in compiler_form) && !(name in source_inference))) {
        print "source core var still has name-based compiler dispatch: " name > "/dev/stderr"
        failed = 1
      }
    }
    END {exit failed}
  ' "$tmp/compiler-status" "$tmp/compiler-form-status" "$tmp/source-vars"

  awk -F '\t' '{print "source-var\t" $1 "\t" $2}' \
    "$tmp/source-vars" >"$tmp/upstream-status-input"
  cat "$tmp/compiler-status" "$tmp/compiler-form-status" \
    "$tmp/manifest-status" \
    >>"$tmp/upstream-status-input"
  awk -F '\t' '{print "upstream-var\t" $1 "\t" $2}' \
    "$tmp/upstream-vars" >>"$tmp/upstream-status-input"

  awk -F '\t' '
    $1 == "source-var" {
      source[$2 SUBSEP $3] = 1
      next
    }
    $1 == "compiler-call" {
      compiler_status[$2] = $3
      compiler_reason[$2] = $4
      next
    }
    $1 == "compiler-form" {
      name = $2
      sub(/^(clojure|cljs)\.core\//, "", name)
      form_status[name] = $3
      form_reason[name] = $4
      next
    }
    $1 == "definition" {
      definition_status[$2] = $3
      definition_reason[$2] = $4
      if (index($2, "clojure.core/") == 1) {
        core_alias = "cljs.core/" substr($2, length("clojure.core/") + 1)
        definition_status[core_alias] = $3
        definition_reason[core_alias] = $4
      }
      next
    }
    $1 == "namespace" {
      namespace_status[$2] = $3
      namespace_reason[$2] = $4
      next
    }
    $1 == "upstream-var" {
      qualified = $2
      kind = $3
      split(qualified, parts, "/")
      namespace = parts[1]
      name = substr(qualified, length(namespace) + 2)
      status = "deferred"
      reason = "not-yet-ported-or-statically-classified"
      if ((qualified SUBSEP kind) in source) {
        status = "source"
        reason = "precompiled-lg-source"
      } else if (qualified in definition_status) {
        status = definition_status[qualified]
        reason = definition_reason[qualified]
      } else if (namespace == "cljs.core" && name in compiler_status) {
        status = compiler_status[name]
        reason = compiler_reason[name]
      } else if (namespace == "cljs.core" && name in form_status) {
        status = form_status[name]
        reason = form_reason[name]
      } else if (namespace in namespace_status &&
                 (namespace_status[namespace] == "blocked-static-typing" ||
                  namespace_status[namespace] == "host-boundary" ||
                  namespace_status[namespace] == "out-of-scope")) {
        status = namespace_status[namespace]
        reason = namespace_reason[namespace]
      }
      print "upstream-var\t" qualified "\t" kind "\t" status "\t" reason
    }
  ' "$tmp/upstream-status-input" \
    | LC_ALL=C sort -t '	' -k2,2 -k3,3
fi

awk -F '\t' '$1 == "namespace-ownership" {
  print "namespace\t" $2 "\t" $3
}' "$tmp/manifest-status"
awk -F '\t' '$1 == "namespace" {
  print "namespace-status\t" $2 "\t" $3 "\t" $4
}' "$tmp/manifest-status"
awk -F '\t' '$1 == "definition" {
  print
}' "$tmp/manifest-status"

core_ownership=$(awk -F '\t' '
  $1 == "namespace-ownership" && $2 == "clojure.core" {print $3}
' "$tmp/manifest-status")
if test -z "$core_ownership"; then
  echo "stdlib manifest does not classify clojure.core ownership" >&2
  exit 1
fi
printf 'namespace\tcljs.core\t%s\n' "$core_ownership"
printf 'namespace-status\tcljs.core\tsource-aggregate\tautomatic-core-source-alias\n'
printf 'namespace-bootstrap\tclojure.core\tautomatic-core-refer\n'
printf 'namespace-bootstrap\tcljs.core\tautomatic-core-refer\n'

while IFS='|' read -r var classification; do
  printf 'namespace-var\t%s\t%s\n' "$var" "$classification"
done <<'EOF'
clojure.data/diff|source
clojure.data/equality-partition|source
clojure.data/diff-similar|source
clojure.edn/read-string|source
clojure.edn/register-tag-parser!|host-boundary
cljs.reader/read-string|source
cljs.reader/register-tag-parser!|host-boundary
cljs.pprint/float?|source
cljs.pprint/char-code|source
cljs.pprint/pprint|source
cljs.test/empty-env|source
cljs.test/*current-env*|source
cljs.test/get-current-env|source
cljs.test/set-env!|source
cljs.test/clear-env!|source
cljs.test/get-and-clear-env!|source
cljs.test/inc-report-counter!|source
cljs.test/report|source
cljs.test/testing-contexts-str|source
cljs.test/testing|source
cljs.test/is|source
cljs.test/are|source
cljs.test/try-expr|source
cljs.test/assert-expr|source
cljs.test/deftest|source
cljs.test/run-test|source
cljs.test/run-tests|source
cljs.test/update-current-env!|source
cljs.test/use-fixtures|source
cljs.test/ns?|source
cljs.test/compose-fixtures|source
cljs.test/join-fixtures|source
cljs.test/successful?|source
cljs.test/run-block|source
cljs.test/test-var-block|source
cljs.test/test-var|source
cljs.test/test-vars-block|source
cljs.test/test-vars|source
cljs.test/testing-vars-str|source
cljs.test/async|source
cljs.test/async?|source
cljs.test/block|source
cljs.test/run-tests-block|source
cljs.test/test-all-vars-block|source
cljs.test/test-all-vars|source
cljs.test/test-ns-block|source
cljs.test/test-ns|source
clojure.core/chunk-buffer|source
clojure.core/array-chunk|source
clojure.core/chunk-append|source
clojure.core/chunk|source
clojure.core/-chunked-first|source
clojure.core/-chunked-rest|source
clojure.core/-chunked-next|source
clojure.core/chunk-cons|source
clojure.core/chunk-first|source
clojure.core/chunk-rest|source
clojure.core/chunk-next|source
clojure.core/uuid|source
clojure.set/project|source
clojure.set/rename|source
clojure.string/escape|source
clojure.string/split|source
clojure.walk/walk|source
clojure.walk/prewalk|source
clojure.walk/postwalk|source
clojure.walk/keywordize-keys|source
clojure.walk/stringify-keys|source
clojure.walk/prewalk-replace|source
clojure.walk/postwalk-replace|source
clojure.zip/zipper|source
clojure.zip/root|source
clojure.zip/next|source
EOF

stdlib_sources=$(rg --files "$lg_root/stdlib" -g '*.cljc')
sed -n \
  's/.*\[ocaml\.\(Lg_runtime\.Runtime_[A-Za-z0-9_]*\) :as \([A-Za-z0-9_-]*\)\].*/\1\	\2/p' \
  $stdlib_sources >"$tmp/stdlib-runtime-aliases"

(
  rg -o --no-filename \
    -g '*.ml' -g '*.mli' -g '*.cljc' -g '*.lgi' \
    'Lg_runtime\.Runtime_[A-Za-z0-9_]+(\.[a-z][A-Za-z0-9_]*)+' \
    "$lg_root/src" "$lg_root/stdlib"
  while IFS="$(printf '\t')" read -r module alias; do
    rg -o --no-filename "${alias}/[a-z][A-Za-z0-9_!?-]*" \
      $stdlib_sources \
      | awk -v module="$module" '{
          member = $0
          sub(/^[^\/]*\//, "", member)
          gsub(/-/, "_", member)
          gsub(/\?/, "_question", member)
          gsub(/!/, "_bang", member)
          print module "." member
        }'
  done <"$tmp/stdlib-runtime-aliases"
) | LC_ALL=C sort -u \
  | awk '{print "runtime-primitive\t" $0 "\ttyped-primitive-boundary"}'

if test -n "$logseq_root" && test -d "$logseq_root"; then
  if git -C "$logseq_root" rev-parse HEAD >"$tmp/logseq-commit" 2>/dev/null; then
    printf 'meta\tlogseq-commit\t%s\n' "$(sed -n '1p' "$tmp/logseq-commit")"
  fi
  sed -n '/:aggregate-namespaces/,/]/p' "$lg_root/stdlib/upstream.edn" \
    | tr ' []' '\n' \
    | awk '/^(clojure|cljs)\./ {
        print $1 "\tsource-aggregate\taggregate-stdlib"
        if ($1 == "clojure.core") {
          print "cljs.core\tsource-core-alias\tautomatic-core-alias"
        }
      }' >"$tmp/namespace-support"

  # Exact non-source definition classifications override their namespace. A
  # blocked or host-only sibling must never downgrade an aggregate namespace or
  # another source definition in that namespace.
  awk -F '\t' '
    $1 == "namespace" && $3 != "source-aggregate" && $3 != "source" {
      print $2 "\t" $3 "\t" $4
    }
    $1 == "definition" {
      if ($3 == "source") {
        print $2 "\tsource-aggregate\tprecompiled-lg-source"
      } else {
        print $2 "\t" $3 "\t" $4
      }
    }
  ' "$tmp/manifest-status" >>"$tmp/namespace-support"

  (
    cd "$logseq_root"
    rg --files -0 -g '*.clj' -g '*.cljs' -g '*.cljc' \
      | xargs -0 -n 100 bb "$lg_root/script/clojure_namespace_inventory.clj"
  ) \
    | LC_ALL=C sort \
    | uniq -c \
    | awk '
        $2 == "namespace" {
          print "logseq-namespace\t" $3 "\t" $1
        }
        $2 == "qualified-var" {
          print "logseq-qualified-var\t" $3 "\t" $1
        }
        $2 == "core-var" {
          print "logseq-core-var\t" $3 "\t" $1
        }
      ' \
    | LC_ALL=C sort -t '	' -k1,1 -k3,3nr -k2,2 \
    >"$tmp/logseq-counts"

  awk -F '\t' '
    FNR == NR {
      support[$1] = $2
      reason[$1] = $3
      next
    }
    function namespace_status(namespace) {
      return namespace in support ? support[namespace] : "unsupported"
    }
    function namespace_reason(namespace) {
      return namespace in reason ? reason[namespace] : "not-in-aggregate-or-blocked-manifest"
    }
    {
      if ($1 == "logseq-namespace") {
        print
        print "logseq-namespace-status\t" $2 "\t" namespace_status($2) \
          "\t" $3 "\t" namespace_reason($2)
      } else if ($1 == "logseq-qualified-var") {
        print
        split($2, qualified, "/")
        namespace = qualified[1]
        print "logseq-qualified-var-status\t" $2 "\t" \
          ($2 in support ? support[$2] : namespace_status(namespace)) "\t" $3 "\t" \
          ($2 in reason ? reason[$2] : namespace_reason(namespace))
      } else if ($1 == "logseq-core-var") {
        if ($2 in support) {
          print
          print "logseq-core-var-status\t" $2 "\t" \
            support[$2] "\t" $3 "\t" reason[$2]
        }
      }
    }
  ' "$tmp/namespace-support" "$tmp/logseq-counts" \
    | LC_ALL=C sort -t '	' -k1,1 -k2,2
fi
