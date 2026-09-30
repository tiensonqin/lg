(rule
 (targets
  test_declared_protocol_methods_reject_duplicate_arity.actual
  test_defonce_rejects_invalid_declarations_1.actual
  test_defonce_rejects_invalid_declarations_2.actual
  test_defonce_rejects_invalid_declarations_3.actual
  test_direct_external_package_constructors_reject_bad_arity.actual
  test_direct_ocaml_constructors_reject_bad_arity_1.actual
  test_direct_ocaml_constructors_reject_bad_arity_2.actual
  test_direct_ocaml_constructors_reject_bad_arity_3.actual
  test_hash_map_rejects_odd_key_value_forms.actual
  test_include_module_rejects_bad_forms_1.actual
  test_include_module_rejects_bad_forms_2.actual
  test_module_alias_rejects_bad_forms.actual
  test_module_functors_reject_bad_forms_1.actual
  test_module_functors_reject_bad_forms_2.actual
  test_module_functors_reject_bad_forms_3.actual
  test_module_functors_reject_bad_forms_4.actual
  test_module_functors_reject_bad_forms_5.actual
  test_multi_arity_defn_rejects_invalid_declarations_1.actual
  test_multi_arity_defn_rejects_invalid_declarations_2.actual
  test_namespace_refer_clojure_exclude_hides_core_binding.actual
  test_namespace_rejects_malformed_and_repeated_forms_1.actual
  test_namespace_rejects_malformed_and_repeated_forms_2.actual
  test_namespace_rejects_malformed_and_repeated_forms_3.actual
  test_nil_type_annotation_remains_explicitly_unsupported.actual
  test_ocaml_option_and_result_constructors_reject_bad_arity_1.actual
  test_ocaml_option_and_result_constructors_reject_bad_arity_2.actual
  test_ocaml_option_and_result_constructors_reject_bad_arity_3.actual
  test_ocaml_option_and_result_constructors_reject_bad_arity_4.actual
  test_ocaml_type_application_annotations_reject_bad_forms_1.actual
  test_ocaml_type_application_annotations_reject_bad_forms_2.actual
  test_ocaml_variant_constructors_reject_bad_arity_1.actual
  test_ocaml_variant_constructors_reject_bad_arity_2.actual
  test_ocaml_variants_reject_bad_declarations_1.actual
  test_ocaml_variants_reject_bad_declarations_2.actual
  test_ocaml_variants_reject_bad_declarations_3.actual
  test_println_rejects_unknown_symbols.actual
  test_private_defn_rejects_invalid_declarations_1.actual
  test_private_defn_rejects_invalid_declarations_2.actual
  test_protocols_reject_duplicate_method_declarations.actual
  test_set_of_rejects_nil_element_annotation.actual
  test_set_of_rejects_types_without_comparators_1.actual
  test_set_of_rejects_types_without_comparators_2.actual
  test_try_and_raise_reject_malformed_forms_1.actual
  test_try_and_raise_reject_malformed_forms_2.actual
  test_try_and_raise_reject_malformed_forms_3.actual
  test_try_and_raise_reject_malformed_forms_4.actual
  test_try_and_raise_reject_malformed_forms_5.actual
  test_try_and_raise_reject_malformed_forms_6.actual
  test_variadic_signature_rejects_missing_rest_type.actual
 )
 (deps
  ../../stdlib/clojure/core.lgi
  ../../stdlib/clojure/core.cljc
  ../../stdlib/clojure/string.lgi
  ../../stdlib/clojure/string.cljc
  ../../stdlib/clojure/edn.lgi
  ../../stdlib/clojure/edn.cljc
  ../../stdlib/cljs/reader.lgi
  ../../stdlib/cljs/reader.cljc
  ../../stdlib/clojure/set.lgi
  ../../stdlib/clojure/set.cljc
  ../../stdlib/clojure/data.lgi
  ../../stdlib/clojure/data.cljc
  ../../stdlib/clojure/walk.lgi
  ../../stdlib/clojure/walk.cljc
  ../../stdlib/clojure/zip.lgi
  ../../stdlib/clojure/zip.cljc
  ../../stdlib/cljs/cache.cljc
  ../../stdlib/cljs/pprint.lgi
  ../../stdlib/cljs/pprint.cljc
  ../../stdlib/cljs/test.lgi
  ../../stdlib/cljs/test.cljc
  cases/test_declared_protocol_methods_reject_duplicate_arity.cljc
  cases/test_defonce_rejects_invalid_declarations_1.cljc
  cases/test_defonce_rejects_invalid_declarations_2.cljc
  cases/test_defonce_rejects_invalid_declarations_3.cljc
  cases/test_direct_external_package_constructors_reject_bad_arity.cljc
  cases/test_direct_ocaml_constructors_reject_bad_arity_1.cljc
  cases/test_direct_ocaml_constructors_reject_bad_arity_2.cljc
  cases/test_direct_ocaml_constructors_reject_bad_arity_3.cljc
  cases/test_hash_map_rejects_odd_key_value_forms.cljc
  cases/test_include_module_rejects_bad_forms_1.cljc
  cases/test_include_module_rejects_bad_forms_2.cljc
  cases/test_module_alias_rejects_bad_forms.cljc
  cases/test_module_functors_reject_bad_forms_1.cljc
  cases/test_module_functors_reject_bad_forms_2.cljc
  cases/test_module_functors_reject_bad_forms_3.cljc
  cases/test_module_functors_reject_bad_forms_4.cljc
  cases/test_module_functors_reject_bad_forms_5.cljc
  cases/test_multi_arity_defn_rejects_invalid_declarations_1.cljc
  cases/test_multi_arity_defn_rejects_invalid_declarations_2.cljc
  cases/test_namespace_refer_clojure_exclude_hides_core_binding.cljc
  cases/test_namespace_rejects_malformed_and_repeated_forms_1.cljc
  cases/test_namespace_rejects_malformed_and_repeated_forms_2.cljc
  cases/test_namespace_rejects_malformed_and_repeated_forms_3.cljc
  cases/test_nil_type_annotation_remains_explicitly_unsupported.cljc
  cases/test_ocaml_option_and_result_constructors_reject_bad_arity_1.cljc
  cases/test_ocaml_option_and_result_constructors_reject_bad_arity_2.cljc
  cases/test_ocaml_option_and_result_constructors_reject_bad_arity_3.cljc
  cases/test_ocaml_option_and_result_constructors_reject_bad_arity_4.cljc
  cases/test_ocaml_type_application_annotations_reject_bad_forms_1.cljc
  cases/test_ocaml_type_application_annotations_reject_bad_forms_2.cljc
  cases/test_ocaml_variant_constructors_reject_bad_arity_1.cljc
  cases/test_ocaml_variant_constructors_reject_bad_arity_2.cljc
  cases/test_ocaml_variants_reject_bad_declarations_1.cljc
  cases/test_ocaml_variants_reject_bad_declarations_2.cljc
  cases/test_ocaml_variants_reject_bad_declarations_3.cljc
  cases/test_println_rejects_unknown_symbols.cljc
  cases/test_private_defn_rejects_invalid_declarations_1.cljc
  cases/test_private_defn_rejects_invalid_declarations_2.cljc
  cases/test_protocols_reject_duplicate_method_declarations.cljc
  cases/test_set_of_rejects_nil_element_annotation.cljc
  cases/test_set_of_rejects_types_without_comparators_1.cljc
  cases/test_set_of_rejects_types_without_comparators_2.cljc
  cases/test_try_and_raise_reject_malformed_forms_1.cljc
  cases/test_try_and_raise_reject_malformed_forms_2.cljc
  cases/test_try_and_raise_reject_malformed_forms_3.cljc
  cases/test_try_and_raise_reject_malformed_forms_4.cljc
  cases/test_try_and_raise_reject_malformed_forms_5.cljc
  cases/test_try_and_raise_reject_malformed_forms_6.cljc
  cases/test_variadic_signature_rejects_missing_rest_type.cljc
 )
 (action
  (run %{exe:golden_runner.bc} --outputs %{targets} --stdlib %{dep:../../stdlib/clojure/core.lgi} %{dep:../../stdlib/clojure/core.cljc} %{dep:../../stdlib/clojure/string.lgi} %{dep:../../stdlib/clojure/string.cljc} %{dep:../../stdlib/clojure/edn.lgi} %{dep:../../stdlib/clojure/edn.cljc} %{dep:../../stdlib/cljs/reader.lgi} %{dep:../../stdlib/cljs/reader.cljc} %{dep:../../stdlib/clojure/set.lgi} %{dep:../../stdlib/clojure/set.cljc} %{dep:../../stdlib/clojure/data.lgi} %{dep:../../stdlib/clojure/data.cljc} %{dep:../../stdlib/clojure/walk.lgi} %{dep:../../stdlib/clojure/walk.cljc} %{dep:../../stdlib/clojure/zip.lgi} %{dep:../../stdlib/clojure/zip.cljc} %{dep:../../stdlib/cljs/cache.cljc} %{dep:../../stdlib/cljs/pprint.lgi} %{dep:../../stdlib/cljs/pprint.cljc} %{dep:../../stdlib/cljs/test.lgi} %{dep:../../stdlib/cljs/test.cljc} --cases %{dep:cases/test_declared_protocol_methods_reject_duplicate_arity.cljc} %{dep:cases/test_defonce_rejects_invalid_declarations_1.cljc} %{dep:cases/test_defonce_rejects_invalid_declarations_2.cljc} %{dep:cases/test_defonce_rejects_invalid_declarations_3.cljc} %{dep:cases/test_direct_external_package_constructors_reject_bad_arity.cljc} %{dep:cases/test_direct_ocaml_constructors_reject_bad_arity_1.cljc} %{dep:cases/test_direct_ocaml_constructors_reject_bad_arity_2.cljc} %{dep:cases/test_direct_ocaml_constructors_reject_bad_arity_3.cljc} %{dep:cases/test_hash_map_rejects_odd_key_value_forms.cljc} %{dep:cases/test_include_module_rejects_bad_forms_1.cljc} %{dep:cases/test_include_module_rejects_bad_forms_2.cljc} %{dep:cases/test_module_alias_rejects_bad_forms.cljc} %{dep:cases/test_module_functors_reject_bad_forms_1.cljc} %{dep:cases/test_module_functors_reject_bad_forms_2.cljc} %{dep:cases/test_module_functors_reject_bad_forms_3.cljc} %{dep:cases/test_module_functors_reject_bad_forms_4.cljc} %{dep:cases/test_module_functors_reject_bad_forms_5.cljc} %{dep:cases/test_multi_arity_defn_rejects_invalid_declarations_1.cljc} %{dep:cases/test_multi_arity_defn_rejects_invalid_declarations_2.cljc} %{dep:cases/test_namespace_refer_clojure_exclude_hides_core_binding.cljc} %{dep:cases/test_namespace_rejects_malformed_and_repeated_forms_1.cljc} %{dep:cases/test_namespace_rejects_malformed_and_repeated_forms_2.cljc} %{dep:cases/test_namespace_rejects_malformed_and_repeated_forms_3.cljc} %{dep:cases/test_nil_type_annotation_remains_explicitly_unsupported.cljc} %{dep:cases/test_ocaml_option_and_result_constructors_reject_bad_arity_1.cljc} %{dep:cases/test_ocaml_option_and_result_constructors_reject_bad_arity_2.cljc} %{dep:cases/test_ocaml_option_and_result_constructors_reject_bad_arity_3.cljc} %{dep:cases/test_ocaml_option_and_result_constructors_reject_bad_arity_4.cljc} %{dep:cases/test_ocaml_type_application_annotations_reject_bad_forms_1.cljc} %{dep:cases/test_ocaml_type_application_annotations_reject_bad_forms_2.cljc} %{dep:cases/test_ocaml_variant_constructors_reject_bad_arity_1.cljc} %{dep:cases/test_ocaml_variant_constructors_reject_bad_arity_2.cljc} %{dep:cases/test_ocaml_variants_reject_bad_declarations_1.cljc} %{dep:cases/test_ocaml_variants_reject_bad_declarations_2.cljc} %{dep:cases/test_ocaml_variants_reject_bad_declarations_3.cljc} %{dep:cases/test_println_rejects_unknown_symbols.cljc} %{dep:cases/test_private_defn_rejects_invalid_declarations_1.cljc} %{dep:cases/test_private_defn_rejects_invalid_declarations_2.cljc} %{dep:cases/test_protocols_reject_duplicate_method_declarations.cljc} %{dep:cases/test_set_of_rejects_nil_element_annotation.cljc} %{dep:cases/test_set_of_rejects_types_without_comparators_1.cljc} %{dep:cases/test_set_of_rejects_types_without_comparators_2.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_1.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_2.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_3.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_4.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_5.cljc} %{dep:cases/test_try_and_raise_reject_malformed_forms_6.cljc} %{dep:cases/test_variadic_signature_rejects_missing_rest_type.cljc})))

(rule
 (alias runtest)
 (deps cases/test_declared_protocol_methods_reject_duplicate_arity.expected test_declared_protocol_methods_reject_duplicate_arity.actual)
 (action (diff cases/test_declared_protocol_methods_reject_duplicate_arity.expected test_declared_protocol_methods_reject_duplicate_arity.actual)))

(rule
 (alias runtest)
 (deps cases/test_defonce_rejects_invalid_declarations_1.expected test_defonce_rejects_invalid_declarations_1.actual)
 (action (diff cases/test_defonce_rejects_invalid_declarations_1.expected test_defonce_rejects_invalid_declarations_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_defonce_rejects_invalid_declarations_2.expected test_defonce_rejects_invalid_declarations_2.actual)
 (action (diff cases/test_defonce_rejects_invalid_declarations_2.expected test_defonce_rejects_invalid_declarations_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_defonce_rejects_invalid_declarations_3.expected test_defonce_rejects_invalid_declarations_3.actual)
 (action (diff cases/test_defonce_rejects_invalid_declarations_3.expected test_defonce_rejects_invalid_declarations_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_direct_external_package_constructors_reject_bad_arity.expected test_direct_external_package_constructors_reject_bad_arity.actual)
 (action (diff cases/test_direct_external_package_constructors_reject_bad_arity.expected test_direct_external_package_constructors_reject_bad_arity.actual)))

(rule
 (alias runtest)
 (deps cases/test_direct_ocaml_constructors_reject_bad_arity_1.expected test_direct_ocaml_constructors_reject_bad_arity_1.actual)
 (action (diff cases/test_direct_ocaml_constructors_reject_bad_arity_1.expected test_direct_ocaml_constructors_reject_bad_arity_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_direct_ocaml_constructors_reject_bad_arity_2.expected test_direct_ocaml_constructors_reject_bad_arity_2.actual)
 (action (diff cases/test_direct_ocaml_constructors_reject_bad_arity_2.expected test_direct_ocaml_constructors_reject_bad_arity_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_direct_ocaml_constructors_reject_bad_arity_3.expected test_direct_ocaml_constructors_reject_bad_arity_3.actual)
 (action (diff cases/test_direct_ocaml_constructors_reject_bad_arity_3.expected test_direct_ocaml_constructors_reject_bad_arity_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_hash_map_rejects_odd_key_value_forms.expected test_hash_map_rejects_odd_key_value_forms.actual)
 (action (diff cases/test_hash_map_rejects_odd_key_value_forms.expected test_hash_map_rejects_odd_key_value_forms.actual)))

(rule
 (alias runtest)
 (deps cases/test_include_module_rejects_bad_forms_1.expected test_include_module_rejects_bad_forms_1.actual)
 (action (diff cases/test_include_module_rejects_bad_forms_1.expected test_include_module_rejects_bad_forms_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_include_module_rejects_bad_forms_2.expected test_include_module_rejects_bad_forms_2.actual)
 (action (diff cases/test_include_module_rejects_bad_forms_2.expected test_include_module_rejects_bad_forms_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_alias_rejects_bad_forms.expected test_module_alias_rejects_bad_forms.actual)
 (action (diff cases/test_module_alias_rejects_bad_forms.expected test_module_alias_rejects_bad_forms.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_functors_reject_bad_forms_1.expected test_module_functors_reject_bad_forms_1.actual)
 (action (diff cases/test_module_functors_reject_bad_forms_1.expected test_module_functors_reject_bad_forms_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_functors_reject_bad_forms_2.expected test_module_functors_reject_bad_forms_2.actual)
 (action (diff cases/test_module_functors_reject_bad_forms_2.expected test_module_functors_reject_bad_forms_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_functors_reject_bad_forms_3.expected test_module_functors_reject_bad_forms_3.actual)
 (action (diff cases/test_module_functors_reject_bad_forms_3.expected test_module_functors_reject_bad_forms_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_functors_reject_bad_forms_4.expected test_module_functors_reject_bad_forms_4.actual)
 (action (diff cases/test_module_functors_reject_bad_forms_4.expected test_module_functors_reject_bad_forms_4.actual)))

(rule
 (alias runtest)
 (deps cases/test_module_functors_reject_bad_forms_5.expected test_module_functors_reject_bad_forms_5.actual)
 (action (diff cases/test_module_functors_reject_bad_forms_5.expected test_module_functors_reject_bad_forms_5.actual)))

(rule
 (alias runtest)
 (deps cases/test_multi_arity_defn_rejects_invalid_declarations_1.expected test_multi_arity_defn_rejects_invalid_declarations_1.actual)
 (action (diff cases/test_multi_arity_defn_rejects_invalid_declarations_1.expected test_multi_arity_defn_rejects_invalid_declarations_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_multi_arity_defn_rejects_invalid_declarations_2.expected test_multi_arity_defn_rejects_invalid_declarations_2.actual)
 (action (diff cases/test_multi_arity_defn_rejects_invalid_declarations_2.expected test_multi_arity_defn_rejects_invalid_declarations_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_namespace_refer_clojure_exclude_hides_core_binding.expected test_namespace_refer_clojure_exclude_hides_core_binding.actual)
 (action (diff cases/test_namespace_refer_clojure_exclude_hides_core_binding.expected test_namespace_refer_clojure_exclude_hides_core_binding.actual)))

(rule
 (alias runtest)
 (deps cases/test_namespace_rejects_malformed_and_repeated_forms_1.expected test_namespace_rejects_malformed_and_repeated_forms_1.actual)
 (action (diff cases/test_namespace_rejects_malformed_and_repeated_forms_1.expected test_namespace_rejects_malformed_and_repeated_forms_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_namespace_rejects_malformed_and_repeated_forms_2.expected test_namespace_rejects_malformed_and_repeated_forms_2.actual)
 (action (diff cases/test_namespace_rejects_malformed_and_repeated_forms_2.expected test_namespace_rejects_malformed_and_repeated_forms_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_namespace_rejects_malformed_and_repeated_forms_3.expected test_namespace_rejects_malformed_and_repeated_forms_3.actual)
 (action (diff cases/test_namespace_rejects_malformed_and_repeated_forms_3.expected test_namespace_rejects_malformed_and_repeated_forms_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_nil_type_annotation_remains_explicitly_unsupported.expected test_nil_type_annotation_remains_explicitly_unsupported.actual)
 (action (diff cases/test_nil_type_annotation_remains_explicitly_unsupported.expected test_nil_type_annotation_remains_explicitly_unsupported.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_option_and_result_constructors_reject_bad_arity_1.expected test_ocaml_option_and_result_constructors_reject_bad_arity_1.actual)
 (action (diff cases/test_ocaml_option_and_result_constructors_reject_bad_arity_1.expected test_ocaml_option_and_result_constructors_reject_bad_arity_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_option_and_result_constructors_reject_bad_arity_2.expected test_ocaml_option_and_result_constructors_reject_bad_arity_2.actual)
 (action (diff cases/test_ocaml_option_and_result_constructors_reject_bad_arity_2.expected test_ocaml_option_and_result_constructors_reject_bad_arity_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_option_and_result_constructors_reject_bad_arity_3.expected test_ocaml_option_and_result_constructors_reject_bad_arity_3.actual)
 (action (diff cases/test_ocaml_option_and_result_constructors_reject_bad_arity_3.expected test_ocaml_option_and_result_constructors_reject_bad_arity_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_option_and_result_constructors_reject_bad_arity_4.expected test_ocaml_option_and_result_constructors_reject_bad_arity_4.actual)
 (action (diff cases/test_ocaml_option_and_result_constructors_reject_bad_arity_4.expected test_ocaml_option_and_result_constructors_reject_bad_arity_4.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_type_application_annotations_reject_bad_forms_1.expected test_ocaml_type_application_annotations_reject_bad_forms_1.actual)
 (action (diff cases/test_ocaml_type_application_annotations_reject_bad_forms_1.expected test_ocaml_type_application_annotations_reject_bad_forms_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_type_application_annotations_reject_bad_forms_2.expected test_ocaml_type_application_annotations_reject_bad_forms_2.actual)
 (action (diff cases/test_ocaml_type_application_annotations_reject_bad_forms_2.expected test_ocaml_type_application_annotations_reject_bad_forms_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_variant_constructors_reject_bad_arity_1.expected test_ocaml_variant_constructors_reject_bad_arity_1.actual)
 (action (diff cases/test_ocaml_variant_constructors_reject_bad_arity_1.expected test_ocaml_variant_constructors_reject_bad_arity_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_variant_constructors_reject_bad_arity_2.expected test_ocaml_variant_constructors_reject_bad_arity_2.actual)
 (action (diff cases/test_ocaml_variant_constructors_reject_bad_arity_2.expected test_ocaml_variant_constructors_reject_bad_arity_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_variants_reject_bad_declarations_1.expected test_ocaml_variants_reject_bad_declarations_1.actual)
 (action (diff cases/test_ocaml_variants_reject_bad_declarations_1.expected test_ocaml_variants_reject_bad_declarations_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_variants_reject_bad_declarations_2.expected test_ocaml_variants_reject_bad_declarations_2.actual)
 (action (diff cases/test_ocaml_variants_reject_bad_declarations_2.expected test_ocaml_variants_reject_bad_declarations_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_ocaml_variants_reject_bad_declarations_3.expected test_ocaml_variants_reject_bad_declarations_3.actual)
 (action (diff cases/test_ocaml_variants_reject_bad_declarations_3.expected test_ocaml_variants_reject_bad_declarations_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_println_rejects_unknown_symbols.expected test_println_rejects_unknown_symbols.actual)
 (action (diff cases/test_println_rejects_unknown_symbols.expected test_println_rejects_unknown_symbols.actual)))

(rule
 (alias runtest)
 (deps cases/test_private_defn_rejects_invalid_declarations_1.expected test_private_defn_rejects_invalid_declarations_1.actual)
 (action (diff cases/test_private_defn_rejects_invalid_declarations_1.expected test_private_defn_rejects_invalid_declarations_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_private_defn_rejects_invalid_declarations_2.expected test_private_defn_rejects_invalid_declarations_2.actual)
 (action (diff cases/test_private_defn_rejects_invalid_declarations_2.expected test_private_defn_rejects_invalid_declarations_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_protocols_reject_duplicate_method_declarations.expected test_protocols_reject_duplicate_method_declarations.actual)
 (action (diff cases/test_protocols_reject_duplicate_method_declarations.expected test_protocols_reject_duplicate_method_declarations.actual)))

(rule
 (alias runtest)
 (deps cases/test_set_of_rejects_nil_element_annotation.expected test_set_of_rejects_nil_element_annotation.actual)
 (action (diff cases/test_set_of_rejects_nil_element_annotation.expected test_set_of_rejects_nil_element_annotation.actual)))

(rule
 (alias runtest)
 (deps cases/test_set_of_rejects_types_without_comparators_1.expected test_set_of_rejects_types_without_comparators_1.actual)
 (action (diff cases/test_set_of_rejects_types_without_comparators_1.expected test_set_of_rejects_types_without_comparators_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_set_of_rejects_types_without_comparators_2.expected test_set_of_rejects_types_without_comparators_2.actual)
 (action (diff cases/test_set_of_rejects_types_without_comparators_2.expected test_set_of_rejects_types_without_comparators_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_1.expected test_try_and_raise_reject_malformed_forms_1.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_1.expected test_try_and_raise_reject_malformed_forms_1.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_2.expected test_try_and_raise_reject_malformed_forms_2.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_2.expected test_try_and_raise_reject_malformed_forms_2.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_3.expected test_try_and_raise_reject_malformed_forms_3.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_3.expected test_try_and_raise_reject_malformed_forms_3.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_4.expected test_try_and_raise_reject_malformed_forms_4.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_4.expected test_try_and_raise_reject_malformed_forms_4.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_5.expected test_try_and_raise_reject_malformed_forms_5.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_5.expected test_try_and_raise_reject_malformed_forms_5.actual)))

(rule
 (alias runtest)
 (deps cases/test_try_and_raise_reject_malformed_forms_6.expected test_try_and_raise_reject_malformed_forms_6.actual)
 (action (diff cases/test_try_and_raise_reject_malformed_forms_6.expected test_try_and_raise_reject_malformed_forms_6.actual)))

(rule
 (alias runtest)
 (deps cases/test_variadic_signature_rejects_missing_rest_type.expected test_variadic_signature_rejects_missing_rest_type.actual)
 (action (diff cases/test_variadic_signature_rejects_missing_rest_type.expected test_variadic_signature_rejects_missing_rest_type.actual)))
