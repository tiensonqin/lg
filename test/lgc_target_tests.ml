let fail message = raise (Failure message)

let expect_ok : ('a, Lg.Compiler.compile_error) result -> 'a = function
  | Ok value -> value
  | Error error ->
      fail ("unexpected compile error: " ^ error.Lg.Compiler.message)

let expect_error expected (result : ('a, Lg.Compiler.compile_error) result) =
  match result with
  | Error error when error.Lg.Compiler.message = expected -> ()
  | Error error ->
      fail
        (Printf.sprintf "expected error %S, got %S" expected
           error.Lg.Compiler.message)
  | Ok _ -> fail ("expected compile error: " ^ expected)

let contains source expected =
  let source_length = String.length source in
  let expected_length = String.length expected in
  let rec search offset =
    offset + expected_length <= source_length
    && (String.sub source offset expected_length = expected
       || search (offset + 1))
  in
  expected_length = 0 || search 0

let assert_contains source expected =
  if not (contains source expected) then
    fail (Printf.sprintf "expected generated source to contain %S" expected)

let assert_not_contains source unexpected =
  if contains source unexpected then
    fail
      (Printf.sprintf "expected generated source not to contain %S" unexpected)

let compile target source =
  Lg.Compiler.compile_string ~target source |> expect_ok

let test_reader_discard_omits_forms () =
  let generated =
    compile Lg.Target.Native
      {|
#_(def discarded-value missing-symbol)
(def retained-values [1 #_2 3])
|}
  in
  assert_not_contains generated "discarded_value";
  assert_contains generated "retained_values";
  assert_not_contains generated "missing_symbol"

let test_selects_each_target () =
  let source =
    {|
(def environment
  #?(:native "native-value"
     :melange "melange-value"
     :js "jsoo-value"))
|}
  in
  let cases =
    [
      (Lg.Target.Native, "native-value", [ "melange-value"; "jsoo-value" ]);
      (Lg.Target.Melange, "melange-value", [ "native-value"; "jsoo-value" ]);
      (Lg.Target.Js_of_ocaml, "jsoo-value", [ "native-value"; "melange-value" ]);
    ]
  in
  List.iter
    (fun (target, selected, unselected) ->
      let generated = compile target source in
      assert_contains generated selected;
      List.iter (assert_not_contains generated) unselected)
    cases

let test_supports_top_level_nested_and_default_conditionals () =
  let source =
    {|
#?(:native (def platform-value 40)
   :default (def platform-value 0))
(def values ["first" #?(:native "native-nested" :default "default-nested")])
|}
  in
  let generated = compile Lg.Target.Native source in
  assert_contains generated "40";
  assert_contains generated "native-nested";
  assert_not_contains generated "default-nested"

let test_does_not_elaborate_unselected_branches () =
  let source =
    {|
(def value
  #?(:native 42
     :melange missing-only-on-melange
     :js missing-only-on-jsoo))
|}
  in
  ignore (compile Lg.Target.Native source)

let test_native_is_the_default_compiler_target () =
  let generated =
    Lg.Compiler.compile_string
      {|(def value #?(:native "native-default" :default "fallback-default"))|}
    |> expect_ok
  in
  assert_contains generated "native-default";
  assert_not_contains generated "fallback-default"

let test_clj_and_cljs_compatibility_features () =
  let source =
    {|
(def environment #?(:clj "clj-value" :cljs "cljs-value"))
|}
  in
  let cases =
    [
      (Lg.Target.Native, "clj-value", "cljs-value");
      (Lg.Target.Melange, "cljs-value", "clj-value");
      (Lg.Target.Js_of_ocaml, "cljs-value", "clj-value");
    ]
  in
  List.iter
    (fun (target, selected, unselected) ->
      let generated = compile target source in
      assert_contains generated selected;
      assert_not_contains generated unselected)
    cases

let test_js_names_js_of_ocaml_target () =
  (match Lg.Target.of_string "js" with
  | Ok Lg.Target.Js_of_ocaml -> ()
  | _ -> fail "expected js to select the js-of-ocaml target");
  if Lg.Target.to_string Lg.Target.Js_of_ocaml <> "js" then
    fail "expected the js-of-ocaml target name to be js";
  let generated =
    compile Lg.Target.Js_of_ocaml
      {|(def environment #?(:js "js-value" :js-of-ocaml "legacy-value"))|}
  in
  assert_contains generated "js-value";
  assert_not_contains generated "legacy-value"

let test_javascript_targets_load_clj_macro_definitions () =
  let source =
    {|
(ns compat.macros)
#?(:clj (defn- emit-value [value] value))
#?(:clj (defmacro from-clj [value] (emit-value value)))
(def answer (from-clj 42))
|}
  in
  [ Lg.Target.Melange; Lg.Target.Js_of_ocaml ]
  |> List.iter (fun target ->
         let generated = compile target source in
         assert_contains generated "42")

let test_javascript_targets_preload_self_required_macros () =
  let source =
    {|
(ns compat.self-macros
  #?(:cljs (:require-macros [compat.self-macros :refer [portable]])))
(defmacro portable [value] value)
(def answer (portable 42))
|}
  in
  [ Lg.Target.Melange; Lg.Target.Js_of_ocaml ]
  |> List.iter (fun target ->
         let generated = compile target source in
         assert_contains generated "42")

let test_rejects_invalid_reader_conditionals () =
  Lg.Compiler.compile_string ~target:Lg.Target.Native
    {|(def value #?(:native 1 :melange))|}
  |> expect_error "The :melange feature in this reader conditional has no form.";
  Lg.Compiler.compile_string ~target:Lg.Target.Native
    {|(def value #?(native 1 :default 2))|}
  |> expect_error "reader conditional feature must be a keyword";
  Lg.Compiler.compile_string ~target:Lg.Target.Native
    {|(def value #?(:native 1 :native 2))|}
  |> expect_error "duplicate reader conditional feature :native"

let test_omits_unmatched_reader_conditionals () =
  let generated =
    compile Lg.Target.Native
      {|
#?(:melange (def melange-only "melange-value"))
(def native-value "native-value")
|}
  in
  assert_contains generated "native-value";
  assert_not_contains generated "melange-value"

let test_splices_reader_conditionals_into_collections () =
  let source =
    {|
(def values [#?@(:clj ["native-splice-a" "native-splice-b"]
                   :cljs ["js-splice-a" "js-splice-b"])])
(def options {#?@(:clj [:b "native-splice-map"]
                       :cljs [:b "js-splice-map"])})
(defn #?@(:clj [^:bool selected?] :cljs [^boolean selected?])
  [value]
  value)
(def selected-value (selected? true))
(def selected-option (:b options))
|}
  in
  let generated = compile Lg.Target.Native source in
  assert_contains generated "selected";
  assert_contains generated "native-splice-a";
  assert_contains generated "native-splice-map";
  assert_not_contains generated "js-splice-a";
  assert_not_contains generated "js-splice-map"

let test_javascript_spliced_recur_marks_defn_recursive () =
  let source =
    {|
(defn normalize [^:bool value]
  (do
    #?@(:cljs [(if value (recur false) value)]
        :clj [value])))
(def answer (normalize true))
|}
  in
  [ Lg.Target.Melange; Lg.Target.Js_of_ocaml ]
  |> List.iter (fun target -> ignore (compile target source))

let test_spliced_reader_conditional_nil_splices_no_forms () =
  let source =
    {|
(def values [1 #?@(:cljs nil :clj [2 3]) 4])
|}
  in
  let native = compile Lg.Target.Native source in
  assert_contains native "2";
  assert_contains native "3";
  let melange = compile Lg.Target.Melange source in
  assert_not_contains melange "2";
  assert_not_contains melange "3"

let test_js_literals_are_single_reader_forms_in_conditionals () =
  let source =
    {|
(def value
  #?(:clj :native
     :cljs #js {}))
(def nested [#?(:clj :native-nested :cljs #js [1 2])])
|}
  in
  let native = compile Lg.Target.Native source in
  assert_contains native "native";
  let melange = compile Lg.Target.Melange source in
  assert_not_contains melange "native"

let test_metadata_forms_do_not_break_map_literals () =
  let source =
    {|
(def map-with-metadata-key {^:foo [:a 1] 17})
(def map-with-metadata-value {:a ^:foo [1 2]})
|}
  in
  ignore (compile Lg.Target.Native source);
  ignore (compile Lg.Target.Melange source)

let test_melange_host_calls_preserve_case_sensitive_members () =
  ignore
    (compile Lg.Target.Melange
       {|
(require [ocaml.Js.Json :as json])
(def result (json/parseExn "{}"))
|})

let test_ocaml_refer_preserves_external_value_types () =
  ignore
    (compile Lg.Target.Native
       {|
(require [ocaml.Stdlib :refer [max_int]])
(def answer (Stdlib.succ max_int))
|})

let expect_structured_error expected_code expected_phase = function
  | Error (error : Lg.Compiler.compile_error) ->
      if error.code <> expected_code then
        fail
          (Printf.sprintf "expected diagnostic code %s, got %s" expected_code
             error.code);
      if error.phase <> expected_phase then fail "unexpected diagnostic phase"
  | Ok _ -> fail ("expected structured compiler error " ^ expected_code)

let test_exposes_structured_error_identity () =
  Lg.Compiler.compile_string "("
  |> expect_structured_error "LG1002" `Parsing;
  Lg.Compiler.compile_string "(def value missing-symbol)"
  |> expect_structured_error "LG2003" `Semantic

let tests =
  [
    ("reader discard omits forms", test_reader_discard_omits_forms);
    ("selects each target", test_selects_each_target);
    ( "supports top-level, nested, and default conditionals",
      test_supports_top_level_nested_and_default_conditionals );
    ( "does not elaborate unselected branches",
      test_does_not_elaborate_unselected_branches );
    ( "native is the default compiler target",
      test_native_is_the_default_compiler_target );
    ( "maps :cljs to JavaScript targets and :clj to Native",
      test_clj_and_cljs_compatibility_features );
    ("names js-of-ocaml target js", test_js_names_js_of_ocaml_target);
    ( "loads :clj macro definitions for JavaScript targets",
      test_javascript_targets_load_clj_macro_definitions );
    ( "preloads self-required macros for JavaScript targets",
      test_javascript_targets_preload_self_required_macros );
    ( "omits unmatched reader conditionals",
      test_omits_unmatched_reader_conditionals );
    ( "splices reader conditionals into collections",
      test_splices_reader_conditionals_into_collections );
    ( "JavaScript spliced recur marks defn recursive",
      test_javascript_spliced_recur_marks_defn_recursive );
    ( "spliced reader conditional nil splices no forms",
      test_spliced_reader_conditional_nil_splices_no_forms );
    ( "JavaScript literals are single reader forms in conditionals",
      test_js_literals_are_single_reader_forms_in_conditionals );
    ( "metadata forms do not break map literals",
      test_metadata_forms_do_not_break_map_literals );
    ( "Melange host calls preserve case-sensitive members",
      test_melange_host_calls_preserve_case_sensitive_members );
    ( "OCaml refer preserves external value types",
      test_ocaml_refer_preserves_external_value_types );
    ( "exposes structured error identity",
      test_exposes_structured_error_identity );
    ( "rejects invalid reader conditionals",
      test_rejects_invalid_reader_conditionals );
  ]

let run () =
  List.iter
    (fun (name, run) ->
      try run ()
      with exn ->
        Printf.eprintf "FAILED: %s\n%s\n" name (Printexc.to_string exn);
        exit 1)
    tests
