open Ast
open Types
open Expression_support
module Env = Compiler_environment

type multi_arity_clause = {
  params : Ast.form;
  body_forms : Ast.form list;
  fixed_count : int;
  rest_index : int option;
  initial_arity : fn_arity;
}

type prepared_multi_arity_clause = {
  target_name : string;
  parts : Expression_support.compiled_fn_parts;
  row_param_types : string option list;
}

type prepared_multi_arity_fn = {
  clauses : prepared_multi_arity_clause list;
  expr : typed_expr;
}

let condp_counter = ref 0
let callable_set_counter = ref 0
let dynamic_case_counter = ref 0
let callable_expression_counter = ref 0
let dotimes_counter = ref 0
let doseq_counter = ref 0
let multi_arity_fn_counter = ref 0

let rec contains_source_macro scope env = function
  | FList (FSymbol ("quote" | "syntax-quote") :: _) -> false
  | FList (FSymbol "let*" :: _) -> true
  | FList (FSymbol name :: forms) ->
      Option.is_some (Env.find_macro ~scope name env)
      || Option.is_some (Env.find_inline_macro ~scope name env)
      || List.exists (contains_source_macro scope env) forms
  | FList forms | FVector forms ->
      List.exists (contains_source_macro scope env) forms
  | FMap entries ->
      List.exists
        (fun (key, value) ->
          contains_source_macro scope env key
          || contains_source_macro scope env value)
        entries
  | FSymbol _ | FCoreSymbol _ | FKeyword _ | FString _ | FRegex _ | FInt _
  | FFloat _ | FDecimal _ | FChar _ | FBool _ ->
      false

let source_type_tag_symbol scope env type_name =
  let source_symbol =
    match String.rindex_opt type_name '/' with
    | Some index ->
        let owner = String.sub type_name 0 index in
        let local_name =
          String.sub type_name (index + 1)
            (String.length type_name - index - 1)
        in
        let owner =
          Env.resolve_namespace_alias ~scope owner env
          |> Option.value ~default:owner
        in
        owner ^ "/" ^ local_name
    | None -> scope ^ "/" ^ type_name
  in
  match Resolver.lookup_record_type scope env type_name with
  | Ok _ ->
      Some
        (typed_ir (TOcaml "Lg_edn_backend.t")
           (Semantic_ir.Constructor
              ("Lg_edn_backend.Symbol", Some (Semantic_ir.String source_symbol))))
  | Error _ -> None

let rec compile_expr scope (env : Env.t) form =
  match compile_expr_unlocated scope env form with
  | Error error -> Error (Source_context.enrich_error form error)
  | Ok expression -> (
      match Source_context.find_identity form with
      | None -> Ok expression
      | Some (node_id, location) ->
          Ok
            {
              expression with
              semantic_expr =
                Semantic_ir.Located (node_id, location, expression.semantic_expr);
            })

and compile_expr_unlocated scope (env : Env.t) = function
  | FInt value ->
      let expression =
        if
          Env.target env = Target.Melange
          && (value < -2147483648 || value > 2147483647)
        then
          Semantic_ir.Apply
            ( Semantic_ir.Ident
                "Lg_runtime.Runtime_int_melange.of_float_unchecked",
              [ Semantic_ir.Float (string_of_int value ^ ".") ] )
        else Semantic_ir.Int value
      in
      Ok (typed_ir TInt expression)
  | FFloat "##Inf" ->
      Ok (typed_ir TFloat (Semantic_ir.Ident "Float.infinity"))
  | FFloat "##-Inf" ->
      Ok (typed_ir TFloat (Semantic_ir.Ident "Float.neg_infinity"))
  | FFloat "##NaN" -> Ok (typed_ir TFloat (Semantic_ir.Ident "Float.nan"))
  | FFloat value when String.contains value '/' ->
      Ok
        (typed_ir (TOcaml "Lg_runtime.Runtime_ratio.t")
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_ratio.of_string",
                [ Semantic_ir.String value ] )))
  | FFloat value -> Ok (typed_ir TFloat (Semantic_ir.Float value))
  | FDecimal value ->
      Ok
        (typed_ir (TOcaml "Lg_runtime.Runtime_decimal.t")
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_decimal.of_string",
                [ Semantic_ir.String value ] )))
  | FChar value -> Ok (typed_ir TChar (Semantic_ir.Char value))
  | FString value -> Ok (typed_ir TString (Semantic_ir.String value))
  | FRegex value ->
      Ok (typed_ir TRegex (Semantic_ir.String ("\000lg-regex:" ^ value)))
  | FBool value -> Ok (typed_ir TBool (Semantic_ir.Bool value))
  | FKeyword keyword -> Ok (typed_ir TKeyword (Semantic_ir.String keyword))
  | FSymbol "nil" -> Ok (typed_ir TNil (Semantic_ir.Constructor ("None", None)))
  | FSymbol "Long/MAX_VALUE" when Env.target env = Target.Native ->
      Ok (typed_ir TInt (Semantic_ir.Ident "Stdlib.max_int"))
  | FSymbol "Long/MIN_VALUE" when Env.target env = Target.Native ->
      Ok (typed_ir TInt (Semantic_ir.Ident "Stdlib.min_int"))
  | FSymbol "Double/MAX_VALUE" when Env.target env = Target.Native ->
      Ok (typed_ir TFloat (Semantic_ir.Float "1.7976931348623157e+308"))
  | FSymbol "Double/MIN_VALUE" when Env.target env = Target.Native ->
      Ok (typed_ir TFloat (Semantic_ir.Float "4.9e-324"))
  | FSymbol "js/undefined" when Env.target env = Target.Melange ->
      Ok (typed_ir TNil (Semantic_ir.Constructor ("None", None)))
  | FSymbol "js/Number.MAX_SAFE_INTEGER"
    when Env.target env = Target.Melange ->
      Ok
        (typed_ir TInt
           (Semantic_ir.Apply
              ( Semantic_ir.Ident
                  "Lg_runtime.Runtime_int_melange.of_float_unchecked",
                [ Semantic_ir.Float "9007199254740991." ] )))
  | FSymbol "js/Number.MIN_SAFE_INTEGER"
    when Env.target env = Target.Melange ->
      Ok
        (typed_ir TInt
           (Semantic_ir.Apply
              ( Semantic_ir.Ident
                  "Lg_runtime.Runtime_int_melange.of_float_unchecked",
                [ Semantic_ir.Float "-9007199254740991." ] )))
  | FSymbol "js/Number.MAX_VALUE" when Env.target env = Target.Melange ->
      Ok (typed_ir TFloat (Semantic_ir.Float "1.7976931348623157e+308"))
  | FSymbol "js/Number.MIN_VALUE" when Env.target env = Target.Melange ->
      Ok (typed_ir TFloat (Semantic_ir.Float "4.9e-324"))
  | FSymbol "js/Error"
    when Env.target env = Target.Melange
         || Env.target env = Target.Js_of_ocaml ->
      Ok (typed_ir TUnit Semantic_ir.Unit)
  | FSymbol name when String.length name > 1 && name.[0] = '@' ->
      let reference_name = String.sub name 1 (String.length name - 1) in
      compile_expr scope env (FList [ FSymbol "deref"; FSymbol reference_name ])
  | FSymbol name -> (
      let name = Resolver.canonical_core_binding_name scope env name in
      let name = Resolver.canonical_host_binding_name scope env name in
      match Env.find_opt (Names.scoped_key scope name) env with
      | Some { ty = TFn ([], return_ty); ocaml_name; _ }
        when is_constructor_name name ->
          let value = Semantic_ir.Constructor (ocaml_name, None) in
          let value =
            if String.contains ocaml_name '.' then value
            else Semantic_ir.Constraint (value, Types.ocaml_name return_ty)
          in
          Ok (typed_ir return_ty value)
      | Some
          {
            ty = TRef value_ty;
            ocaml_name;
            dynamically_bindable = true;
            _;
          } ->
          Ok
            (typed_ir value_ty
               (Semantic_ir.Apply
                  ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.deref",
                    [ Semantic_ir.Ident ocaml_name ] )))
      | Some binding when Option.is_some (Protocol.binding_protocol_id binding) ->
          Error.error
            ("protocol " ^ name
           ^ " is a compile-time marker and cannot be used as a runtime value")
      | Some binding ->
          Ok
            (typed_ir binding.ty
               (binding_value_expression binding))
      | None when name = "None" ->
          Ok
            (typed_ir
               (TOcaml_app ("option", [ TUnknown ]))
               (Semantic_ir.Constructor (name, None)))
      | None -> (
          match untyped_first_class_function_error name with
          | Some message -> Error.error message
          | None -> (
              match source_type_tag_symbol scope env name with
              | Some expression -> Ok expression
              | None -> (
                  match lookup_function scope env name with
                  | Ok function_ -> Ok function_
                  | Error _ -> Error.error ("unknown symbol " ^ name)))))
  | FCoreSymbol core_symbol ->
      lookup_function scope env (Ast.core_symbol_qualified_name core_symbol)
  | FVector forms -> compile_vector scope env forms
  | FMap pairs -> compile_map scope env pairs
  | FList
      (FSymbol ("dotimes" | "clojure.core/dotimes" | "cljs.core/dotimes")
      :: FVector [ FSymbol index_name; limit ] :: body_forms) ->
      incr dotimes_counter;
      let limit_name =
        "__lg_dotimes_limit_" ^ string_of_int !dotimes_counter
      in
      let loop_index_name =
        if index_name = "_" then
          "__lg_dotimes_index_" ^ string_of_int !dotimes_counter
        else index_name
      in
      let next_index =
        FList [ FSymbol "+"; FSymbol loop_index_name; FInt 1 ]
      in
      let recur = FList [ FSymbol "recur"; next_index ] in
      let body = FList (FSymbol "do" :: body_forms @ [ recur ]) in
      compile_expr scope env
        (FList
           [
             FSymbol "let";
             FVector [ FSymbol limit_name; limit ];
             FList
               [
                 FSymbol "loop";
                 FVector [ FSymbol loop_index_name; FInt 0 ];
                 FList
                   [
                     FSymbol "if";
                     FList
                       [
                         FSymbol "<";
                         FSymbol loop_index_name;
                         FSymbol limit_name;
                       ];
                     body;
                     FSymbol "nil";
                   ];
               ];
           ])
  | FList
      (FSymbol ("dotimes" | "clojure.core/dotimes" | "cljs.core/dotimes")
      :: _) ->
      Error.error "dotimes expects [name count] and optional body forms"
  | FList (FSymbol "loop" :: bindings :: body_forms) ->
      compile_loop scope env bindings body_forms
  | FList (FSymbol "recur" :: _) ->
      Error.error "recur is only valid in a loop tail position"
  | (FList (FSymbol "let*" :: _) as form) ->
      Result.bind (Macro_expander.expand_all ~scope ~compiler_env:env form)
        (compile_expr scope env)
  | FList (FSymbol "let" :: bindings :: body_forms) ->
      let forms = bindings :: body_forms in
      if
        Env.source_macros_expanded env
        || not (List.exists (contains_source_macro scope env) forms)
      then compile_let scope env bindings body_forms
      else
        Result.bind
          (Macro_expander.expand_all ~scope ~compiler_env:env
             (FList (FSymbol "let" :: forms)))
          (function
            | FList (FSymbol "let" :: expanded_bindings :: expanded_body_forms) ->
                compile_let scope env expanded_bindings expanded_body_forms
            | _ -> assert false)
  | FList (FSymbol "tag" :: FSymbol name :: payload) ->
      if not (Variant_row.valid_tag name) then Error.error "invalid polymorphic variant tag"
      else
        (match payload with
         | [] -> Ok (typed_ir (TPoly_variant {tags = [name, None]; bound = Lower_row}) (Semantic_ir.PolyTag (name, None)))
         | [payload] -> Result.map (fun (payload : typed_expr) ->
             typed_ir (TPoly_variant {tags = [name, Some payload.ty]; bound = Lower_row})
               (Semantic_ir.PolyTag (name, Some payload.semantic_expr)))
             (compile_expr scope (Env.with_expected_type None env) payload)
         | _ -> Error.error "tag expects a name and at most one payload")
  | FList [FSymbol "pack-module"; FSymbol name; FSymbol signature] ->
      Module_value_elaborator.pack name signature
  | FList (FSymbol "pack-module" :: _) ->
      Error.error "pack-module expects a module and a module signature"
  | FList (FSymbol "let-module" :: binding :: body_forms) ->
      Module_value_elaborator.unpack ~compile_expr ~compile_body scope env binding body_forms
  | FList (FSymbol "letfn" :: bindings :: body_forms) ->
      compile_letfn scope env bindings body_forms
  | FList [ FSymbol "__lg_if-let"; binding; then_form; else_form ] ->
      compile_if_let scope env binding then_form else_form
  | FList [ FSymbol "__lg_if-some"; binding; then_form; else_form ] ->
      compile_if_some scope env binding then_form else_form
  | FList [ FSymbol "__lg_some-thread"; binding; then_form ] ->
      compile_some_thread scope env binding then_form
  | FList (FSymbol "__lg_if-let" :: _) ->
      Error.error "if-let requires [name option], then, and else"
  | FList (FSymbol "__lg_if-some" :: _) ->
      Error.error "if-some requires [name option], then, and else"
  | FList (FSymbol "__lg_some-thread" :: _) ->
      Error.error "some-> requires [name option] and a threaded form"
  | FList (FSymbol "__lg_when-let" :: binding :: body_forms) ->
      compile_when_let scope env binding body_forms
  | FList (FSymbol "__lg_when-some" :: binding :: body_forms) ->
      compile_when_some scope env binding body_forms
  | FList [ FSymbol "let-some"; bindings; then_form; else_form ] ->
      compile_let_some scope env bindings then_form else_form
  | FList (FSymbol "let-some" :: _) ->
      Error.error "let-some requires bindings, then, and else"
  | FList
      (FSymbol "fn" :: FSymbol name :: (FVector _ as params) :: body_forms) ->
      compile_named_fn scope env name params body_forms
  | FList (FSymbol "fn" :: (FList _ as first_clause) :: remaining_clauses) ->
      compile_multi_arity_fn scope env (first_clause :: remaining_clauses)
  | FList (FSymbol "fn" :: params :: body_forms) ->
      compile_fn scope env params body_forms
  | FList (FSymbol "__lg_reify_fn" :: params :: body_forms) ->
      compile_fn ~use_open_context:true scope env params body_forms
  | FList (FSymbol "new" :: FSymbol type_name :: args) ->
      compile_call scope env (type_name ^ ".") args
  | FList [ FSymbol "quote"; value ] -> compile_quoted scope env value
  | FList (FSymbol "quote" :: _) -> Error.error "quote expects one form"
  | FList [ FSymbol "syntax-quote"; value ] -> compile_quoted scope env value
  | FList (FSymbol "syntax-quote" :: _) ->
      Error.error "syntax-quote expects one form"
  | FList [ FSymbol "#uuid"; FString source ] ->
      Ok
        (typed_ir (TOcaml "Lg_runtime.Runtime_uuid.t")
           (Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_uuid.of_string",
                [ Semantic_ir.String source ] )))
  | FList (FSymbol "#uuid" :: _) ->
      Error.error "#uuid expects one string literal"
  | FList [ FSymbol "#inst"; FString source ] -> (
      match Instant_literal.parse source with
      | Error message -> Error.error message
      | Ok epoch_millis ->
          Ok
            (typed_ir (TOcaml "Lg_runtime.Runtime_instant.t")
               (Semantic_ir.Apply
                  ( Semantic_ir.Ident
                      "Lg_runtime.Runtime_instant.of_epoch_millis",
                    [ Semantic_ir.Int64 epoch_millis ] ))))
  | FList (FSymbol "#inst" :: _) ->
      Error.error "#inst expects one string literal"
  | FList (FSymbol "do" :: body_forms) ->
      compile_body scope env "do requires at least one form" body_forms
  | FList [ FKeyword keyword; target ] ->
      compile_call scope env "__lg_get" [ target; FKeyword keyword ]
  | FList [ FKeyword keyword; target; default ] ->
      compile_call scope env "__lg_get"
        [ target; FKeyword keyword; default ]
  | FList (FKeyword _ :: _) -> Error.error "keyword lookup expects one argument"
  | FList [ FSymbol "if"; condition; then_form; else_form ] ->
      compile_if scope env condition then_form else_form
  | FList [ FSymbol "if"; condition; then_form ] ->
      compile_if scope env condition then_form (FSymbol "nil")
  | FList (FSymbol "condp" :: predicate :: target :: clauses) ->
      compile_condp scope env predicate target clauses
  | FList (FSymbol "case" :: target :: clauses) ->
      compile_case scope env target clauses
  | FList [ FSymbol "case" ] -> Error.error "case expects a target"
  | FList (FSymbol "__lg_doseq" :: bindings :: body_forms) ->
      compile_doseq scope env bindings body_forms
  | FList [ FSymbol "for"; bindings; body ] ->
      compile_for scope env bindings body
  | FList (FSymbol "for" :: _) ->
      Error.error "for expects a binding vector and body"
  | FList (FSymbol "__lg_logical-and" :: forms) ->
      compile_logical scope env `And forms
  | FList (FSymbol "__lg_logical-or" :: forms) ->
      compile_logical scope env `Or forms
  | FList (FSymbol "match" :: target :: clauses) ->
      compile_match scope env target clauses
  | FList (FSymbol "try" :: forms) -> compile_try scope env forms
  | FList
      [
        FList
          (FSymbol "__lg_hash-set" :: element_forms);
        key_form;
      ]
    ->
      incr callable_set_counter;
      let suffix = string_of_int !callable_set_counter in
      let key_name = "__lg_callable_set_key_" ^ suffix in
      let elements =
        List.mapi
          (fun index form ->
            ( "__lg_callable_set_element_" ^ suffix ^ "_" ^ string_of_int index,
              form ))
          element_forms
      in
      let body =
        List.fold_right
          (fun (element_name, _) otherwise ->
            FList
              [
                FSymbol "if";
                FList
                  [ FSymbol "__lg_equal"; FSymbol key_name; FSymbol element_name ];
                FSymbol element_name;
                otherwise;
              ])
          elements (FSymbol "nil")
      in
      let bindings =
        FSymbol key_name :: key_form
        :: List.concat_map (fun (name, form) -> [ FSymbol name; form ]) elements
      in
      compile_expr scope env (FList [ FSymbol "let"; FVector bindings; body ])
  | (FList (FSymbol name :: args) as form) -> (
      match Env.find_macro ~scope name env with
      | Some definition
        when not (Env.source_callable_shadowed ~scope name definition env) -> (
          match
            Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
              definition args
          with
          | Error _ as err -> err
          | Ok expanded -> compile_expr scope env expanded)
      | Some _ | None -> (
          match Env.find_inline_macro ~scope name env with
          | Some definition
            when not (Env.source_callable_shadowed ~scope name definition env)
            -> (
              match
                Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
                  definition args
              with
              | Error _ as err -> err
              | Ok expanded -> compile_expr scope env expanded)
          | Some _ | None -> compile_call scope env name args))
  | (FList (FCoreSymbol core_symbol :: args) as form) ->
      let name = Ast.core_symbol_qualified_name core_symbol in
      (match Env.find_inline_macro ~scope name env with
      | Some definition -> (
          match
            Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
              definition args
          with
          | Error _ as error -> error
          | Ok expanded -> compile_expr scope env expanded)
      | None -> compile_call scope env name args)
  | FList [] -> compile_call scope env "__lg_list" []
  | FList (function_form :: arguments) ->
      incr callable_expression_counter;
      let function_name =
        "__lg_callable_expression_" ^ string_of_int !callable_expression_counter
      in
      compile_expr scope env
        (FList
           [
             FSymbol "let";
             FVector [ FSymbol function_name; function_form ];
             FList (FSymbol function_name :: arguments);
           ])

and compile_vector scope env forms =
  (Lazy.force context).special_forms.compile_vector scope env forms

and compile_quoted scope env form =
  let share_collection result =
    Result.map
      (fun expression ->
        let digest =
          Marshal.to_string form [] ^ "\000" ^ Types.ocaml_name expression.ty
          |> Digest.string |> Digest.to_hex
          |> fun value -> String.sub value 0 12
        in
        {
          expression with
          semantic_expr =
            Semantic_ir.SharedValue
              ("__lg_quoted_" ^ digest, expression.semantic_expr);
        })
      result
  in
  match form with
  | FSymbol "nil" -> compile_expr scope env (FSymbol "nil")
  | FSymbol symbol -> Ok (typed_ir TSymbol (Semantic_ir.String symbol))
  | FVector forms ->
      share_collection
        (compile_expr scope env
           (FVector
              (List.map (fun form -> FList [ FSymbol "quote"; form ]) forms)))
  | FList forms ->
      share_collection
        (compile_expr scope env
           (FList
              (FSymbol "__lg_list"
              :: List.map (fun form -> FList [ FSymbol "quote"; form ]) forms)))
  | FMap pairs ->
      share_collection
        (compile_expr scope env
           (FMap
              (pairs
              |> List.map (fun (key, value) ->
                  ( FList [ FSymbol "quote"; key ],
                    FList [ FSymbol "quote"; value ] )))))
  | form -> compile_expr scope env form

and compile_case scope env target clauses =
  let rec grouped_pattern = function
    | [] -> FSymbol "_"
    | [ pattern ] -> pattern
    | pattern :: rest -> FList [ FSymbol "or"; pattern; grouped_pattern rest ]
  in
  let pattern = function
    | FList patterns -> grouped_pattern patterns
    | pattern -> pattern
  in
  let rec pairs acc = function
    | [] ->
        List.rev
          (FList
             [
               FSymbol "throw";
               FList
                 [ FSymbol "ex-info"; FString "No matching clause"; FMap [] ];
             ]
          :: FSymbol "_" :: acc)
    | [ default ] -> List.rev (default :: FSymbol "_" :: acc)
    | constant :: result :: rest ->
        pairs (result :: pattern constant :: acc) rest
  in
  match compile_expr scope env target with
  | Error _ as error -> error
  | Ok target_expression when Types.is_dynamic target_expression.ty ->
      incr dynamic_case_counter;
      let target_name =
        "__lg_open_case_target_" ^ string_of_int !dynamic_case_counter
      in
      let condition constant =
        let constants =
          match constant with FList forms -> forms | form -> [ form ]
        in
        match constants with
        | [] -> FBool false
        | first :: rest ->
            List.fold_left
              (fun condition constant ->
                FList
                  [
                    FSymbol "__lg_logical-or";
                    condition;
                    FList
                      [ FSymbol "__lg_equal"; FSymbol target_name; constant ];
                  ])
              (FList [ FSymbol "__lg_equal"; FSymbol target_name; first ])
              rest
      in
      let rec expand = function
        | [] ->
            FList
              [
                FSymbol "throw";
                FList
                  [ FSymbol "ex-info"; FString "No matching clause"; FMap [] ];
              ]
        | [ default ] -> default
        | constant :: result :: rest ->
            FList [ FSymbol "if"; condition constant; result; expand rest ]
      in
      compile_expr scope env
        (FList
           [
             FSymbol "let";
             FVector [ FSymbol target_name; target ];
             expand clauses;
           ])
  | Ok _ -> compile_match scope env target (pairs [] clauses)

and compile_doseq scope env bindings body_forms =
  let fresh_name label =
    let name =
      "__lg_doseq_" ^ label ^ "_" ^ string_of_int !doseq_counter
    in
    incr doseq_counter;
    name
  in
  let append_recur body recur_form =
    FList [ FSymbol "do"; body; recur_form ]
  in
  let rec form_mentions name = function
    | FSymbol candidate -> String.equal name candidate
    | FList (FSymbol ("quote" | "clojure.core/quote") :: _) -> false
    | FList forms | FVector forms -> List.exists (form_mentions name) forms
    | FMap entries ->
        List.exists
          (fun (key, value) ->
            form_mentions name key || form_mentions name value)
          entries
    | FCoreSymbol _ | FKeyword _ | FString _ | FRegex _ | FInt _ | FFloat _
    | FDecimal _ | FChar _ | FBool _ ->
        false
  in
  let rec expand recur_form = function
    | [] -> Ok (true, FList (FSymbol "do" :: body_forms @ [ FSymbol "nil" ]))
    | FKeyword ":let" :: FVector bindings :: rest ->
        Result.map
          (fun (needs_recur, body) ->
            ( needs_recur,
              FList [ FSymbol "let"; FVector bindings; body ] ))
          (expand recur_form rest)
    | FKeyword ":when" :: condition :: rest ->
        Result.bind (expand recur_form rest) (fun (needs_recur, body) ->
            match recur_form with
            | None -> Error.error "doseq modifier requires a preceding binding"
            | Some recur_form ->
                let then_form =
                  if needs_recur then append_recur body recur_form else body
                in
                Ok
                  ( false,
                    FList [ FSymbol "if"; condition; then_form; recur_form ] ))
    | FKeyword ":while" :: condition :: rest ->
        Result.bind (expand recur_form rest) (fun (needs_recur, body) ->
            match recur_form with
            | None -> Error.error "doseq modifier requires a preceding binding"
            | Some recur_form ->
                let then_form =
                  if needs_recur then append_recur body recur_form else body
                in
                Ok
                  ( false,
                    FList
                      [ FSymbol "if"; condition; then_form; FSymbol "nil" ] ))
    | FKeyword keyword :: _ ->
        Error.error ("Invalid 'doseq' keyword " ^ keyword)
    | ((FSymbol _ | FVector _ | FMap _) as pattern) :: collection :: rest ->
        let remaining_name = fresh_name "remaining" in
        let current_name = fresh_name "current" in
        let element_name = fresh_name "element" in
        let recur_form =
          FList
            [
              FSymbol "recur";
              FList [ FSymbol "__lg_next"; FSymbol current_name ];
            ]
        in
        Result.map
          (fun (needs_recur, body) ->
            let body =
              if needs_recur then append_recur body recur_form else body
            in
            let pattern =
              match pattern with
              | FSymbol name when not (form_mentions name body) -> FSymbol "_"
              | pattern -> pattern
            in
            ( true,
              FList
                [
                  FSymbol "loop";
                  FVector
                    [
                      FSymbol remaining_name;
                      FList [ FSymbol "__lg_seq"; collection ];
                    ];
                  FList
                    [
                      FSymbol "__lg_if-some";
                      FVector
                        [ FSymbol current_name; FSymbol remaining_name ];
                      FList
                        [
                          FSymbol "__lg_if-some";
                          FVector
                            [
                              FSymbol element_name;
                              FList
                                [ FSymbol "__lg_first"; FSymbol current_name ];
                            ];
                          FList
                            [
                              FSymbol "let";
                              FVector [ pattern; FSymbol element_name ];
                              body;
                            ];
                          FSymbol "nil";
                        ];
                      FSymbol "nil";
                    ];
                ] ))
          (expand (Some recur_form) rest)
    | _ -> Error.error "doseq requires binding/collection pairs"
  in
  match bindings with
  | FVector forms ->
      Result.bind (expand None forms) (fun (_needs_recur, expanded) ->
          Result.map
            (fun expression ->
              typed_ir TNil
                (Semantic_ir.Let
                   ( [ (Semantic_ir.PAny, expression.semantic_expr) ],
                     Semantic_ir.Constructor ("None", None) )))
            (compile_expr scope env expanded))
  | _ -> Error.error "doseq bindings must be a vector"

and compile_for scope env bindings body =
  let erased_seqable_parameter = function
    | FSymbol name -> (
        match Env.find_opt (Names.scoped_key scope name) env with
        | Some binding -> (
            match Types.seqable_constraint_info binding.ty with
            | Some (_, (TUnknown | TMeta _ | TVar _), (TUnknown | TMeta _ | TVar _)) -> true
            | Some _ | None -> false)
        | None -> false)
    | _ -> false
  in
  let mapper_parameters pattern collection =
    match pattern with
    | (FVector _ | FMap _) when erased_seqable_parameter collection ->
        FVector [ FSymbol "^:dynamic"; pattern ]
    | _ -> FVector [ pattern ]
  in
  let rec produces_sequence = function
    | [] -> false
    | FKeyword ":when" :: _ -> true
    | FKeyword _ :: _ :: rest -> produces_sequence rest
    | (FSymbol _ | FVector _ | FMap _) :: _ :: _ -> true
    | _ -> false
  in
  let rec expand = function
    | [] -> Ok body
    | FKeyword ":let" :: FVector bindings :: rest ->
        Result.map
          (fun body -> FList [ FSymbol "let"; FVector bindings; body ])
          (expand rest)
    | FKeyword ":when" :: condition :: rest ->
        Result.map
          (fun body ->
            let when_true =
              if produces_sequence rest then body else FVector [ body ]
            in
            FList [ FSymbol "if"; condition; when_true; FVector [] ])
          (expand rest)
    | FKeyword ":while" :: _ -> Error.error "for :while is not supported yet"
    | ((FSymbol _ | FVector _ | FMap _) as pattern) :: collection :: rest ->
        Result.map
          (fun body ->
            let mapper =
              FList
                [ FSymbol "fn"; mapper_parameters pattern collection; body ]
            in
            let function_name =
              if produces_sequence rest then "mapcat" else "map"
            in
            FList [ FSymbol function_name; mapper; collection ])
          (expand rest)
    | _ -> Error.error "for requires binding/collection pairs"
  in
  match bindings with
  | FVector forms -> (
      match expand forms with
      | Error _ as error -> error
      | Ok expanded -> compile_expr scope env expanded)
  | _ -> Error.error "for bindings must be a vector"

and compile_map scope env pairs =
  (Lazy.force context).special_forms.compile_map scope env pairs

and compile_if scope env condition then_form else_form =
  (Lazy.force context).special_forms.compile_if scope env condition then_form
    else_form

and compile_if_let scope env binding then_form else_form =
  (Lazy.force context).special_forms.compile_if_let scope env binding then_form
    else_form

and compile_if_some scope env binding then_form else_form =
  (Lazy.force context).special_forms.compile_if_some scope env binding then_form
    else_form

and compile_some_thread scope env binding then_form =
  (Lazy.force context).special_forms.compile_some_thread scope env binding
    then_form

and compile_when_let scope env binding body_forms =
  (Lazy.force context).special_forms.compile_when_let scope env binding
    body_forms

and compile_when_some scope env binding body_forms =
  (Lazy.force context).special_forms.compile_when_some scope env binding
    body_forms

and compile_let_some scope env bindings then_form else_form =
  (Lazy.force context).special_forms.compile_let_some scope env bindings
    then_form else_form

and compile_condp scope env predicate target clauses =
  incr condp_counter;
  let target_name = "__lg_condp_target_" ^ string_of_int !condp_counter in
  let rec expand = function
    | [] ->
        Ok
          (FList
             [
               FSymbol "throw";
               FList
                 [
                   FSymbol "ex-info";
                   FString "No matching clause in condp";
                   FMap [];
                 ];
             ])
    | [ default ] -> Ok default
    | test :: expression :: rest ->
        Result.map
          (fun otherwise ->
            FList
              [
                FSymbol "if";
                FList [ predicate; test; FSymbol target_name ];
                expression;
                otherwise;
              ])
          (expand rest)
  in
  Result.bind (expand clauses) (fun body ->
      compile_expr scope env
        (FList [ FSymbol "let"; FVector [ FSymbol target_name; target ]; body ]))

and compile_logical scope env operator forms =
  (Lazy.force context).special_forms.compile_logical scope env operator forms

and compile_match scope env target_form clauses =
  (Lazy.force context).special_forms.compile_match scope env target_form clauses

and compile_body scope env empty_error forms =
  (Lazy.force context).special_forms.compile_body scope env empty_error forms

and compile_try scope env forms =
  (Lazy.force context).special_forms.compile_try scope env forms

and loop_branch_type left right =
  (Lazy.force context).special_forms.loop_branch_type left right

and compile_recur scope env loop_name param_tys arg_forms =
  (Lazy.force context).special_forms.compile_recur scope env loop_name param_tys
    arg_forms

and compile_loop_tail scope env loop_name param_tys form =
  (Lazy.force context).special_forms.compile_loop_tail scope env loop_name
    param_tys form

and compile_loop_tail_body scope env loop_name param_tys forms =
  (Lazy.force context).special_forms.compile_loop_tail_body scope env loop_name
    param_tys forms

and compile_loop scope env bindings body_forms =
  (Lazy.force context).special_forms.compile_loop scope env bindings body_forms

and compile_let scope env bindings body_forms =
  (Lazy.force context).special_forms.compile_let scope env bindings body_forms

and compile_letfn scope env bindings body_forms =
  Local_function_elaborator.compile ~compile_named_fn ~compile_body
    ~prepare_recursive:(fun ~ocaml_name scope env name params body ->
      Result.map (fun parts -> fn_code parts)
        (prepare_inferred_recursive_fn_body ~ocaml_name scope env name params body))
    scope env bindings body_forms

and prepare_fn ?(param_type_overrides = []) ?(additional_inference_params = [])
    ?refine_inferred_env ?preferred_record ?(infer_parameters_only = false)
    ?variadic_rest_index
    ?(materialize_open_equality = false) ?(refine_open_overrides = false)
    ?recur_target ?expected_return_ty scope env params body_forms =
  let lookup_function_ty = lookup_function_ty scope env in
  let with_expected_return env =
    Env.with_expected_type expected_return_ty env
  in
  let compile_function_body =
    if infer_parameters_only then None
    else
    match recur_target with
    | None -> None
    | Some target_name ->
        Some
          (fun body_env param_tys forms ->
            compile_loop_tail_body scope (with_expected_return body_env)
              target_name param_tys forms)
  in
  let compile_body scope body_env empty_error forms =
    if infer_parameters_only then Ok (typed_ir TUnknown Semantic_ir.Unit)
    else
      Result.bind
        (compile_body scope (with_expected_return body_env) empty_error forms)
        (fun body ->
          match expected_return_ty with
          | None -> Ok body
          | Some expected ->
              Result.map
                (fun semantic_expr -> typed_ir expected semantic_expr)
                (Call_elaborator.plan_and_emit_argument env ~expected body))
  in
  let prepare param_type_overrides =
    let compile_default expected form =
      let adapt actual =
        Result.map
          (fun semantic_expr -> typed_ir expected semantic_expr)
          (Call_elaborator.plan_and_emit_argument env ~expected actual)
      in
      match (expected, form) with
      | TFn (parameter_tys, return_ty), FSymbol function_name ->
          let parameter_names =
            List.mapi
              (fun index _ -> "__lg_default_arg_" ^ string_of_int index)
              parameter_tys
          in
          let function_env =
            List.fold_left2
              (fun function_env name ty ->
                Env.add (Names.scoped_key scope name) (Types.binding name ty)
                  function_env)
              env parameter_names parameter_tys
          in
          let call =
            FList
              (FSymbol function_name
              :: List.map (fun name -> FSymbol name) parameter_names)
          in
          Result.bind (compile_expr scope function_env call) (fun body ->
              let return_ty =
                Types.instantiate_type ~templates:[ return_ty ]
                  ~actuals:[ body.ty ] return_ty
              in
              let function_ty = TFn (parameter_tys, return_ty) in
              Result.map
                (fun body ->
                  typed_ir function_ty
                    (Semantic_ir.Fun
                       ( List.map
                           (fun name -> Semantic_ir.PVar name)
                           parameter_names,
                         body )))
                (Call_elaborator.plan_and_emit_argument env ~expected:return_ty
                   body))
      | _ ->
          Result.bind
            (compile_expr scope (Env.with_expected_type (Some expected) env) form)
            adapt
    in
    Function_elaborator.prepare ~param_type_overrides
      ~additional_inference_params ?refine_inferred_env ?preferred_record
      ?variadic_rest_index
      ~materialize_open_equality ~refine_open_overrides ?compile_function_body
      ~lookup_function_ty ~compile_default ~compile_body scope env params
      body_forms
  in
  Result.bind (prepare param_type_overrides) (fun parts ->
      let record_values = Option.value parts.body.record_values ~default:[] in
      let refined = ref false in
      let param_type_overrides =
        parts.param_bindings
        |> List.mapi (fun index (_key, (binding : binding)) ->
               match List.nth_opt param_type_overrides index with
               | Some (Some ty) when not (Types.equal ty TUnknown) ->
                   if refine_open_overrides then (
                     if not (Types.equal ty binding.ty) then refined := true;
                     Some binding.ty)
                   else Some ty
               | _ -> (
                   match
                     List.find_opt
                       (fun (_field, value) ->
                         match Semantic_ir.unlocated value with
                         | Semantic_ir.Ident name -> name = binding.ocaml_name
                         | _ -> false)
                       record_values
                   with
                   | None -> None
                   | Some (field, _) ->
                       refined := true;
                       Some field.ty))
      in
      if !refined then prepare param_type_overrides else Ok parts)

and vector_rest_bindings rest_name = function
  | FVector forms -> (
      match Destructure.parse_sequence_pattern forms with
      | Error _ as error -> error
      | Ok pattern ->
          let rest_form = FSymbol rest_name in
          let item_bindings =
            pattern.item_patterns
            |> List.mapi (fun index item_pattern ->
                   let sequence =
                     if index = 0 then rest_form
                     else
                       FList
                         [ FSymbol "drop"; FInt index; rest_form ]
                   in
                   [ item_pattern; FList [ FSymbol "__lg_first"; sequence ] ])
            |> List.concat
          in
          let rest_bindings =
            match pattern.rest_name with
            | None -> []
            | Some name ->
                [
                  FSymbol name;
                  FList
                    [
                      FSymbol "drop";
                      FInt (List.length pattern.item_patterns);
                      rest_form;
                    ];
                ]
          in
          let as_bindings =
            match pattern.sequence_as_name with
            | None -> []
            | Some name -> [ FSymbol name; rest_form ]
          in
          Ok (item_bindings @ rest_bindings @ as_bindings))
  | _ -> Error.error "variadic rest destructuring expects a vector"

and parse_multi_arity_clauses source_name forms =
  let rec parse_clause = function
    | FList (FVector raw_params :: body_forms) when body_forms <> [] -> (
        let rec split fixed = function
          | [] -> Ok (List.rev fixed, None, None)
          | FSymbol "&" :: [ (FSymbol _ as rest) ] ->
              Ok (List.rev fixed, Some [ rest ], None)
          | FSymbol "&" :: [ FSymbol annotation; (FSymbol _ as rest) ]
            when String.starts_with ~prefix:"^:" annotation ->
              Ok (List.rev fixed, Some [ FSymbol annotation; rest ], None)
          | FSymbol "&" :: [ (FVector _ as rest_pattern) ] ->
              Result.map
                (fun bindings ->
                  ( List.rev fixed,
                    Some [ FSymbol "__lg_vector_rest" ],
                    Some bindings ))
                (vector_rest_bindings "__lg_vector_rest" rest_pattern)
          | FSymbol "&" :: [ FSymbol annotation; (FVector _ as rest_pattern) ]
            when String.starts_with ~prefix:"^:" annotation ->
              Result.map
                (fun bindings ->
                  ( List.rev fixed,
                    Some [ FSymbol annotation; FSymbol "__lg_vector_rest" ],
                    Some bindings ))
                (vector_rest_bindings "__lg_vector_rest" rest_pattern)
          | FSymbol "&" :: [ (FMap _ as rest_pattern) ] ->
              (* kwargs-style rest: [& {:as args}] binds the rest seq as a
                 map, compiled as (apply hash-map rest) *)
              Ok
                ( List.rev fixed,
                  Some [ FSymbol "__lg_kwargs_rest" ],
                  Some
                    [ rest_pattern;
                      FList
                        [
                          FSymbol "apply";
                          FSymbol "hash-map";
                          FSymbol "__lg_kwargs_rest";
                        ] ] )
          | FSymbol "&" :: [ FSymbol annotation; (FMap _ as rest_pattern) ]
            when String.starts_with ~prefix:"^:" annotation ->
              Ok
                ( List.rev fixed,
                  Some [ FSymbol annotation; FSymbol "__lg_kwargs_rest" ],
                  Some
                    [ rest_pattern;
                      FList
                        [
                          FSymbol "apply";
                          FSymbol "hash-map";
                          FSymbol "__lg_kwargs_rest";
                        ] ] )
          | FSymbol "&" :: _ ->
              Error.error
                ("defn " ^ source_name
               ^ " variadic arity requires one rest parameter")
          | form :: rest -> split (form :: fixed) rest
        in
        match split [] raw_params with
        | Error _ as err -> err
        | Ok (fixed_forms, rest_forms, rest_binding) -> (
            let body_forms =
              match rest_binding with
              | None -> body_forms
              | Some bindings ->
                  [
                    FList
                      (FSymbol "let"
                      :: FVector bindings
                      :: body_forms);
                  ]
            in
            let fixed_params = FVector fixed_forms in
            match Destructure.parse_param_specs fixed_params with
            | Error _ as err -> err
            | Ok fixed_specs -> (
                let fixed_count = List.length fixed_specs in
                let params =
                  FVector (fixed_forms @ Option.value rest_forms ~default:[])
                in
                match Destructure.parse_param_specs params with
                | Error _ as err -> err
                | Ok specs ->
                    let rest_index =
                      Option.map (fun _ -> fixed_count) rest_forms
                    in
                    let fixed_param_tys =
                      List.map
                        (fun (spec : Destructure.param_spec) ->
                          Option.value spec.explicit_ty ~default:TUnknown)
                        fixed_specs
                    in
                    let explicit_rest_ty =
                      match rest_index with
                      | None -> None
                      | Some index -> (
                          match List.nth_opt specs index with
                          | None -> None
                          | Some (spec : Destructure.param_spec) ->
                              spec.explicit_ty)
                    in
                    Ok
                      {
                        params;
                        body_forms;
                        fixed_count;
                        rest_index;
                        initial_arity =
                          {
                            fixed_params = fixed_param_tys;
                            rest_param =
                              Option.map
                                (fun _ ->
                                  Option.value explicit_rest_ty
                                    ~default:TUnknown)
                                rest_index;
                            return_ty = TUnknown;
                          };
                      })))
    | FList [ (FVector _ as params_form) ] ->
        parse_clause (FList [ params_form; FSymbol "nil" ])
    | _ ->
        Error.error
          ("defn " ^ source_name
         ^ " multi-arity clauses must contain a parameter vector and body")
  in
  let rec parse acc = function
    | [] -> Ok (List.rev acc)
    | form :: rest -> (
        match parse_clause form with
        | Error _ as err -> err
        | Ok clause -> parse (clause :: acc) rest)
  in
  match parse [] forms with
  | Error _ as err -> err
  | Ok clauses ->
      let rec validate seen_fixed seen_variadic = function
        | [] -> Ok clauses
        | clause :: rest -> (
            match clause.rest_index with
            | None ->
                if seen_variadic then
                  Error.error
                    ("defn " ^ source_name ^ " variadic arity must be last")
                else if List.mem clause.fixed_count seen_fixed then
                  Error.error
                    ("defn " ^ source_name ^ " has duplicate arity "
                   ^ string_of_int clause.fixed_count)
                else validate (clause.fixed_count :: seen_fixed) false rest
            | Some _ ->
                if seen_variadic then
                  Error.error
                    ("defn " ^ source_name ^ " has multiple variadic arities")
                else if rest <> [] then
                  Error.error
                    ("defn " ^ source_name ^ " variadic arity must be last")
                else validate seen_fixed true rest)
      in
      validate [] false clauses

and multi_arity_target_name ocaml_name index (arity : fn_arity) =
  let kind =
    match arity.rest_param with None -> "arity" | Some _ -> "variadic"
  in
  ocaml_name ^ "__" ^ kind ^ "_"
  ^ string_of_int (List.length arity.fixed_params)
  ^ "_" ^ string_of_int index

and multi_arity_value targets =
  match targets with
  | [] -> Semantic_ir.Unit
  | target :: rest ->
      Semantic_ir.Tuple [ Semantic_ir.Ident target; multi_arity_value rest ]

and prepare_multi_arity_fn ?(infer_state_return = false) ?signature ~ocaml_name
    scope env source_name forms =
  match parse_multi_arity_clauses source_name forms with
  | Error _ as err -> err
  | Ok parsed_clauses ->
      let initial_arities =
        let resolve =
          Function_elaborator.infer_named_record scope env
        in
        List.map
          (fun clause ->
            {
              fixed_params =
                List.map resolve clause.initial_arity.fixed_params;
              rest_param = Option.map resolve clause.initial_arity.rest_param;
              return_ty = resolve clause.initial_arity.return_ty;
            })
          parsed_clauses
      in
      let declared_matches_clause declared clause =
        List.length declared.fixed_params = clause.fixed_count
        &&
        match (declared.rest_param, clause.rest_index) with
        | None, None -> true
        | Some _, Some _ -> true
        | None, Some _ | Some _, None -> false
      in
      let parsed_clauses, initial_arities =
        match signature with
        | None -> (parsed_clauses, initial_arities)
        | Some declared
          when List.length declared = List.length initial_arities
               && List.for_all2
                    (fun declared inferred ->
                      List.length declared.fixed_params
                        = List.length inferred.fixed_params
                      && Option.equal
                           (fun _ _ -> true)
                           declared.rest_param inferred.rest_param)
                    declared initial_arities ->
            (parsed_clauses, declared)
        | Some declared -> (
            let expanded_clauses =
              declared
              |> List.map (fun arity ->
                     parsed_clauses
                     |> List.find_opt (declared_matches_clause arity))
            in
            match
              List.fold_right
                (fun clause acc ->
                  match (clause, acc) with
                  | Some clause, Some clauses -> Some (clause :: clauses)
                  | None, _ | _, None -> None)
                expanded_clauses (Some [])
            with
            | Some expanded_clauses -> (expanded_clauses, declared)
            | None ->
                failwith
                  ("sidecar overload signature does not match function "
                 ^ source_name))
      in
      let targets =
        List.mapi
          (fun index arity -> multi_arity_target_name ocaml_name index arity)
          initial_arities
      in
      let all_targets = targets in
      let minimum_fixed_count =
        parsed_clauses
        |> List.map (fun clause -> clause.fixed_count)
        |> List.fold_left min max_int
      in
      let rec form_conjoins name = function
        | FList (FSymbol "__lg_conj" :: FSymbol target :: _)
          when target = name ->
            true
        | FList forms | FVector forms -> List.exists (form_conjoins name) forms
        | FMap pairs ->
            List.exists
              (fun (key, value) ->
                form_conjoins name key || form_conjoins name value)
              pairs
        | _ -> false
      in
      let compatible_state_type expected actual =
        Types.assignable ~policy:Host_boundary ~expected ~actual
        && Types.assignable ~policy:Host_boundary ~expected:actual
             ~actual:expected
      in
      let clause_state_return_ty (clause : multi_arity_clause) arity =
        match
          ( Destructure.parse_param_specs clause.params,
            arity.fixed_params )
        with
        | Ok (first_spec :: _), ((TRecord _ | TNamed_record _) as first_ty) :: _ ->
            let rec calls_state_transformer = function
              | FList (FSymbol name :: FSymbol argument :: _)
                when argument = first_spec.source_name -> (
                  match lookup_function_ty scope env name with
                  | Ok (TFn (parameter_ty :: _, return_ty)) ->
                      compatible_state_type first_ty parameter_ty
                      && compatible_state_type first_ty return_ty
                  | Ok _ | Error _ -> false)
              | FList forms | FVector forms ->
                  List.exists calls_state_transformer forms
              | FMap pairs ->
                  List.exists
                    (fun (key, value) ->
                      calls_state_transformer key
                      || calls_state_transformer value)
                    pairs
              | _ -> false
            in
            if List.exists calls_state_transformer clause.body_forms then
              Some first_ty
            else None
        | (Ok _ | Error _), _ -> None
      in
      let arity_equal left right =
        List.length left.fixed_params = List.length right.fixed_params
        && List.for_all2 Types.equal left.fixed_params right.fixed_params
        && Option.equal Types.equal left.rest_param right.rest_param
        && Types.equal left.return_ty right.return_ty
      in
      let rec compile pass state_return_ty starting_arities compiled arities
          clauses remaining_targets =
        match (clauses, remaining_targets) with
        | [], [] ->
            let clauses = List.rev compiled in
            let arity_for_count count =
              arities
              |> List.find_opt (fun (arity : fn_arity) ->
                     match arity.rest_param with
                     | None -> List.length arity.fixed_params = count
                     | Some _ -> List.length arity.fixed_params <= count)
            in
            let arities =
              List.map2
                (fun (parsed : multi_arity_clause) arity ->
                  match parsed.body_forms with
                  | [ FList (FSymbol name :: arguments) ]
                    when name = source_name
                         || name = Names.scoped_key scope source_name -> (
                      match arity_for_count (List.length arguments) with
                      | Some target ->
                          { arity with return_ty = target.return_ty }
                      | None -> arity)
                  | _ -> arity)
                parsed_clauses arities
            in
            let known_call name =
              name = source_name
              || name = Names.scoped_key scope source_name
              || Result.is_ok (lookup_function_ty scope env name)
              || Option.is_some (Protocol.lookup_marker scope env name)
            in
            let fold_lefti fn initial values =
              let rec loop index acc = function
                | [] -> acc
                | value :: rest -> loop (index + 1) (fn acc index value) rest
              in
              loop 0 initial values
            in
            let rec nil_call_slots acc = function
              | FList (FSymbol name :: arguments)
                when known_call name ->
                  let acc =
                    fold_lefti
                      (fun acc argument_index -> function
                        | FSymbol "nil" -> (name, argument_index) :: acc
                        | _ -> acc)
                      acc arguments
                  in
                  List.fold_left nil_call_slots acc arguments
              | FList forms | FVector forms ->
                  List.fold_left nil_call_slots acc forms
              | FMap pairs ->
                  List.fold_left
                    (fun acc (key, value) ->
                      nil_call_slots (nil_call_slots acc key) value)
                    acc pairs
              | _ -> acc
            in
            let nullable_call_slots =
              List.fold_left
                (fun acc (clause : multi_arity_clause) ->
                  List.fold_left nil_call_slots acc clause.body_forms)
                [] parsed_clauses
              |> List.sort_uniq compare
            in
            let self_call name =
              name = source_name || name = Names.scoped_key scope source_name
            in
            let arity_index_for_count count =
              let rec find index = function
                | [] -> None
                | (arity : fn_arity) :: rest ->
                    let matches =
                      match arity.rest_param with
                      | None -> List.length arity.fixed_params = count
                      | Some _ -> List.length arity.fixed_params <= count
                    in
                    if matches then Some index else find (index + 1) rest
              in
              find 0 arities
            in
            let rec direct_nullable_parameters acc = function
              | FList (FSymbol name :: arguments) when self_call name ->
                  let acc =
                    match arity_index_for_count (List.length arguments) with
                    | None -> acc
                    | Some target_arity_index ->
                        fold_lefti
                          (fun acc parameter_index -> function
                            | FSymbol "nil" ->
                                (target_arity_index, parameter_index) :: acc
                            | _ -> acc)
                          acc arguments
                  in
                  List.fold_left direct_nullable_parameters acc arguments
              | FList forms | FVector forms ->
                  List.fold_left direct_nullable_parameters acc forms
              | FMap pairs ->
                  List.fold_left
                    (fun acc (key, value) ->
                      direct_nullable_parameters
                        (direct_nullable_parameters acc key)
                        value)
                    acc pairs
              | _ -> acc
            in
            let rec forwarded_nullable_parameters specs arity_index acc =
              function
              | FList (FSymbol name :: arguments) when known_call name ->
                  let acc =
                    fold_lefti
                      (fun acc argument_index -> function
                        | FSymbol parameter_name
                          when List.mem (name, argument_index)
                                 nullable_call_slots -> (
                            match
                              List.find_index
                                (fun (spec : Destructure.param_spec) ->
                                  spec.source_name = parameter_name)
                                specs
                            with
                            | Some parameter_index ->
                                (arity_index, parameter_index) :: acc
                            | None -> acc)
                        | _ -> acc)
                      acc arguments
                  in
                  List.fold_left
                    (forwarded_nullable_parameters specs arity_index)
                    acc arguments
              | FList forms | FVector forms ->
                  List.fold_left
                    (forwarded_nullable_parameters specs arity_index)
                    acc forms
              | FMap pairs ->
                  List.fold_left
                    (fun acc (key, value) ->
                      forwarded_nullable_parameters specs arity_index
                        (forwarded_nullable_parameters specs arity_index acc
                           key)
                        value)
                    acc pairs
              | _ -> acc
            in
            let nullable_parameters =
              let forwarded =
                parsed_clauses
                |> List.mapi (fun arity_index clause ->
                       match Destructure.parse_param_specs clause.params with
                       | Error _ -> []
                       | Ok specs ->
                           List.fold_left
                             (forwarded_nullable_parameters specs arity_index)
                             [] clause.body_forms)
                |> List.concat
              in
              List.fold_left
                (fun acc (clause : multi_arity_clause) ->
                  List.fold_left direct_nullable_parameters acc
                    clause.body_forms)
                forwarded parsed_clauses
            in
            let arities =
              List.mapi
                (fun arity_index (arity : fn_arity) ->
                  let nullable_indices =
                    nullable_parameters
                    |> List.filter_map (fun (candidate_arity, parameter_index) ->
                           if candidate_arity = arity_index then
                             Some parameter_index
                           else None)
                    |> List.sort_uniq Int.compare
                  in
                  List.fold_left
                    (fun (arity : fn_arity) parameter_index ->
                      match List.nth_opt arity.fixed_params parameter_index with
                      | None
                      | Some (TNullable _)
                      | Some (TOcaml_app ("option", [ _ ])) ->
                          arity
                      | Some ((TMeta _ | TVar _) as inferred_ty)
                        when Option.is_none signature ->
                          let payload_ty = Type_solver.fresh () in
                          let substitutions =
                            match inferred_ty with
                            | TMeta { id; _ } ->
                                Type_solver.of_list
                                  [
                                    ( Type_solver.Metavariable id,
                                      TNullable payload_ty );
                                  ]
                            | TVar name ->
                                Type_solver.of_list
                                  [
                                    ( Type_solver.Declared name,
                                      TNullable payload_ty );
                                  ]
                            | _ -> assert false
                          in
                          {
                            fixed_params =
                              List.mapi
                                (fun index ty ->
                                  if index = parameter_index then
                                    TNullable payload_ty
                                  else Type_solver.apply substitutions ty)
                                arity.fixed_params;
                            rest_param =
                              Option.map
                                (Type_solver.apply substitutions)
                                arity.rest_param;
                            return_ty =
                              Type_solver.apply substitutions arity.return_ty;
                          }
                      | Some ty ->
                          {
                            arity with
                            fixed_params =
                              List.mapi
                                (fun index candidate ->
                                  if index = parameter_index then TNullable ty
                                  else candidate)
                                arity.fixed_params;
                          })
                    arity nullable_indices)
                arities
            in
            if pass = 0 then
              let state_return_ty =
                if infer_state_return then
                  List.map2 clause_state_return_ty parsed_clauses arities
                  |> List.find_map Fun.id
                else None
              in
              let arities =
                match state_return_ty with
                | None -> arities
                | Some return_ty ->
                    List.map
                      (fun arity -> { arity with return_ty })
                      arities
              in
              compile 1 state_return_ty arities [] arities parsed_clauses
                all_targets
            else if
              pass < 4
              && not (List.for_all2 arity_equal starting_arities arities)
            then
              compile (pass + 1) state_return_ty arities [] arities
                parsed_clauses all_targets
            else
              let ty = TOverloaded_fn arities in
              Ok
                {
                  clauses;
                  expr =
                    typed_ir ty
                      (multi_arity_value
                         (List.map (fun c -> c.target_name) clauses));
                }
        | clause :: rest, target_name :: rest_targets -> (
            let overload_row_param_types =
              List.map2
                (fun target arity ->
                  row_param_type_names target arity.fixed_params)
                all_targets arities
            in
            let self_binding =
              Types.binding ~overload_targets:all_targets
                ~overload_row_param_types ocaml_name (TOverloaded_fn arities)
            in
            let clause_env =
              Env.add (Names.scoped_key scope source_name) self_binding env
            in
            let current_arity = List.nth arities (List.length compiled) in
            let param_type_overrides =
              let params =
                match clause.params with FVector params -> params | _ -> []
              in
              List.mapi
                (fun index param ->
                  match clause.rest_index with
                  | Some rest_index when index = rest_index -> (
                      match
                        (List.nth arities (List.length compiled)).rest_param
                      with
                      | Some TUnknown | None -> None
                      | Some element_ty -> Some (TSeq element_ty))
                  | _ -> (
                      match List.nth_opt current_arity.fixed_params index with
                      | Some ty
                        when Option.is_some signature
                             || not
                               (match ty with
                               | TUnknown | TMeta _ | TVar _ -> true
                               | _ -> false) ->
                          Some ty
                      | _ -> (
                          match param with
                          | FSymbol name
                            when index >= minimum_fixed_count
                                 && List.exists (form_conjoins name)
                                      clause.body_forms ->
                              Some (Types.dynamic_constraint TUnknown)
                          | _ -> None)))
                params
            in
            let expected_return_ty =
              match signature with
              | Some _ -> Some current_arity.return_ty
              | None -> if pass > 0 then state_return_ty else None
            in
            match
              prepare_fn ~param_type_overrides ~materialize_open_equality:true
                ?variadic_rest_index:clause.rest_index ~recur_target:target_name
                ?expected_return_ty scope clause_env clause.params
                clause.body_forms
            with
            | Error _ as err -> err
            | Ok prepared_parts ->
                let prepared_parts =
                  match expected_return_ty with
                  | None -> Ok prepared_parts
                  | Some return_ty ->
                      Result.map
                        (fun semantic_expr ->
                          {
                            prepared_parts with
                            body = typed_ir return_ty semantic_expr;
                          })
                        (Call_elaborator.plan_and_emit_argument clause_env
                           ~expected:return_ty prepared_parts.body)
                in
                Result.bind prepared_parts (fun parts ->
                let param_tys =
                  List.map
                    (fun (_key, (binding : binding)) -> binding.ty)
                    parts.param_bindings
                in
                let fixed_params, rest_param =
                  match clause.rest_index with
                  | None -> (param_tys, None)
                  | Some index ->
                      let fixed =
                        List.filteri
                          (fun current _ -> current < index)
                          param_tys
                      in
                      let rest =
                        match List.nth param_tys index with
                        | TSeq element_ty -> element_ty
                        | ty -> ty
                      in
                      (fixed, Some rest)
                in
                let return_ty =
                  match (fn_code parts).ty with
                  | TFn (_, return_ty) -> return_ty
                  | _ -> parts.body.ty
                in
                let arity =
                  { fixed_params; rest_param; return_ty }
                in
                let current_index = List.length compiled in
                let arities =
                  List.mapi
                    (fun index current ->
                      if index = current_index then arity else current)
                    arities
                in
                let nullable_row_indices =
                  match Destructure.parse_param_specs clause.params with
                  | Error _ -> []
                  | Ok specs ->
                      specs
                      |> List.mapi (fun index spec ->
                           if spec.Destructure.destructured then Some index
                           else None)
                      |> List.filter_map Fun.id
                in
                let row_param_types =
                  row_param_type_names ~nullable_row_indices target_name
                    param_tys
                in
                compile pass state_return_ty starting_arities
                  ({ target_name; parts; row_param_types } :: compiled)
                  arities rest rest_targets))
        | _ -> Error.error "internal error: multi-arity clause targets"
      in
      compile 0 None initial_arities [] initial_arities parsed_clauses targets

and lower_prepared_multi_arity (prepared : prepared_multi_arity_fn) =
  let targets = List.map (fun clause -> clause.target_name) prepared.clauses in
  let overload_row_param_types =
    List.map (fun clause -> clause.row_param_types) prepared.clauses
  in
  let row_items =
    List.concat_map
      (fun clause ->
        let param_tys =
          List.map
            (fun (_key, (binding : binding)) -> binding.ty)
            clause.parts.param_bindings
        in
        row_type_items clause.row_param_types param_tys)
      prepared.clauses
  in
  let recursive_bindings =
    List.map
      (fun clause ->
        let expression =
          fn_code ~row_param_type_names:clause.row_param_types clause.parts
        in
        ({
           name = clause.target_name;
           identity = None;
           type_annotation = None;
           expression = expression.semantic_expr;
         }
          : Lowered.recursive_value))
      prepared.clauses
  in
  (targets, overload_row_param_types, row_items, recursive_bindings)

and prepare_recursive_fn ~ocaml_name scope env source_name return_ty params
    body_forms =
  match Destructure.parse_param_specs params with
  | Error _ as err -> err
  | Ok specs -> (
      let declared_param_tys =
        match Env.find_opt (Names.scoped_key scope source_name) env with
        | Some { ty = TFn (param_tys, _); _ }
          when List.length param_tys = List.length specs ->
            Some param_tys
        | Some _ | None -> None
      in
      let explicit_param_tys =
        List.mapi
          (fun index (spec : Destructure.param_spec) ->
            match spec.explicit_ty with
            | Some explicit ->
                let explicit =
                  Function_elaborator.infer_named_record scope env explicit
                in
                let declared =
                  Option.bind declared_param_tys (fun tys ->
                      List.nth_opt tys index)
                in
                (match (explicit, declared) with
                | TNamed_record explicit_record,
                  Some (TNamed_record declared_record as declared)
                  when Type_id.equal explicit_record.type_id
                         declared_record.type_id ->
                    Some declared
                | _ -> Some explicit)
            | None -> Option.bind declared_param_tys (fun tys -> List.nth_opt tys index))
          specs
      in
      if List.exists Option.is_none explicit_param_tys then
        Error.error "recursive defn parameters require type annotations"
      else
        let param_tys = List.map Option.get explicit_param_tys in
        let self_binding =
          Types.binding ocaml_name (TFn (param_tys, return_ty))
          |> Types.generalize_binding
        in
        let env =
          Env.add (Names.scoped_key scope source_name) self_binding env
          |> Env.add ocaml_name self_binding
        in
        match
          prepare_fn
            ~param_type_overrides:(List.map Option.some param_tys)
            ~expected_return_ty:return_ty
            scope env params body_forms
        with
        | Error _ as err -> err
        | Ok parts ->
            if
              Types.assignable ~policy:Host_boundary ~expected:return_ty
                ~actual:parts.body.ty
            then
              Result.map
                (fun semantic_expr ->
                  { parts with body = typed_ir return_ty semantic_expr })
                (Call_elaborator.plan_and_emit_argument env ~expected:return_ty
                   parts.body)
            else
              Error.error
                ("recursive defn " ^ source_name ^ " must return "
                ^ Types.source_name return_ty))

and prepare_inferred_recursive_fn_body ?explicit_return_ty ~ocaml_name scope env
    source_name params body_forms =
  match Macro_expander.expand_all_forms ~scope ~compiler_env:env body_forms with
  | Error _ as error -> error
  | Ok body_forms -> (
  match Destructure.parse_param_specs params with
  | Error _ as err -> err
  | Ok specs -> (
      let recursion_parameter_tys =
        List.map
          (fun (spec : Destructure.param_spec) ->
            Option.value spec.explicit_ty ~default:(Type_solver.fresh ()))
          specs
      in
      let recursion_params =
        List.map2
          (fun (spec : Destructure.param_spec) ty ->
            (spec.source_name, ty))
          specs recursion_parameter_tys
      in
      let rec contains_polymorphic_self_call = function
        | FList (FSymbol name :: arguments)
          when (name = source_name
               || name = Names.scoped_key scope source_name)
               && List.length arguments = List.length recursion_parameter_tys ->
            let actual_tys =
              List.map
                (fun argument ->
                  Type_inference.returned_vector_type recursion_params argument
                  |> Option.value
                       ~default:
                         (Type_inference.inferred_form_type recursion_params
                            argument))
                arguments
            in
            let result =
              List.fold_left2
                (fun result expected actual ->
                  Result.bind result (fun substitutions ->
                      if Types.equal actual TUnknown then Ok substitutions
                      else Type_solver.unify substitutions expected actual))
                (Ok Type_solver.empty) recursion_parameter_tys actual_tys
            in
            (match result with
            | Error conflict -> Type_solver.conflict_is_occurs conflict
            | Ok _ ->
                List.exists contains_polymorphic_self_call arguments)
        | FList (FSymbol "fn" :: _) -> false
        | FList forms | FVector forms ->
            List.exists contains_polymorphic_self_call forms
        | FMap pairs ->
            List.exists
              (fun (key, value) ->
                contains_polymorphic_self_call key
                || contains_polymorphic_self_call value)
              pairs
        | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _
        | FBool _
        | FKeyword _ | FSymbol _ | FCoreSymbol _ ->
            false
      in
      if List.exists contains_polymorphic_self_call body_forms then
        Error.error
          (source_name
         ^ ": polymorphic recursion requires an explicit signature")
      else
      let predeclared_type =
        Env.find_opt (Names.scoped_key scope source_name) env
        |> Option.map (fun (binding : binding) -> binding.ty)
      in
      let predeclared_param_tys, predeclared_return_ty =
        match predeclared_type with
        | Some (TFn (parameter_tys, return_ty))
          when List.length parameter_tys = List.length specs ->
            (Some parameter_tys, Some return_ty)
        | Some _ | None -> (None, None)
      in
      let param_type_overrides =
        List.map (fun (spec : Destructure.param_spec) -> spec.explicit_ty) specs
      in
      let param_tys =
        List.mapi
          (fun index (spec : Destructure.param_spec) ->
            match spec.explicit_ty with
            | Some ty -> ty
            | None ->
                Option.bind predeclared_param_tys (fun types ->
                    List.nth_opt types index)
                |> Option.value ~default:(Type_solver.fresh ()))
          specs
        |> List.map (Function_elaborator.infer_named_record scope env)
      in
      let self_return_ty =
        match explicit_return_ty with
        | Some ty -> ty
        | None ->
            Option.value predeclared_return_ty
              ~default:(Type_solver.fresh ())
      in
      let self_binding =
        Types.binding ocaml_name (TFn (param_tys, self_return_ty))
      in
      let provisional_env =
        Env.add (Names.scoped_key scope source_name) self_binding env
      in
      let inference_params =
        List.combine specs param_tys
        |> List.fold_left
             (fun params ((spec : Destructure.param_spec), ty) ->
               let params = (spec.source_name, ty) :: params in
               if spec.destructured then
                 Destructure.pattern_names spec.pattern
                 |> List.fold_left
                      (fun params name -> (name, TUnknown) :: params)
                      params
               else params)
             []
        |> List.rev
      in
      let lookup_function_ty = lookup_function_ty scope provisional_env in
      let lookup_protocol_constraint =
        Protocol.constraint_type scope provisional_env
      in
      let lookup_dynamic_key_record_type =
        Expression_support.dynamic_key_record_type provisional_env
      in
      let resolve_named_record =
        Function_elaborator.infer_named_record scope provisional_env
      in
      let lookup_closed_sum_candidates payload_types =
        Env.closed_sum_candidates_for_payloads payload_types provisional_env
      in
      let lookup_closed_sum_constructors ty =
        Env.predicate_variant_constructors ty provisional_env
      in
      match
        Type_inference.infer_params ~materialize_open_equality:true
          ~lookup_call_ty:(Expression_support.lookup_call_ty scope provisional_env)
          ~expand_form:(Macro_expander.expand_all ~scope ~compiler_env:provisional_env)
          ~lookup_function_ty
          ~lookup_closed_sum_candidates
          ~lookup_closed_sum_constructors
          ~lookup_protocol_constraint ~lookup_dynamic_key_record_type
          ~lookup_key_record_type:
            (Expression_support.record_type_for_keyword ~scope provisional_env)
          ~resolve_named_record
          inference_params body_forms
      with
      | Error _ as err -> err
      | Ok inferred ->
          let inferred_param_tys =
            List.map
              (fun (spec : Destructure.param_spec) ->
                List.assoc_opt spec.source_name inferred
                |> Option.value ~default:TUnknown
                |> Function_elaborator.infer_named_record scope env)
              specs
          in
          let dynamic_param_tys =
            List.map
              (fun ty ->
                match ty with
                | TConstraint
                    (Seqable_constraint
                      ({
                         element = element_ty;
                         storage = (TUnknown | TMeta _ | TVar _);
                         _;
                       } as constraint_))
                  when Types.is_dynamic element_ty ->
                    TConstraint
                      (Seqable_constraint
                         {
                           constraint_ with
                           storage = Types.dynamic_constraint TUnknown;
                         })
                | ty
                  when Option.is_some (Types.protocol_constraint_info ty)
                       && Option.is_some (Types.seqable_constraint_info ty) ->
                    Types.dynamic_constraint ty
                | ty -> ty)
              inferred_param_tys
          in
          let prepare_recursive_parts self_param_tys overrides =
            let rec direct_tail_symbols = function
              | FSymbol name -> [ name ]
              | FList [ FSymbol "if"; _test; then_form; else_form ] ->
                  direct_tail_symbols then_form @ direct_tail_symbols else_form
              | FList (FSymbol ("do" | "let" | "binding") :: forms) -> (
                  match List.rev forms with
                  | tail :: _ -> direct_tail_symbols tail
                  | [] -> [])
              | _ -> []
            in
            let tail_symbols =
              match List.rev body_forms with
              | tail :: _ -> direct_tail_symbols tail
              | [] -> []
            in
            let return_seed =
              match explicit_return_ty with
              | Some return_ty -> Some return_ty
              | None -> (
                  let params =
                    List.map2
                      (fun (spec : Destructure.param_spec) ty ->
                        (spec.source_name, ty))
                      specs self_param_tys
                  in
                  let self_call = function
                    | FList (FSymbol name :: arguments) ->
                        (name = source_name
                        || name = Names.scoped_key scope source_name)
                        && List.length arguments = List.length specs
                    | _ -> false
                  in
                  let rec recursive_sequence_result = function
                    | FList [ FSymbol "__lg_cons"; value; tail ]
                      when self_call tail ->
                        let element_ty =
                          Type_inference.inferred_form_type params value
                        in
                        if Types.equal element_ty TUnknown then None
                        else Some (TSeq element_ty)
                    | FList
                        [
                          FSymbol "__lg_defer_seq";
                          FList
                            (FSymbol "fn" :: FVector [] :: thunk_body_forms);
                        ]
                    | FList (FSymbol ("do" | "let" | "let*") :: thunk_body_forms)
                      -> (
                        match List.rev thunk_body_forms with
                        | result :: _ -> recursive_sequence_result result
                        | [] -> None)
                    | _ -> None
                  in
                  let returned_vector =
                    match List.rev body_forms with
                    | result :: _ ->
                        Type_inference.returned_vector_type params result
                    | [] -> None
                  in
                  let returned_sequence =
                    match List.rev body_forms with
                    | result :: _ -> recursive_sequence_result result
                    | [] -> None
                  in
                  let returned_value =
                    match List.rev body_forms with
                    | result :: _ ->
                        let ty =
                          match
                            Type_inference.inferred_form_type params result
                          with
                          | ty when Type_solver.is_open ty -> (
                              match
                                Type_inference.inferred_call_return_type
                                  ~lookup_function_ty params result
                              with
                              | (TUnknown | TMeta _ | TVar _) -> ty
                              | ty -> ty)
                          | ty -> ty
                        in
                        (match ty with
                        | TUnknown | TMeta _ | TVar _ -> None
                        | ty -> Some ty)
                    | [] -> None
                  in
                  match (returned_sequence, returned_vector, returned_value) with
                  | Some _ as sequence_ty, _, _ -> sequence_ty
                  | None, (Some _ as vector_ty), _ -> vector_ty
                  | None, None, (Some _ as value_ty) -> value_ty
                  | None, None, None ->
                      List.combine specs self_param_tys
                      |> List.find_map
                           (fun ((spec : Destructure.param_spec), ty) ->
                             match ty with
                             | (TRecord _ | TNamed_record _)
                               when List.mem spec.source_name tail_symbols ->
                                 Some
                                   (Function_elaborator.infer_named_record
                                      ~allow_dynamic_fields:true scope env ty)
                             | _ -> None))
            in
            let return_seed_index =
              match explicit_return_ty with
              | Some _ -> None
              | None ->
                  List.combine specs self_param_tys
                  |> List.find_index
                       (fun ((spec : Destructure.param_spec), ty) ->
                         (match ty with
                         | TRecord _ | TNamed_record _ -> true
                         | _ -> false)
                         && List.mem spec.source_name tail_symbols)
            in
            let prepare ?(constrain_return = false) return_ty =
              let self_binding =
                Types.binding ocaml_name (TFn (self_param_tys, return_ty))
              in
              let env =
                Env.add (Names.scoped_key scope source_name) self_binding env
                |> Env.add ocaml_name self_binding
              in
              let expected_return_ty =
                if constrain_return then Some return_ty else None
              in
              Result.bind
                (prepare_fn ~param_type_overrides:overrides
                   ~materialize_open_equality:true ~recur_target:ocaml_name
                   ?expected_return_ty scope env params body_forms)
                (fun parts ->
                  if not constrain_return then Ok parts
                  else
                    Result.map
                      (fun semantic_expr ->
                        { parts with body = typed_ir return_ty semantic_expr })
                      (Call_elaborator.plan_and_emit_argument env
                         ~expected:return_ty parts.body))
            in
            let return_var = Type_solver.fresh () in
            let initial_return_ty =
              Option.value return_seed ~default:return_var
            in
            let provisional =
              match
                prepare initial_return_ty
              with
              | Ok _ as result -> result
              | Error _ when Option.is_some return_seed -> prepare return_var
              | Error error -> Error error
            in
            let provisional =
              match provisional with
              | Ok _ as result -> result
              | Error _ -> prepare TUnknown
            in
            let provisional =
              Result.bind provisional (fun parts ->
                  match return_seed_index with
                  | None -> Ok parts
                  | Some index -> (
                      match List.nth_opt parts.param_bindings index with
                      | Some (_, { ty = (TRecord _ | TNamed_record _) as ty; _ }) -> (
                          match prepare ~constrain_return:true ty with
                          | Ok _ as refined -> refined
                          | Error _ -> Ok parts)
                      | Some _ | None -> Ok parts))
            in
            Result.bind provisional (fun provisional ->
                let requires_specialized_self_calls =
                  Semantic_ir.exists_identifier
                    (fun name ->
                      String.starts_with
                        ~prefix:"Lg_runtime.Runtime_dynamic" name)
                    provisional.body.semantic_expr
                in
                if
                  Option.fold ~none:false
                    ~some:(Types.equal provisional.body.ty)
                    return_seed
                  ||
                  Types.equal provisional.body.ty TUnknown
                  || not requires_specialized_self_calls
                then Ok provisional
                else
                  let rec stabilize_return remaining return_ty =
                    Result.bind (prepare return_ty) (fun specialized ->
                        if Types.equal specialized.body.ty return_ty then
                          Ok specialized
                        else if remaining = 0 then
                          Error.error
                            ("recursive defn " ^ source_name
                           ^ " return type did not stabilize")
                        else
                          stabilize_return (remaining - 1)
                            specialized.body.ty)
                  in
                  stabilize_return 4 provisional.body.ty)
          in
          if
            List.exists Types.is_dynamic dynamic_param_tys
            || List.exists2
                 (fun inferred dynamic -> not (Types.equal inferred dynamic))
                 inferred_param_tys dynamic_param_tys
          then
            let self_param_tys =
              List.map2
                (fun inferred dynamic ->
                  if Types.is_dynamic dynamic then dynamic else inferred)
                inferred_param_tys dynamic_param_tys
            in
            let overrides =
              List.map2
                (fun explicit inferred ->
                  match explicit with
                  | Some _ -> explicit
                  | None when Types.equal inferred TUnknown -> None
                  | None -> Some inferred)
                param_type_overrides dynamic_param_tys
            in
            prepare_recursive_parts self_param_tys overrides
          else
            prepare_recursive_parts inferred_param_tys param_type_overrides))

and prepare_inferred_recursive_fn ?explicit_return_ty ~ocaml_name scope env
    source_name params body_forms =
  Result.bind
    (prepare_inferred_recursive_fn_body ?explicit_return_ty ~ocaml_name scope env
       source_name params body_forms)
    (fun parts ->
      let expression = fn_code parts in
      Result.bind
        (Macro_expander.expand_all_forms ~scope ~compiler_env:env body_forms)
        (fun body ->
          Result.map
            (fun substitutions ->
              { parts with
                param_bindings = List.map
                  (fun (key, (binding : binding)) ->
                    key, { binding with ty = Type_solver.apply substitutions binding.ty })
                  parts.param_bindings;
                body = { parts.body with
                  ty = Type_solver.apply substitutions parts.body.ty } })
            (Local_function_elaborator.refine_function scope env ~name:source_name
               ~target:ocaml_name ~params ~body expression)))

and prepare_inferred_recursive_fn_with_return ~ocaml_name scope env source_name
    return_ty params body_forms =
  Result.bind
    (prepare_inferred_recursive_fn ~explicit_return_ty:return_ty ~ocaml_name
       scope env source_name params body_forms)
    (fun parts ->
      if
        Types.assignable ~policy:Host_boundary ~expected:return_ty
          ~actual:parts.body.ty
      then
        Result.map
          (fun semantic_expr ->
            {
              parts with
              body =
                typed_ir return_ty
                  (Semantic_ir.Constraint
                     (semantic_expr, Types.ocaml_name return_ty));
            })
          (Call_elaborator.plan_and_emit_argument env ~expected:return_ty
             parts.body)
      else
        Error.error
          ("recursive defn " ^ source_name ^ " must return "
         ^ Types.source_name return_ty))

and fn_code ?(demote = false) ?self_name ?(row_param_type_names = []) parts =
  Function_elaborator.fn_code ~demote ?self_name ~row_param_type_names parts

and compile_multi_arity_fn scope env clauses =
  incr multi_arity_fn_counter;
  let name = "__lg_anonymous_fn_" ^ string_of_int !multi_arity_fn_counter in
  match prepare_multi_arity_fn ~ocaml_name:name scope env name clauses with
  | Error _ as err -> err
  | Ok prepared ->
      let bindings =
        List.map
          (fun clause ->
            let function_ =
              fn_code ~row_param_type_names:clause.row_param_types clause.parts
            in
            (Semantic_ir.PVar clause.target_name, function_.semantic_expr))
          prepared.clauses
      in
      Ok
        {
          prepared.expr with
          semantic_expr =
            Semantic_ir.Let (bindings, prepared.expr.semantic_expr);
        }

and compile_fn ?(param_type_overrides = []) ?preferred_record
    ?(use_open_context = false) scope env params body_forms =
  let expected_type = Env.expected_type env in
  let variadic_params =
    match params with
    | FVector forms ->
        let rec split fixed = function
          | [] -> Ok (FVector (List.rev fixed), None, None)
          | FSymbol "&" :: [ (FSymbol _ as rest_name) ] ->
              Ok
                ( FVector (List.rev_append fixed [ rest_name ]),
                  Some (List.length fixed),
                  None )
          | FSymbol "&" :: [ (FVector _ as rest_pattern) ] ->
              Result.map
                (fun bindings ->
                  ( FVector
                      (List.rev_append fixed [ FSymbol "__lg_vector_rest" ]),
                    Some (List.length fixed),
                    Some bindings ))
                (vector_rest_bindings "__lg_vector_rest" rest_pattern)
          | FSymbol "&" :: [ (FMap _ as rest_pattern) ] ->
              (* kwargs-style rest: [& {:as args}] binds the rest seq as a
                 map, compiled as (apply hash-map rest) *)
              Ok
                ( FVector (List.rev_append fixed [ FSymbol "__lg_kwargs_rest" ]),
                  Some (List.length fixed),
                  Some
                    [ rest_pattern;
                      FList
                        [
                          FSymbol "apply";
                          FSymbol "hash-map";
                          FSymbol "__lg_kwargs_rest";
                        ] ] )
          | FSymbol "&" :: _ ->
              Error.error "fn variadic arity requires one rest parameter"
          | form :: rest -> split (form :: fixed) rest
        in
        split [] forms
    | _ -> Ok (params, None, None)
  in
  match variadic_params with
  | Error _ as err -> err
  | Ok (params, variadic_rest_index, rest_binding) ->
  let body_forms =
    match rest_binding with
    | None -> body_forms
    | Some bindings ->
        [
          FList
            (FSymbol "let"
            :: FVector bindings
            :: body_forms);
        ]
  in
  let param_type_overrides =
    if param_type_overrides <> [] || Option.is_some variadic_rest_index then
      param_type_overrides
    else
      let contextual_parameter (spec : Destructure.param_spec) = function
        | ty when use_open_context -> Some ty
        | TVar _ as ty
          when String.starts_with ~prefix:"__lg_protocol_alias_arg_"
                 spec.source_name ->
            Some ty
        | TUnknown | TMeta _ | TVar _ -> None
        | ty -> Some ty
      in
      match (expected_type, Destructure.parse_param_specs params) with
      | Some (TFn (parameter_tys, _)), Ok specs
        when List.length parameter_tys = List.length specs ->
          List.map2 contextual_parameter specs parameter_tys
      | Some (TOverloaded_fn arities), Ok specs ->
          let argument_count = List.length specs in
          let parameter_tys =
            arities
            |> List.find_map (fun (arity : fn_arity) ->
                   match arity.rest_param with
                   | None
                     when List.length arity.fixed_params = argument_count ->
                       Some arity.fixed_params
                   | Some rest_ty
                     when argument_count >= List.length arity.fixed_params ->
                       Some
                         (arity.fixed_params
                         @ List.init
                             (argument_count - List.length arity.fixed_params)
                             (fun _ -> rest_ty))
                   | None | Some _ -> None)
          in
          (match parameter_tys with
          | Some parameter_tys ->
              List.map2 contextual_parameter specs parameter_tys
          | None -> [])
      | _ -> []
  in
  let expected_return_ty =
    match expected_type with
    | Some (TFn (_, return_ty)) when use_open_context -> Some return_ty
    | Some (TOverloaded_fn [ { return_ty; _ } ]) when use_open_context ->
        Some return_ty
    | Some (TFn (_, ((TRecord _ | TNamed_record _) as return_ty))) ->
        Some return_ty
    | Some
        (TOverloaded_fn
          [ { return_ty = ((TRecord _ | TNamed_record _) as return_ty); _ } ])
      ->
        Some return_ty
    | Some _ | None -> None
  in
  let env = Env.with_expected_type None env in
  match
    prepare_fn ~param_type_overrides ?preferred_record ?variadic_rest_index
      ?expected_return_ty ~refine_open_overrides:true scope env params body_forms
  with
  | Error _ as err -> err
  | Ok parts when unresolved_contextual_type parts.body.ty ->
      Error.error "empty list requires a contextual element type"
  | Ok parts -> (
      let function_ = fn_code parts in
      match variadic_rest_index with
      | None -> Ok function_
      | Some rest_index -> (
          match function_.ty with
          | TFn (param_tys, return_ty) ->
              let rec take count values =
                if count = 0 then []
                else
                  match values with
                  | value :: rest -> value :: take (count - 1) rest
                  | [] -> []
              in
              let fixed_params = take rest_index param_tys in
              let rest_element =
                match List.nth_opt param_tys rest_index with
                | Some (TSeq element_ty) -> element_ty
                | Some ty -> ty
                | None -> TUnknown
              in
              let arity =
                {
                  fixed_params;
                  rest_param = Some rest_element;
                  return_ty;
                }
              in
              Ok
                (typed_ir (TOverloaded_fn [ arity ])
                   (Semantic_ir.Tuple
                      [ function_.semantic_expr; Semantic_ir.Unit ]))
          | _ -> Ok function_))

and compile_named_fn scope env name params body_forms =
  let recursive =
    body_forms
    |> List.concat_map Dependency_graph.value_symbols
    |> List.exists (String.equal name)
  in
  if not recursive then compile_fn scope env params body_forms
  else
    let ocaml_name = "__lg_named_fn_" ^ Names.sanitize_name name in
    Result.bind
      (prepare_inferred_recursive_fn ~ocaml_name scope env name params body_forms)
      (fun parts ->
        let function_ = fn_code parts in
        match Semantic_ir.unlocated function_.semantic_expr with
        | Semantic_ir.Fun (patterns, body) ->
            Ok
              {
                function_ with
                semantic_expr =
                  Semantic_ir.annotate function_.ty
                    (Semantic_ir.LetRecIn
                       ( ocaml_name,
                         patterns,
                         body,
                         Semantic_ir.Ident ocaml_name ));
              }
        | Semantic_ir.Tuple
            [ Semantic_ir.Fun (patterns, body); Semantic_ir.Unit ] ->
            Ok
              {
                function_ with
                semantic_expr =
                  Semantic_ir.annotate function_.ty
                    (Semantic_ir.LetRecIn
                       ( ocaml_name,
                         patterns,
                         body,
                         Semantic_ir.Tuple
                           [ Semantic_ir.Ident ocaml_name; Semantic_ir.Unit ] ));
              }
        | _ -> Error.error "named fn requires a function body")

and compile_call scope env name arg_forms =
  (Lazy.force context).calls.compile_call scope env name arg_forms

and context : Elaboration_context.t Lazy.t =
  lazy (Elaboration_context.create ~compile_expr)

let compile_args_for scope env arg_forms =
  (Lazy.force context).calls.compile_args_for scope env arg_forms
