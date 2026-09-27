open Ast
open Types
open Lowered
module Env = Compiler_environment

let compile_expr = Expression_elaborator.compile_expr

let cljs_test_report_method_counter = ref 0

let next_cljs_test_report_method_name () =
  incr cljs_test_report_method_counter;
  "__lg_cljs_test_report_method_" ^ string_of_int !cljs_test_report_method_counter

let multimethod_method_counter = ref 0

let next_multimethod_method_name () =
  incr multimethod_method_counter;
  "__lg_multimethod_method_" ^ string_of_int !multimethod_method_counter

let cljs_test_report_method_symbol scope = function
  | "report" -> String.equal scope "cljs.test"
  | "cljs.test/report" | "t/report" | "ct/report" -> true
  | _ -> false

let resolve_multimethod_key scope env name =
  match String.split_on_char '/' name with
  | [ alias; member ] ->
      let owner =
        Env.resolve_namespace_alias ~scope alias env |> Option.value ~default:alias
      in
      owner ^ "/" ^ member
  | _ -> Names.scoped_key scope name

let compile_source_expr scope env form =
  let rec compile = function
    | FList (FSymbol name :: args) as form -> (
        match Env.find_macro ~scope name env with
        | None -> compile_expr scope env form
        | Some definition ->
            Result.bind
              (Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
                 definition args)
              compile)
    | form -> compile_expr scope env form
  in
  compile form

let prepare_fn = Expression_elaborator.prepare_fn
let prepare_recursive_fn = Expression_elaborator.prepare_recursive_fn

let prepare_inferred_recursive_fn =
  Expression_elaborator.prepare_inferred_recursive_fn

let prepare_inferred_recursive_fn_with_return =
  Expression_elaborator.prepare_inferred_recursive_fn_with_return

let mutation_value_type = function
  | FString _ -> Some TString
  | FInt _ -> Some TInt
  | FFloat _ -> Some TFloat
  | FBool _ -> Some TBool
  | FChar _ -> Some TChar
  | FKeyword _ -> Some TKeyword
  | FList (FSymbol operation :: _)
    when operation = "str" || operation = "__lg_str"
         || String.ends_with ~suffix:"/str" operation ->
      Some TString
  | _ -> None

let refine_mutable_bindings scope env form =
  let rec walk env = function
    | FList
        (FSymbol operation :: FSymbol reference :: FSymbol updater
       :: [ value ])
      when
        (operation = "swap!" || operation = "__lg_swap!"
        || String.ends_with ~suffix:"/swap!" operation)
        && (updater = "conj" || updater = "__lg_conj"
           || String.ends_with ~suffix:"/conj" updater) ->
        let env = walk env value in
        let key = Names.scoped_key scope reference in
        (match (Env.find_opt key env, mutation_value_type value) with
        | ( Some binding,
            Some value_ty ) -> (
            match binding.ty with
            | TRef (TVector (TUnknown | TMeta _ | TVar _)) ->
                Env.add key
                  { binding with ty = TRef (TVector value_ty); scheme = None }
                  env
            | _ -> env)
        | _ -> env)
    | FList forms | FVector forms -> List.fold_left walk env forms
    | FMap pairs ->
        List.fold_left
          (fun env (key, value) -> walk (walk env key) value)
          env pairs
    | _ -> env
  in
  walk env form

let resolve_auto_keywords scope env form =
  let resolve keyword =
    if not (String.starts_with ~prefix:"::" keyword) then Ok keyword
    else
      let name = String.sub keyword 2 (String.length keyword - 2) in
      match String.index_opt name '/' with
      | None -> Ok (":" ^ scope ^ "/" ^ name)
      | Some index ->
          let alias = String.sub name 0 index in
          let local_name =
            String.sub name (index + 1) (String.length name - index - 1)
          in
          (match Env.resolve_namespace_alias ~scope alias env with
          | Some namespace -> Ok (":" ^ namespace ^ "/" ^ local_name)
          | None ->
              Error.error
                ("cannot resolve auto-keyword namespace alias " ^ alias))
  in
  let rec walk source =
    let resolved =
      match source with
      | FKeyword keyword -> Result.map (fun keyword -> FKeyword keyword) (resolve keyword)
      | FList forms -> Result.map (fun forms -> FList forms) (walk_many forms)
      | FVector forms -> Result.map (fun forms -> FVector forms) (walk_many forms)
      | FMap entries ->
          let rec walk_entries resolved = function
            | [] -> Ok (FMap (List.rev resolved))
            | (key, value) :: rest ->
                Result.bind (walk key) (fun key ->
                    Result.bind (walk value) (fun value ->
                        walk_entries ((key, value) :: resolved) rest))
          in
          walk_entries [] entries
      | (FSymbol _ | FCoreSymbol _ | FString _ | FRegex _ | FInt _ | FFloat _
        | FDecimal _ | FChar _ | FBool _) as leaf ->
          Ok leaf
    in
    Result.map
      (fun target ->
        if target != source then Source_context.copy_location ~source ~target;
        target)
      resolved
  and walk_many forms =
    let rec loop resolved = function
      | [] -> Ok (List.rev resolved)
      | form :: rest ->
          Result.bind (walk form) (fun form -> loop (form :: resolved) rest)
    in
    loop [] forms
  in
  walk form

let fn_code = Expression_elaborator.fn_code
let binding_of_expr = Expression_support.binding_of_expr
let lookup_function = Expression_support.lookup_function
let allocate_anonymous_record = Expression_support.allocate_anonymous_record

let allocate_nested_anonymous_records =
  Expression_support.allocate_nested_anonymous_records

let allocate_function_return_record env next_type
    (parts : Expression_support.compiled_fn_parts) =
  match parts.body.ty with
  | TRecord fields
    when (not (Types.is_homogeneous_record fields))
         && List.exists
              (fun (field : field) -> not (Types.is_dynamic field.ty))
              fields ->
      let nested =
        allocate_nested_anonymous_records ~owner:"" env next_type fields
      in
      let allocation =
        allocate_anonymous_record ~owner:"" nested.env nested.next_type
          nested.nested_fields
      in
      let items =
          if allocation.fresh then
            nested.items
            @ [
                Type_def
                  {
                    type_id = allocation.record.type_id;
                    type_name = allocation.record.type_name;
                    type_parameters = allocation.record.type_parameters;
                    fields = allocation.record.fields;
                    nominal = false;
                    location = None;
                  };
              ]
          else nested.items
      in
      let body =
          match parts.body.record_values with
          | Some _ ->
              Structural_map.as_named_record allocation.record parts.body
          | None ->
              let source_name = "__lg_function_record_result" in
              let source =
                {
                  parts.body with
                  semantic_expr = Semantic_ir.Ident source_name;
                  record_values = None;
                }
              in
              let projected =
                Structural_map.as_named_record allocation.record source
              in
              {
                projected with
                semantic_expr =
                  Semantic_ir.Let
                    ( [
                        ( Semantic_ir.PVar source_name,
                          parts.body.semantic_expr );
                      ],
                      projected.semantic_expr );
                record_values = None;
              }
      in
      ( allocation.env,
        allocation.next_type,
        items,
        { parts with body } )
  | _ -> (env, next_type, [], parts)

let allocate_function_local_records env next_type
    (parts : Expression_support.compiled_fn_parts) =
  let current_env = ref env in
  let current_next_type = ref next_type in
  let items = ref [] in
  let local_record_cache = ref [] in
  let same_record_fields left right =
    List.length left = List.length right
    && List.for_all2
         (fun (left : field) (right : field) ->
           String.equal left.keyword right.keyword
           && String.equal left.ocaml_name right.ocaml_name
           && left.mutable_ = right.mutable_
           && left.runtime_map = right.runtime_map
           && Types.row_compatible ~expected:left.ty ~actual:right.ty
           && Types.row_compatible ~expected:right.ty ~actual:left.ty)
         left right
  in
  let rec materialize_type = function
    | TPoly_variant _ as ty -> Semantic_type.map_children materialize_type ty
    | TRecord fields when Types.is_homogeneous_record fields ->
        TRecord
          (List.map
             (fun (field : field) ->
               { field with ty = materialize_type field.ty })
             fields)
    | TRecord fields ->
        let fields =
          List.map
            (fun (field : field) ->
              { field with ty = materialize_type field.ty })
            fields
        in
        (match
           !local_record_cache
           |> List.find_map (fun (cached_fields, record) ->
                  if same_record_fields cached_fields fields then Some record
                  else None)
         with
        | Some record -> TNamed_record record
        | None ->
            let allocation =
              allocate_anonymous_record ~owner:"" !current_env
                !current_next_type fields
            in
            current_env := allocation.env;
            current_next_type := allocation.next_type;
            local_record_cache :=
              (fields, allocation.record) :: !local_record_cache;
            if allocation.fresh then
              items :=
                !items
                @ [
                    Type_def
                      {
                        type_id = allocation.record.type_id;
                        type_name = allocation.record.type_name;
                        type_parameters = allocation.record.type_parameters;
                        fields = allocation.record.fields;
                        nominal = false;
                        location = None;
                      };
                  ];
            TNamed_record allocation.record)
    | TNullable ty -> TNullable (materialize_type ty)
    | TArray ty -> TArray (materialize_type ty)
    | TRef ty -> TRef (materialize_type ty)
    | TList ty -> TList (materialize_type ty)
    | TVector ty -> TVector (materialize_type ty)
    | TSet ty -> TSet (materialize_type ty)
    | TSeq ty -> TSeq (materialize_type ty)
    | TOcaml_app (name, arguments) ->
        TOcaml_app (name, List.map materialize_type arguments)
    | TConstraint constraint_ ->
        TConstraint (Types.map_constraint materialize_type constraint_)
    | TTuple arguments -> TTuple (List.map materialize_type arguments)
    | TFn (parameters, return_type) ->
        TFn (parameters, materialize_type return_type)
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun arity ->
               {
                 fixed_params = arity.fixed_params;
                 rest_param = arity.rest_param;
                 return_ty = materialize_type arity.return_ty;
               })
             arities)
    | TNamed_record record ->
        TNamed_record
          {
            record with
            type_arguments = List.map materialize_type record.type_arguments;
            fields =
              List.map
                (fun (field : field) ->
                  { field with ty = materialize_type field.ty })
                record.fields;
          }
    | ( TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _
      ) as ty ->
        ty
  in
  let rec constrain_record type_name = function
    | Semantic_ir.Located (node_id, location, value) ->
        Semantic_ir.Located
          (node_id, location, constrain_record type_name value)
    | Semantic_ir.Record (fields, _) ->
        Semantic_ir.Record (fields, Some type_name)
    | value -> value
  in
  let rec constrain_pattern = function
    | Semantic_ir.PLocated (node_id, location, pattern) ->
        Semantic_ir.PLocated (node_id, location, constrain_pattern pattern)
    | Semantic_ir.PTyped (pattern, ty) ->
        let ty =
          match ty with TRecord _ -> ty | ty -> materialize_type ty
        in
        Semantic_ir.PTyped (pattern, ty)
    | pattern -> pattern
  in
  let materialize = function
    | Semantic_ir.Typed ((TRecord _ as ty), value)
      when (match Semantic_ir.unlocated value with
           | Semantic_ir.Record _ -> true
           | _ -> false) -> (
        match materialize_type ty with
        | TNamed_record record ->
            Semantic_ir.Typed
              ( TNamed_record record,
                constrain_record
                  (Structural_map.record_type_application record)
                  value )
        | ty -> Semantic_ir.Typed (ty, value))
    | Semantic_ir.Typed ((TRecord _ as ty), value) ->
        Semantic_ir.Typed (ty, value)
    | Semantic_ir.Typed ((TNamed_record _ as ty), value) -> (
        match materialize_type ty with
        | TNamed_record record as ty ->
            Semantic_ir.Typed
              ( ty,
                constrain_record
                  (Structural_map.record_type_application record)
                  value )
        | ty -> Semantic_ir.Typed (ty, value))
    | Semantic_ir.Typed (ty, value) ->
        Semantic_ir.Typed (materialize_type ty, value)
    | Semantic_ir.PackDynamic conversion ->
        Semantic_ir.PackDynamic
          {
            conversion with
            source_ty = materialize_type conversion.source_ty;
            target_ty = materialize_type conversion.target_ty;
          }
    | Semantic_ir.UnpackDynamic conversion ->
        Semantic_ir.UnpackDynamic
          {
            conversion with
            source_ty = materialize_type conversion.source_ty;
            target_ty = materialize_type conversion.target_ty;
          }
    | Semantic_ir.NullableToSeq conversion ->
        Semantic_ir.NullableToSeq
          {
            conversion with
            source_ty = materialize_type conversion.source_ty;
            element_ty = materialize_type conversion.element_ty;
          }
    | Semantic_ir.Fun (patterns, body) ->
        Semantic_ir.Fun (List.map constrain_pattern patterns, body)
    | value -> value
  in
  let semantic_expr =
    Semantic_ir.rewrite materialize parts.body.semantic_expr
  in
  let body_ty = materialize_type parts.body.ty in
  let param_bindings =
    List.map
      (fun (key, (binding : binding)) ->
        let ty =
          match binding.ty with
          | TRecord fields when not (Types.is_homogeneous_record fields) ->
              TRecord
                (List.map
                   (fun (field : field) ->
                     { field with ty = materialize_type field.ty })
                   fields)
          | ty -> materialize_type ty
        in
        (key, { binding with ty }))
      parts.param_bindings
  in
  ( !current_env,
    !current_next_type,
    !items,
    {
      parts with
      param_bindings;
      body = { parts.body with ty = body_ty; semantic_expr };
    } )

let allocate_top_level_local_records env next_type body =
  let parts : Expression_support.compiled_fn_parts =
    {
      param_bindings = [];
      param_identities = [];
      destructured_bindings = [];
      return_param_index_hint = None;
      body;
    }
  in
  let env, next_type, items, parts =
    allocate_function_local_records env next_type parts
  in
  (env, next_type, items, parts.body)

let dynamic_ty = Types.dynamic_constraint TUnknown

let list_nth list_name index =
  Semantic_ir.Apply
    ( Semantic_ir.Ident "List.nth",
      [ Semantic_ir.Ident list_name; Semantic_ir.Int index ] )

let dynamic_arg_names arity =
  List.init arity (fun index -> "__lg_multimethod_arg_" ^ string_of_int index)

let compile_multimethod_dispatch scope env dispatch_form =
  let args_name = "__lg_multimethod_dispatch_args" in
  match dispatch_form with
  | FKeyword keyword ->
      Ok
        ( 1,
          Semantic_ir.Fun
            ( [ Semantic_ir.PVar args_name ],
              Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.get",
                  [
                    list_nth args_name 0;
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident
                          "Lg_runtime.Runtime_multimethod.dynamic_keyword",
                        [ Semantic_ir.String keyword ] );
                  ] ) ),
          [ TRecord [ Types.make_field keyword TUnknown ] ] )
  | FSymbol "identity" ->
      Ok
        ( 1,
          Semantic_ir.Fun
            ([ Semantic_ir.PVar args_name ], list_nth args_name 0),
          [ TUnknown ] )
  | FSymbol "first" ->
      Ok
        ( 1,
          Semantic_ir.Fun
            ( [ Semantic_ir.PVar args_name ],
              Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.first_value",
                  [ list_nth args_name 0 ] ) ),
          [ TUnknown ] )
  | FList (FSymbol "fn" :: (FVector params as params_form) :: body_forms) ->
      let arity = List.length params in
      let overrides = List.map (fun _ -> Some dynamic_ty) params in
      Result.bind (prepare_fn scope env params_form body_forms)
        (fun static_dispatch ->
          let static_parameter_tys =
            static_dispatch.param_bindings
            |> List.map (fun (_key, (binding : binding)) -> binding.ty)
          in
          Result.bind
            (Expression_elaborator.compile_fn ~param_type_overrides:overrides
               scope env params_form body_forms)
            (fun dispatch ->
              Ok
                ( arity,
                  Semantic_ir.Fun
                    ( [ Semantic_ir.PVar args_name ],
                      Semantic_ir.Apply
                        ( dispatch.semantic_expr,
                          List.init arity (list_nth args_name) ) ),
                  static_parameter_tys )))
  | _ ->
      Error.error
        "defmulti currently supports keyword, identity, and fn dispatch forms"

let compile_multimethod_default scope env = function
  | [] ->
      Ok
        (Semantic_ir.Apply
           ( Semantic_ir.Ident "Lg_runtime.Runtime_multimethod.dynamic_keyword",
             [ Semantic_ir.String ":default" ] ))
  | [ FKeyword ":default"; value ] ->
      Result.map
        (fun value -> value.Types.semantic_expr)
        (Multimethod_dynamic_boundary.compile_form ~compile_expr scope env value)
  | _ -> Error.error "defmulti options currently support only :default"

let multimethod_dispatch_value_type = function
  | FKeyword _ -> Some TKeyword
  | FString _ -> Some TString
  | FInt _ -> Some TInt
  | FFloat _ -> Some TFloat
  | FChar _ -> Some TChar
  | FBool _ -> Some TBool
  | FRegex _ -> Some TRegex
  | FSymbol "nil" -> Some TNil
  | _ -> None

let refine_multimethod_dispatch_fields dispatch_ty parameter_tys =
  let refine = function
    | TRecord fields ->
        TRecord
          (List.map
             (fun (field : field) ->
               match field.ty with
               | TUnknown | TMeta _ | TVar _ -> { field with ty = dispatch_ty }
               | _ -> field)
             fields)
    | ty -> ty
  in
  List.map refine parameter_tys

let allocate_multi_arity_local_records env next_type
    (prepared : Expression_elaborator.prepared_multi_arity_fn) =
  let env, next_type, items, clauses =
    List.fold_left
      (fun (env, next_type, items, clauses)
           (clause : Expression_elaborator.prepared_multi_arity_clause) ->
        let env, next_type, clause_items, parts =
          allocate_function_local_records env next_type clause.parts
        in
        let param_bindings =
          List.map2
            (fun row_param_type (original, materialized) ->
              match row_param_type with
              | Some _ -> original
              | None -> materialized)
            clause.row_param_types
            (List.combine clause.parts.param_bindings parts.param_bindings)
        in
        let parts = { parts with param_bindings } in
        ( env,
          next_type,
          items @ clause_items,
          { clause with parts } :: clauses ))
      (env, next_type, [], []) prepared.clauses
  in
  (env, next_type, items, { prepared with clauses = List.rev clauses })

let row_param_type_names = Expression_support.row_param_type_names
let row_type_items = Expression_support.row_type_items
let check_emitted_name_collision = Resolver.check_emitted_name_collision
let unresolved_contextual_type = Expression_support.unresolved_contextual_type
let record_type_key = Resolver.record_type_key

let rec unresolved_record_hint = function
  | TPoly_variant row -> List.find_map unresolved_record_hint (List.filter_map snd row.tags)
  | TOcaml name when String.starts_with ~prefix:"__lg_record:" name ->
      Some
        (String.sub name (String.length "__lg_record:")
           (String.length name - String.length "__lg_record:"))
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      unresolved_record_hint ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.find_map unresolved_record_hint arguments
  | TConstraint constraint_ ->
      List.find_map unresolved_record_hint
        (Types.constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.find_map unresolved_record_hint (return_ty :: parameters)
  | TOverloaded_fn arities ->
      List.find_map
        (fun (arity : fn_arity) ->
          match
            List.find_map unresolved_record_hint
              (arity.return_ty :: arity.fixed_params)
          with
          | Some _ as hint -> hint
          | None -> Option.bind arity.rest_param unresolved_record_hint)
        arities
  | TRecord fields ->
      List.find_map
        (fun (field : field) -> unresolved_record_hint field.ty)
        fields
  | TNamed_record record ->
      List.find_map unresolved_record_hint record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _ ->
      None

let rec form_mentions_symbol name = function
  | FSymbol candidate -> candidate = name
  | FList (FSymbol ("quote" | "clojure.core/quote") :: _) -> false
  | FList (FSymbol "record" :: FSymbol _ :: fields) ->
      List.exists
        (function
          | FList (_field_name :: values) ->
              List.exists (form_mentions_symbol name) values
          | field -> form_mentions_symbol name field)
        fields
  | FList forms | FVector forms -> List.exists (form_mentions_symbol name) forms
  | FMap pairs ->
      List.exists
        (fun (key, value) ->
          form_mentions_symbol name key || form_mentions_symbol name value)
        pairs
  | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _ | FBool _
  | FKeyword _
  | FCoreSymbol _ ->
      false

let rec form_has_function_recur = function
  | FList (FSymbol ("fn" | "fn*" | "defn" | "defn-" | "loop" | "loop*") :: _)
    ->
      false
  | FList (FSymbol "recur" :: _) -> true
  | FList forms | FVector forms -> List.exists form_has_function_recur forms
  | FMap pairs ->
      List.exists
        (fun (key, value) ->
          form_has_function_recur key || form_has_function_recur value)
        pairs
  | FSymbol _ | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _
  | FBool _
  | FKeyword _ | FCoreSymbol _ ->
      false

let function_is_recursive scope name body_forms =
  List.exists (form_mentions_symbol name) body_forms
  || List.exists
       (form_mentions_symbol (Names.scoped_key scope name))
       body_forms
  || List.exists form_has_function_recur body_forms

let order_protocol_groups groups =
  let method_names (_, methods) =
    List.filter_map
      (function
        | FList (FSymbol method_name :: _) -> Some method_name | _ -> None)
      methods
  in
  let depends_on (_, methods) provider =
    method_names provider
    |> List.exists (fun method_name ->
        List.exists (form_mentions_symbol method_name) methods)
  in
  let rec order ordered remaining =
    match
      List.find_opt
        (fun candidate ->
          not
            (List.exists
               (fun provider ->
                 provider != candidate && depends_on candidate provider)
               remaining))
        remaining
    with
    | None -> List.rev_append ordered remaining
    | Some candidate ->
        order (candidate :: ordered)
          (List.filter (fun group -> group != candidate) remaining)
  in
  order [] groups

let expression_references_declaration env expression =
  Semantic_ir.exists_identifier
    (fun name -> Env.unresolved_declaration name env)
    expression

let requires_stable_forward_binding env env_key expression =
  expression_references_declaration env expression
  || Env.explicitly_declared env_key env

let compile_defprotocol = Protocol_elaborator.compile_defprotocol
let compile_extend_type = Protocol_elaborator.compile_extend_type

let runtime_root_expression expression =
  Semantic_ir.Apply
    ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.of_value",
      [ expression ] )

let redef_root_name ocaml_name = ocaml_name ^ "__root"

let redefable_binding (binding : Types.binding) =
  { binding with redef_root_name = Some (redef_root_name binding.ocaml_name) }

let redefable_function_wrapper root_name = function
  | TFn (parameter_tys, _) ->
      let names =
        List.mapi
          (fun index _ -> "__lg_redef_arg_" ^ string_of_int index)
          parameter_tys
      in
      let args = List.map (fun name -> Semantic_ir.Ident name) names in
      Semantic_ir.Fun
        ( List.map (fun name -> Semantic_ir.PVar name) names,
          Semantic_ir.Apply
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.deref",
                  [ Semantic_ir.Ident root_name ] ),
              args ) )
  | _ -> assert false

let compatible_redefinition_root env env_key value_ty =
  match Env.find_opt env_key env with
  | Some binding -> (
      match
        ( Types.runtime_root_name binding,
          Types.runtime_root_value_type binding )
      with
      | Some root_name, Some previous_ty when previous_ty = value_ty ->
          Some root_name
      | Some _, Some _ | Some _, None | None, _ -> None)
  | None -> None

let reset_runtime_root root_name expression =
  Semantic_ir.Apply
    ( Semantic_ir.Ident
        "Lg_runtime.Runtime_reference.replace_for_redefinition",
      [ Semantic_ir.Ident root_name; expression ] )

let rec contains_unresolved_type = function
  | TPoly_variant row -> List.exists contains_unresolved_type (List.filter_map snd row.tags)
  | TUnknown | TMeta _ | TVar _ | TNil -> true
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      contains_unresolved_type ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists contains_unresolved_type arguments
  | TConstraint constraint_ ->
      List.exists contains_unresolved_type
        (Types.constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.exists contains_unresolved_type (return_ty :: parameters)
  | TOverloaded_fn arities ->
      List.exists
        (fun (arity : fn_arity) ->
          List.exists contains_unresolved_type
            (arity.return_ty :: arity.fixed_params)
          || Option.fold ~none:false ~some:contains_unresolved_type
               arity.rest_param)
        arities
  | TRecord fields ->
      List.exists (fun (field : field) -> contains_unresolved_type field.ty)
        fields
  | TNamed_record record ->
      List.exists contains_unresolved_type record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TOcaml _ ->
      false

let redefable_roots = ref true

let source_scope_redefable_roots scope =
  !redefable_roots
  && (not (String.equal scope ""))
  &&
  not
    (String.equal scope "clojure.core"
    || String.starts_with ~prefix:"clojure." scope
    || String.starts_with ~prefix:"cljs." scope
    || String.starts_with ~prefix:"datascript." scope
    || String.starts_with ~prefix:"me.tonsky." scope)

let predeclare_protocol_groups scope env receiver_form groups =
  List.fold_left
    (fun result (protocol_name, methods) ->
      Result.bind result (fun env ->
          match Protocol.find_protocol_id scope env protocol_name with
          | Some _ ->
              Result.bind
                (Protocol_elaborator.predeclare_implementations_from_evidence
                   scope env receiver_form protocol_name methods)
                (fun env ->
                  Protocol_elaborator.predeclare_implementations scope env
                    receiver_form protocol_name methods)
          | None -> Ok env))
    (Ok env) groups

let deferred_value_type env (expr : Types.typed_expr) =
  Types.align_deferred_param_types
    (Protocol.refine_deferred_type env expr.ty)
    expr.semantic_expr

let preserves_required_seqable_protocol_result (expr : Types.typed_expr) =
  let method_returns_seqable_capability = function
    | TFn (_, return_ty) -> Option.is_some (Types.seqable_constraint_info return_ty)
    | TOverloaded_fn arities ->
        List.exists
          (fun (arity : fn_arity) ->
            Option.is_some (Types.seqable_constraint_info arity.return_ty))
          arities
    | _ -> false
  in
  let rec contains_required_result = function
    | ty when Option.is_some (Types.protocol_constraint_info ty) -> (
        match Types.protocol_constraint_info ty with
        | Some (_, witness_ty, value_ty) ->
            Option.fold ~none:false
              ~some:(List.exists method_returns_seqable_capability)
              (Types.protocol_witness_method_types witness_ty)
            || contains_required_result value_ty
        | None -> false)
    | TFn (parameters, return_ty) ->
        List.exists contains_required_result parameters
        || contains_required_result return_ty
    | TOverloaded_fn arities ->
        List.exists
          (fun (arity : fn_arity) ->
            List.exists contains_required_result arity.fixed_params
            || Option.fold ~none:false ~some:contains_required_result
                 arity.rest_param
            || contains_required_result arity.return_ty)
          arities
    | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
        contains_required_result value_ty
    | _ -> false
  in
  contains_required_result expr.ty

let located_value_pattern form pattern =
  match Source_context.find_identity form with
  | None -> pattern
  | Some (node_id, location) -> Located_value (node_id, location, pattern)

let compile_module_alias = Module_elaborator.compile_module_alias
let compile_module_signature = Module_signature_elaborator.compile
let compile_module_apply = Module_elaborator.compile_module_apply
let compile_module = Module_elaborator.compile_module
let compile_module_functor = Module_elaborator.compile_module_functor
let open_module_bindings = Module_environment.open_bindings
let parse_type_parameters = Type_parameters.parse
let compile_type_alias = Type_definition_elaborator.compile_type_alias

let compile_external_record ?location env next_type emitted_name type_parameters
    field_forms =
  let scope, source_name =
    match Resolver.split_qualified_type_name emitted_name with
    | Some (module_path, local_name) -> (module_path, local_name)
    | None -> ("", emitted_name)
  in
  Type_definition_elaborator.compile_type_record ?location
    ~emitted_name scope env next_type source_name type_parameters field_forms
let compile_type_record = Type_definition_elaborator.compile_type_record
let compile_signature = Signature_elaborator.compile

let compile_type_record_fields =
  Type_definition_elaborator.compile_type_record_fields

let compile_type_variant = Type_definition_elaborator.compile_type_variant

let sidecar_function_signature scope env name =
  let signatures = Env.signatures env in
  match
    Signature_overlay.find_value (Names.scoped_key scope name) signatures
  with
  | Some _ as signature -> signature
  | None when scope = "" && not (Names.is_qualified name) ->
      Signature_overlay.find_value ("user/" ^ name) signatures
  | None -> None

let recursive_type_annotation scope env name =
  match
    sidecar_function_signature scope env name
    |> Option.map (Function_elaborator.infer_named_record scope env)
  with
  | Some (TFn _ as signature) -> Some signature
  | Some _ | None -> None

let linked_parameter_return parameter_tys return_ty =
  List.find_opt
    (fun parameter_ty ->
      String.equal (Types.source_name parameter_ty)
        (Types.source_name return_ty))
    parameter_tys

let prepare_function scope env name params body_forms =
  let signature =
    sidecar_function_signature scope env name
    |> Option.map (Function_elaborator.infer_named_record scope env)
  in
  match signature with
  | Some (TFn (parameter_types, return_type)) ->
      Result.bind
        (prepare_fn
           ~param_type_overrides:(List.map Option.some parameter_types)
           ~expected_return_ty:return_type scope env params body_forms)
        (fun (parts : Expression_support.compiled_fn_parts) ->
          Result.map
            (fun semantic_expr ->
              {
                parts with
                body = typed_ir return_type semantic_expr;
                return_param_index_hint = None;
              })
            (Call_elaborator.plan_and_emit_argument env ~expected:return_type
               parts.body))
  | Some _ -> Error.error ("function signature expected for " ^ name)
  | None ->
      let forward_signature =
        match Env.find_opt (Names.scoped_key scope name) env with
        | Some { ty = TFn (parameter_tys, return_ty); forward_declared = true; _ }
          ->
            Some (parameter_tys, return_ty)
        | Some _ | None -> None
      in
      let forward_param_overrides =
        match forward_signature with
        | Some (parameter_tys, _) -> List.map Option.some parameter_tys
        | None -> []
      in
      let forward_return_ty =
        match forward_signature with
        | Some (parameter_tys, return_ty) ->
            linked_parameter_return parameter_tys return_ty
        | None -> None
      in
      Result.bind
        (prepare_fn ~param_type_overrides:forward_param_overrides
           ?expected_return_ty:forward_return_ty
           ~materialize_open_equality:true scope env params body_forms)
        (fun (parts : Expression_support.compiled_fn_parts) ->
          let parts =
            match forward_return_ty with
            | Some return_ty ->
                { parts with body = typed_ir return_ty parts.body.semantic_expr }
            | None -> parts
          in
          match (forward_return_ty, parts.return_param_index_hint) with
          | Some _, _ | None, None -> Ok parts
          | None, Some index -> (
              match List.nth_opt parts.param_bindings index with
              | None -> Ok parts
              | Some (_, parameter) ->
                  let return_ty = Types.constraint_value_type parameter.ty in
                  let self_returning_protocol =
                    match Types.protocol_constraint_info parameter.ty with
                    | Some (protocol_id, _, _) ->
                        Protocol.has_self_returning_method env protocol_id
                    | None -> false
                  in
                  if
                    (not self_returning_protocol)
                    || Types.equal parts.body.ty return_ty
                  then Ok parts
                  else
                    prepare_fn
                      ~param_type_overrides:
                        (List.map
                           (fun (_, (binding : binding)) -> Some binding.ty)
                           parts.param_bindings)
                      ~expected_return_ty:return_ty
                      ~materialize_open_equality:true scope env params
                      body_forms))

let successful_call_refinement scope env params body_forms =
  let body_forms =
    List.map
      (fun form ->
        Macro_expander.expand_all ~scope ~compiler_env:env form
        |> Result.value ~default:form)
      body_forms
  in
  let internal_name_is expected actual =
    String.equal expected actual
    || String.ends_with ~suffix:("/" ^ expected) actual
  in
  let rec positive_refinements parameter_name = function
    | FList [ FSymbol predicate; FSymbol argument ]
      when String.equal parameter_name argument ->
        if internal_name_is "__lg_symbol-predicate" predicate then [ TSymbol ]
        else if internal_name_is "__lg_keyword-predicate" predicate then
          [ TKeyword ]
        else if internal_name_is "__lg_int-predicate" predicate then [ TInt ]
        else []
    | FList (FSymbol conjunction :: conditions)
      when internal_name_is "__lg_logical-and" conjunction ->
        List.concat_map (positive_refinements parameter_name) conditions
    | _ -> []
  in
  let successful_condition = function
    | FList [ FSymbol if_name; condition; _; FSymbol nil_name ]
      when String.equal "if" if_name && String.equal "nil" nil_name ->
        Some condition
    | _ -> None
  in
  match (params, List.rev body_forms) with
  | FVector parameter_forms, final_form :: _ -> (
      match successful_condition final_form with
      | None -> None
      | Some condition ->
          parameter_forms
          |> List.mapi (fun index form -> (index, form))
          |> List.find_map (fun (index, form) ->
                 match form with
                 | FSymbol parameter_name -> (
                     match
                       positive_refinements parameter_name condition
                       |> List.sort_uniq Stdlib.compare
                     with
                     | [ refined_ty ] -> Some (index, refined_ty)
                     | [] | _ :: _ :: _ -> None)
                 | _ -> None))
  | _ -> None

let add_defined_function scope env_key binding params body_forms env =
  let env = Env.add env_key binding env in
  let env =
    Env.remove_successful_call_refinement binding.ocaml_name env
  in
  match successful_call_refinement scope env params body_forms with
  | Some (parameter_index, refined_ty) ->
      Env.add_successful_call_refinement binding.ocaml_name parameter_index
        refined_ty env
  | None -> env

let rec concrete_defrecord_field_type = function
  | TPoly_variant row as ty ->
      if List.for_all (fun payload -> Option.is_some (concrete_defrecord_field_type payload)) (List.filter_map snd row.tags)
      then Some ty else None
  | TUnknown | TMeta _ | TVar _ | TRecord _ -> None
  | ty when Types.is_dynamic ty -> None
  | ty when Option.is_some (Types.protocol_constraint_info ty) -> None
  | ty when Option.is_some (Types.seqable_constraint_info ty) -> None
  | TNullable (TUnknown | TMeta _ | TVar _) -> None
  | TNullable inner when Types.is_dynamic inner -> None
  | TOcaml_app ("option", [ (TUnknown | TMeta _ | TVar _) ]) -> None
  | TOcaml_app ("option", [ inner ]) when Types.is_dynamic inner -> None
  | TNullable ty ->
      Option.map (fun ty -> TNullable ty) (concrete_defrecord_field_type ty)
  | TOcaml_app (name, arguments) ->
      let rec concrete arguments =
        match arguments with
        | [] -> Some []
        | argument :: rest ->
            Option.bind (concrete_defrecord_field_type argument)
              (fun argument ->
                Option.map (fun rest -> argument :: rest) (concrete rest))
      in
      Option.map
        (fun arguments -> TOcaml_app (name, arguments))
        (concrete arguments)
  | TTuple items ->
      let rec concrete items =
        match items with
        | [] -> Some []
        | item :: rest ->
            Option.bind (concrete_defrecord_field_type item) (fun item ->
                Option.map (fun rest -> item :: rest) (concrete rest))
      in
      Option.map (fun items -> TTuple items) (concrete items)
  | TArray ty ->
      Option.map (fun ty -> TArray ty) (concrete_defrecord_field_type ty)
  | TRef ty -> Option.map (fun ty -> TRef ty) (concrete_defrecord_field_type ty)
  | TList ty ->
      Option.map (fun ty -> TList ty) (concrete_defrecord_field_type ty)
  | TVector ty ->
      Option.map (fun ty -> TVector ty) (concrete_defrecord_field_type ty)
  | TSet ty -> Option.map (fun ty -> TSet ty) (concrete_defrecord_field_type ty)
  | TSeq ty -> Option.map (fun ty -> TSeq ty) (concrete_defrecord_field_type ty)
  | TFn (parameters, return_ty) ->
      let rec concrete parameters =
        match parameters with
        | [] -> Some []
        | parameter :: rest ->
            Option.bind (concrete_defrecord_field_type parameter)
              (fun parameter ->
                Option.map (fun rest -> parameter :: rest) (concrete rest))
      in
      Option.bind (concrete parameters) (fun parameters ->
          Option.map
            (fun return_ty -> TFn (parameters, return_ty))
            (concrete_defrecord_field_type return_ty))
  | TOverloaded_fn _ -> None
  | TConstraint _ -> None
  | ( TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
    | TBool | TUnit | TNil | TOcaml _ | TNamed_record _ ) as ty ->
      Some ty

let has_static_capability ty =
  Option.is_some (Types.protocol_constraint_info ty)
  || Option.is_some (Types.seqable_constraint_info ty)
  || Option.is_some (Types.truthy_constraint_info ty)
  || Option.is_some (Types.nil_predicate_constraint_info ty)
  || Option.is_some (Types.printable_constraint_info ty)
  || Option.is_some (Types.exception_data_constraint_info ty)
  || Option.is_some (Types.hashable_constraint_info ty)
  || Option.is_some (Types.comparable_constraint_info ty)
  || Option.is_some (Types.array_index_constraint_info ty)
  || Option.is_some (Types.symbol_predicate_constraint_info ty)
  || Option.is_some (Types.contains_constraint_info ty)

let freshen_unknowns = Type_solver.freshen_unknowns

let nullable_payload = function
  | TNullable ty | TOcaml_app ("option", [ ty ]) -> Some ty
  | _ -> None

let merge_defrecord_field_types previous inferred =
  if
    (match previous with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
    && has_static_capability inferred
  then inferred
  else
  let merge_payload previous inferred =
    match
      ( concrete_defrecord_field_type previous,
        concrete_defrecord_field_type inferred )
    with
    | _, Some (TNamed_record _ as inferred) -> inferred
    | None, Some inferred -> inferred
    | Some previous, _ -> previous
    | None, None -> previous
  in
  match (nullable_payload previous, nullable_payload inferred) with
  | Some previous, Some inferred ->
      Types.normalize_nullable
        (TNullable (merge_payload previous inferred))
  | Some payload, None ->
      Types.normalize_nullable (TNullable (merge_payload payload inferred))
  | None, Some payload ->
      Types.normalize_nullable (TNullable (merge_payload previous payload))
  | None, None -> merge_payload previous inferred

let rec type_parameters_of_type = function
  | TPoly_variant row -> List.concat_map type_parameters_of_type (List.filter_map snd row.tags)
  | TVar name -> [ name ]
  | TNullable ty
  | TArray ty
  | TRef ty
  | TList ty
  | TVector ty
  | TSet ty
  | TSeq ty ->
      type_parameters_of_type ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.concat_map type_parameters_of_type arguments
  | TConstraint constraint_ ->
      List.concat_map type_parameters_of_type
        (Types.constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.concat_map type_parameters_of_type (return_ty :: parameters)
  | TOverloaded_fn arities ->
      arities
      |> List.concat_map (fun (arity : fn_arity) ->
          type_parameters_of_type arity.return_ty
          @ List.concat_map type_parameters_of_type arity.fixed_params
          @ Option.fold ~none:[] ~some:type_parameters_of_type arity.rest_param)
  | TRecord fields ->
      fields
      |> List.concat_map (fun (field : field) ->
          type_parameters_of_type field.ty)
  | TNamed_record record ->
      List.concat_map type_parameters_of_type record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TOcaml _ ->
      []

let generalize_types types =
  match (Type_solver.generalize (TTuple types)).body with
  | TTuple generalized -> generalized
  | _ -> assert false

let infer_defrecord_field_types scope env record_name field_names interface_forms =
  let accessor_parameter name =
    "__lg_record_field_" ^ Names.sanitize_name name
  in
  let field_name accessor =
    List.find_opt (fun name -> accessor = ".-" ^ name) field_names
  in
  let rec rewrite_field_access receiver = function
    | FList [ FSymbol accessor; FSymbol target ]
      when target = receiver && Option.is_some (field_name accessor) ->
        FSymbol (accessor_parameter (Option.get (field_name accessor)))
    | FList forms -> FList (List.map (rewrite_field_access receiver) forms)
    | FVector forms -> FVector (List.map (rewrite_field_access receiver) forms)
    | FMap pairs ->
        FMap
          (List.map
             (fun (key, value) ->
               ( rewrite_field_access receiver key,
                 rewrite_field_access receiver value ))
             pairs)
    | form -> form
  in
  let lookup_function_ty = Expression_support.lookup_function_ty scope env in
  let lookup_protocol_constraint = Protocol.constraint_type scope env in
  let rec protocol_ids ty =
    match Types.protocol_constraint_info ty with
    | Some (protocol_id, _, value_ty) -> protocol_id :: protocol_ids value_ty
    | None -> (
        match Types.dynamic_constraint_info ty with
        | Some capability -> protocol_ids capability
        | None -> [])
  in
  let rec has_guarded_protocol_constraint ty =
    if Types.is_guarded_protocol_constraint ty then true
    else
      match Types.protocol_constraint_info ty with
      | Some (_, _, value_ty) -> has_guarded_protocol_constraint value_ty
      | None -> (
          match Types.dynamic_constraint_info ty with
          | Some capability -> has_guarded_protocol_constraint capability
          | None -> false)
  in
  let resolve_protocol_record ty =
    if has_guarded_protocol_constraint ty then ty
    else
    match protocol_ids ty with
    | [] -> ty
    | protocols ->
        let candidates =
          Env.filter_record_bindings
            (fun key (binding : binding) ->
              if String.starts_with ~prefix:"__record/" key then
                match binding.ty with
                | TNamed_record record
                  when List.for_all
                         (fun protocol_id ->
                           Protocol.type_satisfies env protocol_id
                             (TNamed_record record))
                         protocols ->
                    Some record
                | _ -> None
              else None)
            env
          |> List.sort_uniq (fun left right ->
                 Type_id.compare left.type_id right.type_id)
        in
        (match candidates with [ record ] -> TNamed_record record | _ -> ty)
  in
  let method_types =
    interface_forms
    |> List.filter_map (function
         | FList (FSymbol method_name :: FVector parameters :: _) ->
             Some
               ( method_name,
                 TFn
                   ( List.map (fun _ -> Type_solver.fresh ()) parameters,
                     Type_solver.fresh () ) )
         | _ -> None)
    |> ref
  in
  let method_return_type method_name =
    match List.assoc_opt method_name !method_types with
    | Some (TFn (_, return_ty)) -> (
        match return_ty with
        | TUnknown | TMeta _ | TVar _ -> None
        | ty -> Some ty)
    | Some _ | None -> None
  in
  let update_method_types inferred =
    method_types :=
      List.map
        (fun (name, ty) ->
          (name, List.assoc_opt name inferred |> Option.value ~default:ty))
        !method_types
  in
  let propagate_receiver_protocol_methods receiver inferred =
    let rec evidence ty =
      match Types.protocol_constraint_info ty with
      | Some (protocol_id, witness_ty, value_ty) ->
          (protocol_id, witness_ty) :: evidence value_ty
      | None -> []
    in
    let update inferred (protocol_id, witness_ty) =
      match
        ( Protocol_registry.find_protocol protocol_id (Env.protocols env),
          Types.protocol_witness_method_types witness_ty )
      with
      | Some declaration, Some witness_methods ->
          let declared_methods =
            Protocol_registry.Method_map.bindings declaration.methods
          in
          if List.length declared_methods <> List.length witness_methods then
            inferred
          else
            List.fold_left2
              (fun inferred (method_id, _) witness_method ->
                let method_name = Method_id.name method_id in
                match List.assoc_opt method_name inferred with
                | None -> inferred
                | Some existing ->
                    Type_inference.replace_param method_name
                      (Type_inference.refine_type existing witness_method)
                      inferred)
              inferred declared_methods witness_methods
      | None, _ | _, None -> inferred
    in
    match List.assoc_opt receiver inferred with
    | None -> inferred
    | Some receiver_ty -> List.fold_left update inferred (evidence receiver_ty)
  in
  let infer_method field_types = function
    | FList
        (FSymbol method_name
        :: FVector (FSymbol receiver :: method_params)
        :: body_forms) -> (
        let method_params =
          method_params
          |> List.filter_map (function
            | FSymbol name when not (List.mem name field_names) ->
                Some (name, TUnknown)
            | _ -> None)
        in
        let params =
          ((receiver, TUnknown) :: method_params)
          @ List.map (fun name -> (name, TUnknown)) field_names
          @ List.map
              (fun name -> (accessor_parameter name, TUnknown))
              field_names
          @ List.filter
              (fun (name, _) -> not (String.equal name method_name))
              !method_types
        in
        let body_forms = List.map (rewrite_field_access receiver) body_forms in
        let body_forms =
          Macro_expander.expand_all_forms ~scope ~compiler_env:env body_forms
          |> Result.value ~default:body_forms
        in
        let lookup_dynamic_key_record_type =
          Expression_support.dynamic_key_record_type env
        in
        let resolve_named_record =
          Function_elaborator.infer_named_record scope env
        in
        let nullable_constructor_fields =
          Array.make (List.length field_names) false
        in
        let form_has_nullable_return = function
          | FList (FSymbol function_name :: arguments) -> (
              match lookup_function_ty function_name with
              | Ok (TFn (parameters, return_ty))
                when List.length parameters = List.length arguments ->
                  Option.is_some (nullable_payload return_ty)
              | _ -> false)
          | _ -> false
        in
        let observe_call name argument_forms argument_tys =
          let constructor_name = record_name ^ "." in
          if
            (name = constructor_name
            || String.ends_with ~suffix:("/" ^ constructor_name) name)
            && List.length argument_tys = List.length field_names
          then
            List.combine argument_forms argument_tys
            |> List.iteri (fun index (form, ty) ->
                if
                  Types.equal ty TNil
                  || Option.is_some (nullable_payload ty)
                  || form_has_nullable_return form
                then nullable_constructor_fields.(index) <- true)
        in
        let lookup_closed_sum_candidates payload_types =
          Env.closed_sum_candidates_for_payloads payload_types env
        in
        let lookup_closed_sum_constructors ty =
          Env.predicate_variant_constructors ty env
        in
        match
          Type_inference.infer_params
            ?expected_return_ty:(method_return_type method_name)
            ~lookup_call_ty:(Expression_support.lookup_call_ty scope env)
            ~expand_form:(Macro_expander.expand_all ~scope ~compiler_env:env)
            ~lookup_function_ty
            ~lookup_closed_sum_candidates
            ~lookup_closed_sum_constructors
            ~lookup_protocol_constraint ~lookup_dynamic_key_record_type
            ~lookup_key_record_type:
              (Expression_support.record_type_for_keyword ~scope env)
            ~resolve_named_record ~observe_call params body_forms
        with
        | Error _ -> field_types
        | Ok inferred_params ->
            let inferred_params =
              propagate_receiver_protocol_methods receiver inferred_params
            in
            update_method_types inferred_params;
            let inferred_fields =
              List.combine field_names field_types
              |> List.mapi (fun index (name, previous) ->
let inferred =
                  List.assoc_opt name inferred_params
                  |> Option.value ~default:TUnknown
                in
                let accessor_inferred =
                  List.assoc_opt (accessor_parameter name) inferred_params
                  |> Option.value ~default:TUnknown
                in
                let inferred =
                  Type_inference.refine_type inferred accessor_inferred
                in
                let inferred =
                  Function_elaborator.infer_named_record
                    ~allow_dynamic_fields:true scope env inferred
                  |> resolve_protocol_record
                in
                let merged =
                  merge_defrecord_field_types previous inferred
                in
                if
                  nullable_constructor_fields.(index)
                  && Option.is_none (nullable_payload merged)
                then TNullable merged
                else merged)
            in
            inferred_fields)
    | _ -> field_types
  in
  let rec stabilize remaining field_types =
    let previous_methods = !method_types in
    let inferred =
      List.fold_left infer_method field_types interface_forms
    in
    let stable_fields =
      List.length field_types = List.length inferred
      && List.for_all2 Types.equal field_types inferred
    in
    let stable_methods =
      List.length previous_methods = List.length !method_types
      && List.for_all2
           (fun (left_name, left_ty) (right_name, right_ty) ->
             left_name = right_name && Types.equal left_ty right_ty)
           previous_methods !method_types
    in
    if remaining = 0 || (stable_fields && stable_methods) then inferred
    else stabilize (remaining - 1) inferred
  in
  let inferred =
    stabilize 2 (List.map (fun _ -> TUnknown) field_names)
    |> List.map (fun ty ->
           if has_guarded_protocol_constraint ty then TUnknown
           else if has_static_capability ty then freshen_unknowns ty
           else
             concrete_defrecord_field_type ty
             |> Option.value ~default:TUnknown)
  in
  inferred

let rec compile scope env next_type form =
  Result.bind (resolve_auto_keywords scope env form) (fun form ->
      compile_resolved scope env next_type form)

and compile_resolved scope env next_type form =
  let definition_name =
    match form with
    | FList
        (FSymbol ("def" | "defonce" | "defn" | "defn-") :: FSymbol "^:dynamic" :: FSymbol name
        :: _) ->
        Some name
    | FList
        (FSymbol ("def" | "defonce" | "defn" | "defn-" | "defmacro") :: FSymbol name :: _)
      ->
        Some name
    | _ -> None
  in
  match definition_name with
  | Some name
    when scope <> "clojure.core" && scope <> "cljs.core"
         && not (Env.core_excluded ~scope name env)
         && (Option.is_some (Env.find_opt (Names.scoped_key "clojure.core" name) env)
             || Option.is_some (Env.find_macro ~scope:"clojure.core" name env)
             || Option.is_some (Env.find_inline_macro ~scope:"clojure.core" name env)) ->
      Error.error
        ("definition " ^ Names.scoped_key scope name ^ " conflicts with clojure.core/" ^ name
         ^ "; add (:refer-clojure :exclude [" ^ name ^ "]) to the namespace")
  | _ -> compile_definition scope env next_type form

and compile_definition scope env next_type form =
  let env = refine_mutable_bindings scope env form in
  match form with
  | FList [ FSymbol "ffi"; (FSymbol name as name_form);
            FVector parameters; result; options ] ->
      let ocaml_name = Names.ocaml_binding_name scope name in
      Result.map
        (fun (foreign : Foreign_binding.t) ->
          let binding = Types.binding ocaml_name foreign.value_type in
          scope, Env.add (Names.scoped_key scope name) binding env,
          next_type, Foreign_binding foreign)
        (Foreign_binding.parse ~target:(Env.target env)
             ~is_opaque:(function
               | TOcaml name -> (match Resolver.lookup_type_declaration scope env name with
                   | Some { kind = Opaque; _ } -> true | _ -> false)
               | _ -> false)
           ~resolve_type:(Function_elaborator.infer_named_record scope env)
           ~name:ocaml_name ~location:(Source_context.find name_form)
           parameters result options)
  | FList (FSymbol "ffi" :: _) ->
      Error.error "ffi expects a name, argument type vector, result type, and options map"
  | FList
      (FSymbol ("defn" | "defn-")
      :: FSymbol "^:dynamic"
      :: (FSymbol name as name_form)
      :: forms) ->
      let forms =
        match forms with
        | FString _docstring :: rest -> rest
        | rest -> rest
      in
      let forms =
        match forms with
        | FMap _attributes :: rest -> rest
        | rest -> rest
      in
      compile scope env next_type
        (FList
           [
             FSymbol "def";
             FSymbol "^:dynamic";
             name_form;
             FList (FSymbol "fn" :: FSymbol name :: forms);
           ])
  | FList
      [
        FSymbol "do";
        FList
          [
            FSymbol "defrecord";
            (FSymbol record_name as name_form);
            (FVector _ as fields);
          ];
        FList (FSymbol "extend-type" :: FSymbol receiver_name :: implementations);
      ]
    when record_name = receiver_name ->
      compile scope env next_type
        (FList (FSymbol "defrecord" :: name_form :: fields :: implementations))
  | FList (FSymbol "do" :: forms) ->
      let items_of = function Group items -> items | item -> [ item ] in
      let rec compile_forms scope env next_type items = function
        | [] -> Ok (scope, env, next_type, Group (List.rev items))
        | form :: rest -> (
            match compile scope env next_type form with
            | Error _ as error -> error
            | Ok (scope, env, next_type, item) ->
                compile_forms scope env next_type
                  (List.rev_append (items_of item) items)
                  rest)
      in
      compile_forms scope env next_type [] forms
  | FList
      (FSymbol "defrecord"
      :: (FSymbol name as name_form)
      :: FVector raw_fields
      :: interface_forms) ->
      let emitted_name = Names.ocaml_binding_name scope name in
      let provisional_type_id =
        Type_id.create ~owner:(if scope = "" then [] else [ scope ]) ~name
      in
      let provisional_record =
        Types.named_record ~type_id:provisional_type_id ~nominal:false
          ~type_name:emitted_name ~set_module_name:("Set_" ^ emitted_name) []
      in
      let env =
        let key = record_type_key scope name in
        match Env.find_opt key env with
        | Some _ -> env
        | None ->
            Env.add key
              (Types.binding ~forward_declared:true emitted_name
                 provisional_record)
              env
      in
      let resolve_field_hint hint =
        Result.bind (Type_annotation.of_param_annotation hint) (fun ty ->
            let ty = Function_elaborator.infer_named_record scope env ty in
            match unresolved_record_hint ty with
            | Some name -> Error.error ("unknown record type " ^ name)
            | None -> Ok ty)
      in
      let rec field_specs acc hint = function
        | [] -> (
            match hint with
            | None -> Ok (List.rev acc)
            | Some _ -> Error.error "defrecord field hint requires a field")
        | FSymbol metadata :: rest when String.starts_with ~prefix:"^" metadata
          -> (
            match hint with
            | None -> field_specs acc (Some metadata) rest
            | Some _ -> Error.error "defrecord field has multiple type hints")
        | FSymbol field_name :: rest -> (
            match hint with
            | None -> field_specs ((field_name, None) :: acc) None rest
            | Some hint ->
                Result.bind (resolve_field_hint hint) (fun ty ->
                    field_specs ((field_name, Some ty) :: acc) None rest))
        | _ -> Error.error "defrecord fields must be symbols"
      in
      let rec protocol_groups groups current = function
        | [] -> (
            match current with
            | None -> Ok (List.rev groups)
            | Some (protocol_name, methods) ->
                Ok (List.rev ((protocol_name, List.rev methods) :: groups)))
        | FSymbol protocol_name :: rest ->
            let groups =
              match current with
              | None -> groups
              | Some (name, methods) -> (name, List.rev methods) :: groups
            in
            protocol_groups groups (Some (protocol_name, [])) rest
        | (FList _ as method_form) :: rest -> (
            match current with
            | None -> Error.error "defrecord method requires a protocol name"
            | Some (protocol_name, methods) ->
                protocol_groups groups
                  (Some (protocol_name, method_form :: methods))
                  rest)
        | _ :: _ -> Error.error "invalid defrecord protocol implementation"
      in
      let items_of = function Group items -> items | item -> [ item ] in
      Result.bind (field_specs [] None raw_fields) (fun field_specs ->
          let signature_fields =
            Signature_overlay.find_record (Names.scoped_key scope name)
              (Env.signatures env)
          in
          let signature_field_type field_name =
            let declared_fields =
              match signature_fields with
              | Some fields -> Some fields
              | None -> (
                  match Resolver.lookup_record_type scope env name with
                  | Ok record when record.fields <> [] -> Some record.fields
                  | Ok _ | Error _ -> None)
            in
            Option.bind declared_fields (fun fields ->
              fields
              |> List.find_opt (fun (field : Types.field) ->
                     field.keyword = ":" ^ field_name)
              |> Option.map (fun (field : Types.field) ->
                     Function_elaborator.infer_named_record scope env
                       field.ty))
          in
          let conflicting_field =
            List.find_opt
              (fun (field_name, metadata_type) ->
                match (signature_field_type field_name, metadata_type) with
                | Some declared, Some annotated ->
                    not
                      (Types.assignable ~policy:Host_boundary ~expected:declared
                         ~actual:annotated
                      && Types.assignable ~policy:Host_boundary ~expected:annotated
                           ~actual:declared)
                | _ -> false)
              field_specs
          in
          match conflicting_field with
          | Some (field_name, _) ->
              Error.error
                ("defrecord field annotation does not match its signature: "
                ^ name ^ "/" ^ field_name)
          | None ->
          let field_specs =
            List.map
              (fun (field_name, metadata_type) ->
                ( field_name,
                  match signature_field_type field_name with
                  | Some ty -> Some ty
                  | None -> metadata_type ))
              field_specs
          in
          let fields = List.map fst field_specs in
          let inferred_field_types =
            infer_defrecord_field_types scope env name fields interface_forms
          in
          let fresh_unresolved_field_type = function
            | TNullable _ -> TNullable (Type_solver.fresh ())
            | TOcaml_app ("option", [ _ ]) ->
                TOcaml_app ("option", [ Type_solver.fresh () ])
            | _ -> Type_solver.fresh ()
          in
          let inferred_field_types =
            List.map2
              (fun (_field_name, explicit_ty) inferred_ty ->
                match explicit_ty with
                | Some _ -> inferred_ty
                | None
                  when Option.is_none
                         (concrete_defrecord_field_type inferred_ty)
                       && not (has_static_capability inferred_ty) ->
                    fresh_unresolved_field_type inferred_ty
                | None -> inferred_ty)
              field_specs inferred_field_types
          in
          let field_types =
            inferred_field_types
            |> List.map2 (fun (_field_name, explicit_ty) inferred_ty ->
                   match (explicit_ty, inferred_ty) with
                   | ( Some explicit_ty,
                       (TNullable inferred_inner
                       | TOcaml_app ("option", [ inferred_inner ])) )
                     when not
                            (match explicit_ty with
                            | TNullable _
                            | TOcaml_app ("option", [ _ ]) ->
                                true
                            | _ -> false)
                          && (Types.equal inferred_inner TUnknown
                             || (match inferred_inner with
                                | TMeta _ | TVar _ -> true
                                | _ -> false)
                             || Types.is_dynamic inferred_inner
                             || Types.assignable ~policy:Host_boundary
                                  ~expected:explicit_ty
                                  ~actual:inferred_inner) ->
                       TNullable explicit_ty
                   | Some explicit_ty, _ -> explicit_ty
                   | None, _ -> inferred_ty)
                 field_specs
          in
          let field_types = generalize_types field_types in
          let type_parameters =
            field_types
            |> List.concat_map type_parameters_of_type
            |> List.sort_uniq String.compare
          in
          let record_fields =
            List.map2
              (fun field_name ty -> Types.make_field (":" ^ field_name) ty)
              fields field_types
          in
          match
            compile_type_record_fields
              ?location:(Source_context.find name_form)
              ~allow_empty:true
              ~nominal:false
              ~reuse_existing:true
              ~emitted_name
              scope env next_type name type_parameters record_fields
          with
          | Error _ as error -> error
          | Ok (scope, env, next_type, type_item) -> (
              match protocol_groups [] None interface_forms with
              | Error _ as error -> error
              | Ok groups ->
                  let groups = order_protocol_groups groups in
                  let receiver_form = FSymbol name in
                  let rec compile_groups env next_type items = function
                    | [] -> Ok (scope, env, next_type, Group items)
                    | (protocol_name, methods) :: rest -> (
                        let wrap_method method_name _receiver_name params
                            body_forms =
                          FList (FSymbol method_name :: params :: body_forms)
                        in
                        let expand_method = function
                          | FList
                              (FSymbol method_name
                              :: (FVector (FSymbol receiver_name :: _) as params)
                              :: body_forms) ->
                              [
                                wrap_method method_name receiver_name params
                                  body_forms;
                              ]
                          | (FList (FSymbol method_name :: arities) as method_form)
                            ->
                              let rec expand acc = function
                                | [] -> Some (List.rev acc)
                                | FList
                                    ((FVector (FSymbol receiver_name :: _) as
                                      params)
                                    :: body_forms)
                                  :: rest ->
                                    expand
                                      (wrap_method method_name receiver_name
                                         params body_forms
                                      :: acc)
                                      rest
                                | _ -> None
                              in
                              Option.value (expand [] arities)
                                ~default:[ method_form ]
                          | method_form -> [ method_form ]
                        in
                        let wrapped_methods =
                          List.concat_map expand_method methods
                        in
                        let implementation_form =
                        match
                            Protocol.find_protocol_id scope env protocol_name
                          with
                          | Some _ ->
                              FList
                               (FSymbol "extend-type-no-register" :: FSymbol name
                               :: FSymbol protocol_name :: wrapped_methods)
                          | None ->
                              FList
                               (FSymbol "deftype-methods-no-register"
                               :: FSymbol name :: FSymbol protocol_name
                               :: methods)
                        in
                        match
                          compile scope env next_type implementation_form
                        with
                        | Error _ as error -> error
                        | Ok (_, env, next_type, item) ->
                            compile_groups env next_type
                              (items @ items_of item)
                              rest)
                  in
                  Result.bind
                    (predeclare_protocol_groups scope env receiver_form groups)
                    (fun env ->
                      compile_groups env next_type (items_of type_item) groups)))
  | (FList (FSymbol "deftype" :: args) as form)
    when Option.is_some (Env.find_macro ~scope "deftype" env) -> (
      match Env.find_macro ~scope "deftype" env with
      | None -> assert false
      | Some definition -> (
          match
            Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
              definition args
          with
          | Error _ as error -> error
          | Ok expanded -> compile scope env next_type expanded))
  | FList
      (FSymbol "deftype"
      :: (FSymbol name as name_form)
      :: FVector raw_fields
      :: _interface_forms) ->
      let rec field_specs acc metadata mutable_field = function
        | [] -> Ok (List.rev acc)
        | FSymbol ("^:mutable" | "^:unsynchronized-mutable") :: rest ->
            field_specs acc metadata true rest
        | FSymbol metadata :: rest when String.starts_with ~prefix:"^" metadata
          ->
            field_specs acc (Some metadata) mutable_field rest
        | FSymbol field_name :: rest ->
            field_specs
              ((field_name, metadata, mutable_field) :: acc)
              None false rest
        | _ -> Error.error "deftype fields must be symbols"
      in
      Result.bind (field_specs [] None false raw_fields) (fun fields ->
          let signature_fields =
            Signature_overlay.find_record (Names.scoped_key scope name)
              (Env.signatures env)
          in
          let signature_field_type field_name =
            Option.bind signature_fields (fun fields ->
                fields
                |> List.find_opt (fun (field : Types.field) ->
                       field.keyword = ":" ^ field_name)
                |> Option.map (fun (field : Types.field) -> field.ty))
          in
          let resolve_field_type field_name metadata =
            match signature_field_type field_name with
            | Some ty -> Ok ty
            | None -> (
                match metadata with
                | None -> Ok (Type_solver.fresh ())
                | Some annotation ->
                    Result.map
                      (Function_elaborator.infer_named_record scope env)
                      (Type_annotation.of_param_annotation annotation))
          in
          let rec build_definitions definitions = function
            | [] -> Ok (List.rev definitions)
            | (field_name, metadata, mutable_field) :: rest ->
                Result.bind
                  (resolve_field_type field_name metadata)
                  (fun inferred_type ->
                    let definition =
                      ( type_parameters_of_type inferred_type,
                        Types.make_field ~mutable_:mutable_field
                          (":" ^ field_name) inferred_type )
                    in
                    build_definitions (definition :: definitions) rest)
          in
          Result.bind (build_definitions [] fields) (fun definitions ->
              let record_fields =
                match definitions with
                | [] -> [ Types.make_record_identity_field () ]
                | _ -> List.map snd definitions
              in
              let generalized_types =
                record_fields
                |> List.map (fun (field : Types.field) -> field.ty)
                |> generalize_types
              in
              let record_fields =
                List.map2
                  (fun (field : Types.field) ty -> { field with ty })
                  record_fields generalized_types
              in
              let type_parameters =
                generalized_types |> List.concat_map type_parameters_of_type
                |> List.sort_uniq String.compare
              in
              compile_type_record_fields
                ?location:(Source_context.find name_form)
                ~allow_empty:true scope env next_type name type_parameters
                record_fields))
  | FList
      (FSymbol
         ( "deftype-methods"
         | "deftype-methods-no-pack"
         | "deftype-methods-no-register" )
      :: FSymbol type_name :: interface_forms)
    -> (
      match Resolver.lookup_record_type scope env type_name with
      | Error _ as err -> err
      | Ok record ->
          let receiver_ty = TNamed_record record in
          let method_arity params =
            match Destructure.parse_param_specs (FVector params) with
            | Ok specs -> List.length specs
            | Error _ -> List.length params
          in
          let deftype_method_names =
            interface_forms
            |> List.filter_map (function
                 | FList (FSymbol method_name :: _) -> Some method_name
                 | _ -> None)
          in
          let rec predeclare_methods env names current_interface = function
            | [] -> Ok (env, List.sort_uniq String.compare names)
            | FSymbol interface_name :: rest ->
                let registered =
                  match Protocol.find_protocol_id scope env interface_name with
                  | None -> Ok env
                  | Some protocol_id -> (
                      match
                        Protocol_registry.find_protocol protocol_id
                          (Env.protocols env)
                      with
                      | Some declaration
                        when Protocol_registry.Method_map.is_empty
                               declaration.methods ->
                          Protocol_elaborator.add_marker_implementation env
                            protocol_id receiver_ty
                      | Some _ | None -> Ok env)
                in
                Result.bind registered (fun env ->
                    predeclare_methods env names (Some interface_name) rest)
            | FList (FSymbol method_name :: arities) :: rest
              when arities <> []
                   && List.for_all
                        (function
                          | FList (FVector _ :: _) -> true
                          | _ -> false)
                        arities ->
                let methods =
                  List.map
                    (function
                      | FList ((FVector _ as params) :: body_forms) ->
                          FList (FSymbol method_name :: params :: body_forms)
                      | _ -> assert false)
                    arities
                in
                predeclare_methods env names current_interface (methods @ rest)
            | FList
                (FSymbol method_name :: FVector params :: _body_forms)
              :: rest -> (
                match current_interface with
                | Some "IPrintWithWriter" ->
                    let source_name =
                      Expression_support.print_method_name record
                    in
                    let ocaml_name = Names.sanitize_name source_name in
                    let dynamic = Types.dynamic_constraint TUnknown in
                    let binding =
                      Types.binding ~forward_declared:true ocaml_name
                        (TFn
                           ( [ receiver_ty; TOcaml "Buffer.t"; dynamic ],
                             TUnit ))
                    in
                    predeclare_methods
                      (Env.add (Names.scoped_key scope source_name) binding env)
                      (ocaml_name :: names) current_interface rest
                | Some protocol_name -> (
                    match
                      ( Protocol.find_protocol_id scope env protocol_name,
                        Protocol.lookup_protocol_marker ~refine:false scope env
                          protocol_name method_name )
                    with
                    | Some _, Some marker ->
                        let arity = method_arity params in
                        let source_name =
                          Expression_support.deftype_method_name record
                            method_name arity
                        in
                        let ocaml_name = Names.sanitize_name source_name in
                        let method_ty =
                          let method_ty =
                            match marker.ty with
                            | TOverloaded_fn arities ->
                                arities
                                |> List.find_opt (fun (candidate : fn_arity) ->
                                       Option.is_none candidate.rest_param
                                       && List.length candidate.fixed_params
                                          = arity)
                                |> Option.map (fun candidate ->
                                       TFn
                                         ( candidate.fixed_params,
                                           candidate.return_ty ))
                                |> Option.value ~default:marker.ty
                            | method_ty -> method_ty
                          in
                          Types.instantiate_receiver_method_type receiver_ty
                            method_ty
                        in
                        let binding =
                          Types.binding ~forward_declared:true ocaml_name
                            method_ty
                        in
                        let implementation =
                          match marker.ty with
                          | TOverloaded_fn arities ->
                              let overload_targets =
                                List.map
                                  (fun (candidate : fn_arity) ->
                                    Expression_support.deftype_method_name record
                                      method_name
                                      (List.length candidate.fixed_params)
                                    |> Names.sanitize_name)
                                  arities
                              in
                              Types.binding ~forward_declared:true
                                ~overload_targets ocaml_name
                                (Types.instantiate_receiver_method_type
                                   receiver_ty marker.ty)
                          | _ -> binding
                        in
                        let registered =
                          match marker.ty with
                          | TOverloaded_fn _
                            when Option.is_some
                                   (Protocol.lookup_marker_impl env marker
                                      method_name receiver_ty) ->
                              Ok env
                          | _ ->
                              Protocol_elaborator.add_implementation env
                                method_name receiver_ty marker implementation
                        in
                        (match registered with
                        | Error _ as error -> error
                        | Ok env ->
                            predeclare_methods env (ocaml_name :: names)
                              current_interface rest)
                    | None, _ | _, None ->
                        predeclare_methods env names current_interface rest)
                | None ->
                    predeclare_methods env names current_interface rest)
            | _ :: rest ->
                predeclare_methods env names current_interface rest
          in
          Result.bind
            (predeclare_methods env [] None interface_forms)
            (fun (env, _implementation_names) ->
          let rec compile_methods env items current_interface = function
            | [] ->
                let ordinary, recursive =
                  List.rev items
                  |> List.fold_left
                       (fun (ordinary, recursive) -> function
                         | Recursive_value_binding
                             { name; identity; type_annotation; expression } ->
                             ( ordinary,
                               ({
                                  name;
                                  identity;
                                  type_annotation;
                                  expression;
                                }
                                 : recursive_value)
                               :: recursive )
                         | item -> (item :: ordinary, recursive))
                       ([], [])
                in
                let items =
                  List.rev ordinary
                  @
                  match List.rev recursive with
                  | [] -> []
                  | bindings -> [ Recursive_value_bindings bindings ]
                in
                Ok (scope, env, next_type, Group items)
            | FSymbol interface_name :: rest ->
                compile_methods env items (Some interface_name) rest
            | FList (FSymbol method_name :: arities) :: rest
              when arities <> []
                   && List.for_all
                        (function
                          | FList (FVector _ :: _) -> true
                          | _ -> false)
                        arities ->
                let methods =
                  List.map
                    (function
                      | FList ((FVector _ as params) :: body_forms) ->
                          FList (FSymbol method_name :: params :: body_forms)
                      | _ -> assert false)
                    arities
                in
                compile_methods env items current_interface (methods @ rest)
            | FList
                (FSymbol method_name
                :: (FVector params as params_form)
                :: body_forms)
              :: rest -> (
                let arity = method_arity params in
                let source_name =
                  if current_interface = Some "IPrintWithWriter" then
                    Expression_support.print_method_name record
                  else
                    Expression_support.deftype_method_name record method_name
                      arity
                in
                let ocaml_name = Names.sanitize_name source_name in
                let receiver_name, params_form =
                  let receiver_annotation = function
                    | TNamed_record record -> "^" ^ Type_id.name record.type_id
                    | ty -> "^" ^ Types.source_name ty
                  in
                  match params with
                  | FSymbol annotation :: FSymbol "_" :: remaining
                    when String.starts_with ~prefix:"^" annotation ->
                      let receiver_name = "__lg_deftype_this" in
                      ( receiver_name,
                        FVector
                          (FSymbol annotation :: FSymbol receiver_name
                         :: remaining) )
                  | FSymbol annotation :: FSymbol receiver_name :: _
                    when String.starts_with ~prefix:"^" annotation ->
                      (receiver_name, params_form)
                  | FSymbol "_" :: remaining ->
                      let receiver_name = "__lg_deftype_this" in
                      let params =
                        match receiver_ty with
                        | TNamed_record _ ->
                            FSymbol (receiver_annotation receiver_ty)
                            :: FSymbol receiver_name :: remaining
                        | _ -> FSymbol receiver_name :: remaining
                      in
                      (receiver_name, FVector params)
                  | FSymbol receiver_name :: _ -> (receiver_name, params_form)
                  | _ -> ("__lg_deftype_this", params_form)
                in
                let params_form =
                  match (receiver_ty, params_form) with
                  | TNamed_record _, FVector (FSymbol first :: _)
                    when String.starts_with ~prefix:"^" first ->
                      params_form
                  | TNamed_record _, FVector params ->
                      FVector
                        (FSymbol
                           (match receiver_ty with
                           | TNamed_record record ->
                               "^" ^ Type_id.name record.type_id
                           | ty -> "^" ^ Types.source_name ty)
                        :: params)
                  | _ -> params_form
                in
                let rec unresolved_print_call = function
                  | FList (FSymbol name :: arguments) ->
                      let special_form =
                        List.mem name
                          [
                            "binding";
                            "do";
                            "fn";
                            "if";
                            "let";
                            "match";
                            "try";
                            "deref";
                            "pr-sequential-writer";
                            "pr-writer";
                          ]
                        || Option.is_some (Env.find_macro ~scope name env)
                      in
                      ((not special_form)
                      && not (String.starts_with ~prefix:"-" name)
                      && not (String.starts_with ~prefix:"." name)
                      && not (List.mem name deftype_method_names)
                      && Option.is_none
                           (Expression_support.untyped_first_class_function_error
                              name)
                      && Result.is_error (lookup_function scope env name))
                      || List.exists unresolved_print_call arguments
                  | FList forms | FVector forms ->
                      List.exists unresolved_print_call forms
                  | FMap pairs ->
                      List.exists
                        (fun (key, value) ->
                          unresolved_print_call key
                          || unresolved_print_call value)
                        pairs
                  | FSymbol _ | FInt _ | FFloat _ | FDecimal _ | FChar _
                  | FString _
                  | FRegex _ | FBool _ | FKeyword _ | FCoreSymbol _ ->
                      false
                in
                let skip_unresolved_print =
                  current_interface = Some "IPrintWithWriter"
                  && List.exists unresolved_print_call body_forms
                in
                let rec form_mentions name = function
                  | FSymbol candidate -> candidate = name
                  | FList
                      (FSymbol
                         ("record" | "clojure.core/record" | "cljs.core/record")
                      :: _type_name :: field_forms) ->
                      List.exists
                        (function
                          | FList [ _field_name; value ] ->
                              form_mentions name value
                          | form -> form_mentions name form)
                        field_forms
                  | FList forms | FVector forms ->
                      List.exists (form_mentions name) forms
                  | FMap pairs ->
                      List.exists
                        (fun (key, value) ->
                          form_mentions name key || form_mentions name value)
                        pairs
                  | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _
                  | FRegex _
                  | FBool _ | FKeyword _ | FCoreSymbol _ ->
                      false
                in
                let rec rewrite_mutable_assignments = function
                    | FList [ FSymbol "set!"; FSymbol field_name; value_form ]
                      -> (
                      let keyword = ":" ^ field_name in
                      match Types.find_field keyword record.fields with
                      | Some { mutable_ = true; _ } ->
                          FList
                              [
                                FSymbol "__deftype-field-set!";
                                FKeyword keyword;
                                FSymbol receiver_name;
                              rewrite_mutable_assignments value_form;
                            ]
                      | _ ->
                          FList
                              [
                                FSymbol "set!";
                              FSymbol field_name;
                              rewrite_mutable_assignments value_form;
                            ])
                  | FList forms ->
                      FList (List.map rewrite_mutable_assignments forms)
                  | FVector forms ->
                      FVector (List.map rewrite_mutable_assignments forms)
                  | FMap pairs ->
                      FMap
                        (List.map
                           (fun (key, value) ->
                             ( rewrite_mutable_assignments key,
                               rewrite_mutable_assignments value ))
                           pairs)
                  | form -> form
                in
                let compile_expanded_body body_forms =
                  let body_forms =
                    List.map rewrite_mutable_assignments body_forms
                  in
                  let parameter_names =
                    match Destructure.parse_param_specs params_form with
                    | Ok specs ->
                        specs
                        |> List.concat_map
                             (fun (spec : Destructure.param_spec) ->
                               spec.source_name
                               :: Destructure.pattern_names spec.pattern)
                    | Error _ -> Destructure.pattern_names params_form
                  in
                let field_bindings =
                  record.fields
                  |> List.filter (fun (field : field) ->
                         let source_name =
                           Names.keyword_source_name field.keyword
                         in
                         (not (List.mem source_name parameter_names))
                         && List.exists (form_mentions source_name) body_forms)
                  |> List.concat_map (fun (field : field) ->
                         let source_name =
                           Names.keyword_source_name field.keyword
                         in
                        [
                          FSymbol source_name;
                           FList
                            [
                              FSymbol (".-" ^ source_name);
                               FSymbol receiver_name;
                             ];
                         ])
                in
                let body_forms =
                  [
                    FList
                      (FSymbol "let" :: FVector field_bindings :: body_forms);
                  ]
                in
                  let protocol_method_type protocol_name =
                    match
                      Protocol_elaborator.marker scope env protocol_name
                        method_name
                    with
                    | Error _ -> None
                    | Ok marker ->
                        let method_ty =
                          match marker.ty with
                          | TOverloaded_fn arities ->
                              arities
                              |> List.find_opt (fun (candidate : fn_arity) ->
                                     Option.is_none candidate.rest_param
                                     && List.length candidate.fixed_params
                                        = arity)
                              |> Option.map (fun candidate ->
                                     TFn
                                       ( candidate.fixed_params,
                                         candidate.return_ty ))
                              |> Option.value ~default:marker.ty
                          | method_ty -> method_ty
                        in
                        Some method_ty
                  in
                  let param_type_overrides =
                    match (current_interface, method_name, params) with
                    | Some "IPrintWithWriter", "-pr-writer", [ _; _; _ ] ->
                        [
                        Some receiver_ty;
                        Some (TOcaml "Buffer.t");
                        Some TNil;
                      ]
                    | Some "ILookup", "-lookup", _receiver :: arguments ->
                        Some receiver_ty
                        :: List.map
                             (fun _ -> Some (Type_solver.fresh ()))
                             arguments
                    | Some protocol_name, _, _ -> (
                        match protocol_method_type protocol_name with
                        | Some method_ty ->
                            Protocol_elaborator.protocol_parameter_overrides
                              receiver_ty method_ty
                        | None -> [ Some receiver_ty ])
                    | None, _, _ -> [ Some receiver_ty ]
                  in
                  let method_env, use_open_context =
                    match current_interface with
                    | Some protocol_name -> (
                        match protocol_method_type protocol_name with
                        | Some method_ty ->
                            let expected_method_ty =
                              Types.instantiate_receiver_method_type receiver_ty
                                method_ty
                            in
                            let use_return_context =
                              Protocol_elaborator.method_return_needs_context env
                                expected_method_ty
                            in
                            ( Env.with_expected_type
                                (if use_return_context then
                                   Some expected_method_ty
                                 else None)
                                env,
                              use_return_context )
                        | None -> (env, false))
                    | None -> (env, false)
                  in
                  if skip_unresolved_print then
                    compile_methods
                      (Env.remove (Names.scoped_key scope source_name) env)
                    items current_interface rest
                  else
                  match
                    Expression_elaborator.compile_fn ~param_type_overrides
                      ~use_open_context scope method_env params_form body_forms
                  with
                | Error _ as err -> err
                | Ok implementation -> (
                    let binding = binding_of_expr ocaml_name implementation in
                    let register_protocol env =
                      match current_interface with
                      | Some "IPrintWithWriter" -> Ok env
                      | Some protocol_name
                        when Option.is_some
                                 (Protocol.find_protocol_id scope env
                                    protocol_name)
                             && Option.is_some
                                  (Protocol.lookup_protocol_marker ~refine:false
                                       scope env protocol_name method_name) -> (
                          match
                            Protocol_elaborator.marker scope env protocol_name
                              method_name
                          with
                          | Error _ as error -> error
                          | Ok ({ ty = TOverloaded_fn _; _ } as marker) ->
                              Protocol_elaborator.update_overloaded_implementation
                                env method_name receiver_ty marker binding
                          | Ok marker ->
                              Protocol_elaborator.add_implementation env
                                method_name receiver_ty marker binding)
                      | _ -> Ok env
                    in
                      match register_protocol env with
                    | Error _ as error -> error
                    | Ok env ->
                        let env =
                            Env.add
                              (Names.scoped_key scope source_name)
                              binding env
                        in
                        let item =
                          if
                            expression_references_declaration env
                              implementation.semantic_expr
                          then
                            let implementation_type =
                              match current_interface with
                              | Some protocol_name -> (
                                  match
                                    Protocol.lookup_protocol_marker
                                      ~refine:false scope env protocol_name
                                      method_name
                                  with
                                  | Some marker ->
                                      Protocol_elaborator
                                      .refine_protocol_implementation_type
                                        marker.ty implementation.ty
                                  | None -> implementation.ty)
                              | None -> implementation.ty
                            in
                            Deferred_value_binding
                              {
                                name = ocaml_name;
                                value_type =
                                  Protocol.refine_deferred_type env
                                    implementation_type;
                                return_param_index =
                                  implementation.return_param_index;
                                expression = implementation.semantic_expr;
                              }
                          else if
                            Semantic_ir.exists_identifier
                              (String.equal ocaml_name)
                              implementation.semantic_expr
                          then
                            Recursive_value_binding
                              {
                                name = ocaml_name;
                                identity = None;
                                type_annotation = None;
                                expression = implementation.semantic_expr;
                              }
                          else
                            Value_binding
                              {
                                pattern = Named ocaml_name;
                                expression = implementation.semantic_expr;
                              }
                        in
                        compile_methods env (item :: items) current_interface
                          rest)
                in
                match
                  Macro_expander.expand_all_forms ~scope ~compiler_env:env
                    body_forms
                with
                | Error _ as error -> error
                | Ok body_forms -> compile_expanded_body body_forms)
            | _ :: _ ->
                Error.error
                  "deftype methods must be (method-name [params] body...)"
          in
          compile_methods env [] None interface_forms))
  | FList
      (FSymbol "defmulti" :: FSymbol name :: dispatch_form :: option_forms) -> (
      match
        ( compile_multimethod_dispatch scope env dispatch_form,
          compile_multimethod_default scope env option_forms )
      with
      | Ok (arity, dispatch_fn, parameter_tys), Ok default_dispatch ->
          let source_key = Names.scoped_key scope name in
          let ocaml_name = Names.ocaml_binding_name scope name in
          let dispatch_name = ocaml_name ^ "_dispatch_fn" in
          let method_table_name = ocaml_name ^ "_method_table" in
          let method_entries_name = ocaml_name ^ "_method_entries" in
          let dynamic_args_name = ocaml_name ^ "_dynamic_args" in
          let selected_method_name = ocaml_name ^ "_selected_method" in
          let arg_names = dynamic_arg_names arity in
          let arg_values =
            List.map (fun name -> Semantic_ir.Ident name) arg_names
          in
          let method_entries = Semantic_ir.Ident method_entries_name in
          let invoke =
            Semantic_ir.Match
              ( Semantic_ir.Apply
                  ( Semantic_ir.Ident
                      "Lg_runtime.Runtime_multimethod.select_method",
                    [ Semantic_ir.String source_key;
                      Semantic_ir.Ident dynamic_args_name;
                      method_entries;
                    ] ),
                [ ( Semantic_ir.PConstructor
                      ("Some", Some (Semantic_ir.PVar selected_method_name)),
                    Semantic_ir.Apply
                      (Semantic_ir.Ident selected_method_name, arg_values) );
                  ( Semantic_ir.PConstructor ("None", None),
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident
                          "Lg_runtime.Runtime_multimethod.no_method",
                        [ Semantic_ir.String source_key ] ) );
                ] )
          in
          let render =
            Semantic_ir.Fun
              ( Semantic_ir.PVar dynamic_args_name
                :: List.map (fun name -> Semantic_ir.PVar name) arg_names,
                Semantic_ir.Let
                  ( [ ( Semantic_ir.PVar method_entries_name,
                        Semantic_ir.Prefix
                          ("!", Semantic_ir.Ident method_table_name) );
                    ],
                    invoke ) )
          in
          let expression =
            Semantic_ir.Let
              ( [ (Semantic_ir.PVar dispatch_name, dispatch_fn);
                  ( Semantic_ir.PVar method_table_name,
                    Semantic_ir.Apply
                      (Semantic_ir.Ident "ref", [ Semantic_ir.List [] ]) );
                ],
                Semantic_ir.Sequence
                  [
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident "Lg_runtime.Runtime_multimethod.register",
                        [
                          Semantic_ir.String source_key;
                          Semantic_ir.Ident dispatch_name;
                          default_dispatch;
                        ] );
                    Semantic_ir.Tuple
                      [ Semantic_ir.Ident method_table_name; render ];
                  ] )
          in
          let binding =
            Types.binding ~multimethod:true ~multimethod_definition:expression
              ocaml_name
              (TFn
                 (parameter_tys, TUnknown))
          in
          Ok
            ( scope,
              Env.add source_key binding env,
              next_type,
              Comment ("deferred multimethod " ^ source_key) )
      | (Error _ as error), _ | _, (Error _ as error) -> error)
  | FList
      (FSymbol "defmethod"
      :: FSymbol "print-method"
      :: FSymbol type_name
      :: (FVector _ as params_form)
      :: body_forms) -> (
      match Resolver.lookup_record_type scope env type_name with
      | Error _ as error -> error
      | Ok record -> (
            let source_name = Expression_support.print_method_name record in
            let ocaml_name = Names.sanitize_name source_name in
            match
              Expression_elaborator.compile_fn
                ~param_type_overrides:
                  [ Some (TNamed_record record); Some (TOcaml "Buffer.t") ]
                scope env params_form body_forms
            with
            | Error _ as error -> error
            | Ok implementation ->
                let binding = binding_of_expr ocaml_name implementation in
                let env =
                  Env.add (Names.scoped_key scope source_name) binding env
                in
                Ok
                  ( scope,
                    env,
                    next_type,
                    Value_binding
                    {
                      pattern = Named ocaml_name;
                        expression = implementation.semantic_expr;
                    } )))
  | FList
      (FSymbol "defmethod"
      :: FSymbol method_name
      :: dispatch_form
      :: (FVector _ as params_form)
      :: body_forms)
    when cljs_test_report_method_symbol scope method_name -> (
      let dynamic = Types.dynamic_constraint TUnknown in
      match
        ( Report_dynamic_boundary.compile_form ~compile_expr scope env
            dispatch_form,
          Expression_elaborator.compile_fn
            ~param_type_overrides:[ Some dynamic ]
            scope env params_form body_forms )
      with
      | Ok dispatch, Ok implementation ->
          let method_name = next_cljs_test_report_method_name () in
          let callback_name = method_name ^ "_callback" in
          let event_name = method_name ^ "_event" in
          let callback =
            Semantic_ir.Fun
              ( [ Semantic_ir.PVar event_name ],
                Semantic_ir.Sequence
                  [
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident callback_name,
                        [ Semantic_ir.Ident event_name ] );
                    Semantic_ir.Unit;
                  ] )
          in
          let expression =
            Semantic_ir.Let
              ( [ (Semantic_ir.PVar callback_name, implementation.semantic_expr) ],
                Semantic_ir.Sequence
                  [
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident
                          "Lg_runtime.Runtime_test_report.register",
                        [ dispatch.semantic_expr; callback ] );
                    Semantic_ir.Unit;
                  ] )
          in
          Ok
            ( scope,
              env,
              next_type,
              Value_binding { pattern = Named method_name; expression } )
      | (Error _ as error), _ | _, (Error _ as error) -> error)
  | FList (FSymbol "defmethod" :: FSymbol ("t/report" as method_name) :: _) ->
      Ok
        ( scope,
          env,
          next_type,
          Comment ("test runner handles " ^ method_name) )
  | FList
      (FSymbol "defmethod"
      :: FSymbol method_name
      :: dispatch_form
      :: (FVector params as params_form)
      :: body_forms) -> (
      let source_key = resolve_multimethod_key scope env method_name in
      match Env.find_opt source_key env with
      | None -> Error.error ("unknown multimethod " ^ method_name)
      | Some binding -> (
          match binding.ty with
          | TFn (parameter_tys, _) ->
              let parameter_tys =
                match
                  ( binding.multimethod_method_types,
                    multimethod_dispatch_value_type dispatch_form )
                with
                | [], Some dispatch_ty ->
                    refine_multimethod_dispatch_fields dispatch_ty parameter_tys
                | _ -> parameter_tys
              in
              let arity = List.length parameter_tys in
              if arity <> List.length params then
                Error.error
                  ("defmethod for " ^ method_name ^ " expects "
                 ^ string_of_int arity ^ " parameters")
              else
                 (match
                   ( Multimethod_dynamic_boundary.compile_form ~compile_expr scope
                       env dispatch_form,
                     prepare_fn
                       ~param_type_overrides:
                         (List.map
                            (function
                              | TUnknown | TMeta _ | TVar _ -> None
                              | ty -> Some ty)
                            parameter_tys)
                       ~refine_open_overrides:true
                       ~materialize_open_equality:true scope env params_form
                       body_forms )
                 with
                 | Ok dispatch, Ok parts ->
                     let env, next_type, local_type_items, parts =
                       allocate_function_local_records env next_type parts
                     in
                     let env, next_type, return_type_items, parts =
                       allocate_function_return_record env next_type parts
                     in
                     let method_name = next_multimethod_method_name () in
                     let parameter_tys =
                       parts.param_bindings
                       |> List.map (fun (_key, (binding : binding)) -> binding.ty)
                     in
                     let row_param_types =
                       row_param_type_names ~env binding.ocaml_name parameter_tys
                     in
                     let row_type_items =
                       match binding.multimethod_method_types with
                       | [] -> row_type_items row_param_types parameter_tys
                       | _ -> []
                     in
                     let implementation =
                       fn_code ~self_name:binding.ocaml_name
                         ~row_param_type_names:row_param_types parts
                     in
                     let method_ty = implementation.ty in
                     let unified_ty =
                       match binding.multimethod_method_types with
                       | [] -> Ok method_ty
                       | _ -> (
                           match
                             Type_solver.unify Type_solver.empty binding.ty
                               method_ty
                           with
                           | Ok substitutions ->
                               Ok (Type_solver.apply substitutions binding.ty)
                           | Error _ ->
                               Error.error
                                 ("defmethod " ^ method_name
                                ^ " requires a closed sum type for incompatible method signatures: "
                                ^ Types.source_name binding.ty ^ " versus "
                                ^ Types.source_name method_ty))
                     in
                     let implementation_name = method_name ^ "_implementation" in
                     (match unified_ty with
                      | Error _ as error -> error
                      | Ok unified_ty ->
                          let dispatch_name = method_name ^ "_dispatch" in
                          let method_table =
                            Semantic_ir.Apply
                              ( Semantic_ir.Ident "fst",
                                [ Semantic_ir.Ident binding.ocaml_name ] )
                          in
                          let expression =
                            Semantic_ir.Let
                              ( [
                                  (Semantic_ir.PVar dispatch_name, dispatch.semantic_expr);
                                  ( Semantic_ir.PVar implementation_name,
                                    implementation.semantic_expr );
                                ],
                                Semantic_ir.Sequence
                                  [
                                    Semantic_ir.Apply
                                      ( Semantic_ir.Ident
                                          "Lg_runtime.Runtime_multimethod.register_method",
                                        [
                                          Semantic_ir.String source_key;
                                          Semantic_ir.Ident dispatch_name;
                                        ] );
                                    Semantic_ir.Infix
                                      ( ":=",
                                        method_table,
                                            Semantic_ir.Cons
                                          ( Semantic_ir.Tuple
                                              [ Semantic_ir.Ident dispatch_name;
                                                Semantic_ir.Ident
                                                  implementation_name;
                                              ],
                                            Semantic_ir.Prefix ("!", method_table) ) );
                                    Semantic_ir.Ident implementation_name;
                                  ] )
                          in
                          let definition_items =
                            match
                              ( binding.multimethod_method_types,
                                binding.multimethod_definition )
                            with
                            | [], Some definition ->
                                [
                                  Value_binding
                                    {
                                      pattern = Named binding.ocaml_name;
                                      expression = definition;
                                    };
                                ]
                            | _ -> []
                          in
                          let binding =
                            {
                              binding with
                              ty = unified_ty;
                              row_param_types =
                                (match binding.multimethod_method_types with
                                | [] -> row_param_types
                                | _ -> binding.row_param_types);
                              multimethod_method_types =
                                method_ty :: binding.multimethod_method_types;
                              multimethod_definition = None;
                            }
                          in
                          Ok
                            ( scope,
                              Env.add source_key binding env,
                              next_type,
                              Group
                                (return_type_items @ local_type_items
                               @ row_type_items
                               @ definition_items
                               @ [
                                   Value_binding
                                     { pattern = Named method_name; expression };
                                 ]) ))
                 | (Error _ as error), _ | _, (Error _ as error) -> error)
          | _ -> Error.error (method_name ^ " is not a multimethod")))
  | FList (FSymbol "defmethod" :: _) ->
      Error.error "defmethod currently supports print-method"
  | FList (FSymbol "recursive-definition-group" :: definitions) ->
      let definitions =
        definitions
        |> List.map (function
             | FList
                 (FSymbol (("defn" | "defn-") as definition)
                 :: FSymbol annotation :: (FSymbol _ as name) :: forms)
               when String.starts_with ~prefix:"^" annotation ->
                 (match forms with
                 | (FVector _ as params) :: body_forms ->
                     FList
                       (FSymbol definition :: name :: params
                      :: FList
                           [ FSymbol "__return-type"; FSymbol annotation ]
                      :: body_forms)
                 | _ ->
                     FList
                       (FSymbol definition :: name :: FSymbol annotation
                      :: forms))
             | FList
                 (FSymbol (("defn" | "defn-") as definition)
                 :: FList
                      [
                        FSymbol "__type-hint";
                        FSymbol annotation;
                        FSymbol name;
                      ]
                 :: forms) ->
                 (match forms with
                 | (FVector _ as params) :: body_forms ->
                     FList
                       (FSymbol definition :: FSymbol name :: params
                      :: FList
                           [ FSymbol "__return-type"; FSymbol annotation ]
                      :: body_forms)
                 | _ ->
                     FList
                       (FSymbol definition :: FSymbol name
                      :: FSymbol annotation :: forms))
             | definition -> definition)
      in
      let definition_name_and_params = function
        | FList
            (FSymbol ("defn" | "defn-") :: FSymbol name
            :: (FVector _ as params) :: _) ->
            Some (name, params)
        | FList
            (FSymbol ("defn" | "defn-") :: FSymbol name
            :: FSymbol annotation :: (FVector _ as params) :: _)
          when String.starts_with ~prefix:"^" annotation ->
            Some (name, params)
        | _ -> None
      in
      let env =
        definitions
        |> List.fold_left
             (fun env definition ->
               match definition_name_and_params definition with
               | Some (name, params) ->
                   let key = Names.scoped_key scope name in
                   let ocaml_name = Names.ocaml_binding_name scope name in
                   (match sidecar_function_signature scope env name with
                   | Some ty ->
                       Env.add key
                         (Types.binding ocaml_name
                            (Function_elaborator.infer_named_record scope env
                               ty))
                         env
                   | None -> (
                       match Env.find_opt key env with
                       | Some (binding : binding)
                         when not
                                (Types.equal binding.ty
                                   (TOcaml "__declared_fn")) ->
                           Env.add key (Types.instantiate_binding binding) env
                       | Some _ | None ->
                           Env.add key
                             (Types.binding ocaml_name
                                (match Destructure.parse_param_specs params with
                                | Ok specs ->
                                    let parameter_tys =
                                      List.map
                                        (fun (spec : Destructure.param_spec) ->
                                          Option.value spec.explicit_ty
                                            ~default:(Type_solver.fresh ())
                                          |> Function_elaborator
                                             .infer_named_record scope env)
                                        specs
                                    in
                                    TFn
                                      (parameter_tys, Type_solver.fresh ())
                                | Error _ -> TOcaml "__declared_fn"))
                             env))
               | None -> env)
             env
      in
      let method_definitions, function_definitions =
        List.partition
          (function
            | FList (FSymbol "deftype-methods" :: _) -> true
            | _ -> false)
          definitions
      in
      let generalize_function_bindings env =
        List.fold_left
          (fun env definition ->
            match definition_name_and_params definition with
            | Some (name, _) ->
                let key = Names.scoped_key scope name in
                (match Env.find_opt key env with
                | Some binding ->
                    Env.add key (Types.generalize_binding binding) env
                | None -> env)
            | None -> env)
          env function_definitions
      in
      let scc_inference_params env =
        function_definitions
        |> List.filter_map (fun definition ->
             match definition_name_and_params definition with
             | Some (name, _) ->
                 Env.find_opt (Names.scoped_key scope name) env
                 |> Option.map (fun (binding : binding) -> (name, binding.ty))
             | None -> None)
      in
      let scc_requires_inference env =
        scc_inference_params env
        |> List.exists (fun (_, ty) ->
               Type_solver.variables ty
               |> List.exists (function
                    | Type_solver.Metavariable _ -> true
                    | Type_solver.Declared _ -> false))
      in
      let requires_scc_inference = scc_requires_inference env in
      let active_scc_inference_params env =
        if requires_scc_inference then scc_inference_params env else []
      in
      let apply_scc_substitutions substitutions env =
        Env.fold
          (fun key (binding : binding) env ->
            let ty = Type_solver.apply substitutions binding.ty in
            if ty == binding.ty then env
            else
              Env.add key
                (Types.generalize_binding { binding with ty; scheme = None })
                env)
          env env
      in
      let refine_scc_inference inferred env =
        let substitutions =
          scc_inference_params env
          |> List.fold_left
               (fun substitutions (name, ty) ->
                 Result.bind substitutions (fun substitutions ->
                     match List.assoc_opt name inferred with
                     | Some inferred_ty ->
                         Type_solver.unify substitutions ty inferred_ty
                     | None -> Ok substitutions))
               (Ok Type_solver.empty)
        in
        match substitutions with
        | Error _ -> env
        | Ok substitutions -> apply_scc_substitutions substitutions env
      in
      let link_scc_forwarded_parameters env =
        let function_types = scc_inference_params env in
        let source_name_matches name expected =
          String.equal name expected
          || String.ends_with ~suffix:("/" ^ expected) name
        in
        let rec pattern_bound_names = function
          | FSymbol name -> if String.equal name "_" then [] else [ name ]
          | FList [ FSymbol "__type-hint"; FSymbol _; pattern ] ->
              pattern_bound_names pattern
          | FVector forms -> List.concat_map pattern_bound_names forms
          | FMap _ as pattern -> Destructure.pattern_names pattern
          | FList (FSymbol _constructor :: payload_patterns) ->
              List.concat_map pattern_bound_names payload_patterns
          | _ -> []
        in
        let function_type name =
          match List.assoc_opt name function_types with
          | Some ty -> Some ty
          | None -> (
              match Env.find_opt (Names.scoped_key scope name) env with
              | Some (binding : binding) -> Some binding.ty
              | None -> (
                  match Env.find_opt name env with
                  | Some (binding : binding) -> Some binding.ty
                  | None -> None))
        in
        let scc_return_type name =
          match List.assoc_opt name function_types with
          | Some (TFn (_, return_ty)) -> Some return_ty
          | Some _ | None -> None
        in
        let unify_scc_return substitutions name expected_ty =
          match scc_return_type name with
          | Some return_ty ->
              Type_solver.unify substitutions return_ty expected_ty
              |> Result.value ~default:substitutions
          | None -> substitutions
        in
        let rec walk bound local_params substitutions = function
          | FList (FSymbol "quote" :: _) -> substitutions
          | FList
              (FSymbol "fn" :: FVector parameters :: body_forms)
          | FList
              (FSymbol "fn" :: FSymbol _ :: FVector parameters :: body_forms)
            ->
              let bound =
                Destructure.pattern_names (FVector parameters) @ bound
              in
              List.fold_left (walk bound local_params) substitutions body_forms
          | FList
              (FSymbol ("let" | "let*" | "loop")
              :: FVector bindings :: body_forms) ->
              let rec walk_bindings bound substitutions = function
                | pattern :: value :: rest ->
                    let substitutions =
                      walk bound local_params substitutions value
                    in
                    walk_bindings
                      (Destructure.pattern_names pattern @ bound)
                      substitutions rest
                | _ -> (bound, substitutions)
              in
              let bound, substitutions =
                walk_bindings bound substitutions bindings
              in
              List.fold_left (walk bound local_params) substitutions body_forms
          | FList (FSymbol match_name :: target :: clauses)
            when source_name_matches match_name "match"
                 || source_name_matches match_name "__lg_match" ->
              let substitutions = walk bound local_params substitutions target in
              let rec walk_clauses substitutions = function
                | pattern :: result :: rest ->
                    let bound =
                      pattern_bound_names pattern @ bound
                    in
                    walk_clauses
                      (walk bound local_params substitutions result)
                      rest
                | [ pattern ] -> walk bound local_params substitutions pattern
                | [] -> substitutions
              in
              walk_clauses substitutions clauses
          | FList (FSymbol name :: arguments) as form ->
              let substitutions =
                if List.mem name bound then substitutions
                else
                  match function_type name with
                  | Some (TFn (parameter_tys, _))
                    when List.length parameter_tys = List.length arguments ->
                      let substitutions =
                        List.fold_left2
                          (fun substitutions parameter_ty argument ->
                            match argument with
                            | FSymbol argument_name
                              when not (List.mem argument_name bound) -> (
                                match
                                  List.assoc_opt argument_name local_params
                                with
                                | Some argument_ty ->
                                    Type_solver.unify substitutions
                                      parameter_ty argument_ty
                                    |> Result.value ~default:substitutions
                                | None -> substitutions)
                            | _ -> substitutions)
                          substitutions parameter_tys arguments
                      in
                      List.fold_left2
                        (fun substitutions parameter_ty -> function
                          | FList (FSymbol callee :: _)
                            when not (List.mem callee bound) ->
                              unify_scc_return substitutions callee
                                parameter_ty
                          | _ -> substitutions)
                        substitutions parameter_tys arguments
                  | Some _ | None -> substitutions
              in
              (match form with
              | FList (_ :: arguments) ->
                  List.fold_left (walk bound local_params) substitutions arguments
              | _ -> assert false)
          | FList forms | FVector forms ->
              List.fold_left (walk bound local_params) substitutions forms
          | FMap entries ->
              List.fold_left
                (fun substitutions (key, value) ->
                  walk bound local_params
                    (walk bound local_params substitutions key)
                    value)
                substitutions entries
          | FSymbol _ | FCoreSymbol _ | FKeyword _ | FString _ | FRegex _
          | FInt _ | FFloat _ | FDecimal _ | FChar _ | FBool _ ->
              substitutions
        in
        let substitutions =
          List.fold_left
            (fun substitutions -> function
              | FList
                  (FSymbol ("defn" | "defn-") :: FSymbol name
                  :: params :: body_forms) -> (
                  match
                    ( Env.find_opt (Names.scoped_key scope name) env,
                      Destructure.parse_param_specs params )
                  with
                  | Some { ty = TFn (parameter_tys, _); _ }, Ok specs
                    when List.length parameter_tys = List.length specs ->
                      let local_params =
                        List.map2
                          (fun (spec : Destructure.param_spec) ty ->
                            (spec.source_name, ty))
                          specs parameter_tys
                      in
                      let substitutions =
                        List.fold_left (walk [] local_params) substitutions
                          body_forms
                      in
                      (match
                         ( Env.find_opt (Names.scoped_key scope name) env,
                           List.rev body_forms )
                       with
                      | ( Some { ty = TFn (_, return_ty); _ },
                          FList (FSymbol callee :: _) :: _ )
                        when not (List.mem_assoc callee local_params) ->
                          unify_scc_return substitutions callee return_ty
                      | _ -> substitutions)
                  | _ -> substitutions)
              | _ -> substitutions)
            Type_solver.empty function_definitions
        in
        apply_scc_substitutions substitutions env
      in
      let infer_scc_parameters env =
        if not requires_scc_inference then Ok env
        else
        let rec infer env = function
          | [] -> Ok env
          | FList
              (FSymbol ("defn" | "defn-") :: FSymbol name
              :: (FVector _ as params) :: body_forms)
            :: rest ->
              let key = Names.scoped_key scope name in
              let predeclared_param_tys =
                match Env.find_opt key env with
                | Some { ty = TFn (parameter_tys, _); _ } -> parameter_tys
                | Some _ | None -> []
              in
              let inferred_env = ref env in
              let refine_inferred_env inferred env =
                let env = refine_scc_inference inferred env in
                inferred_env := env;
                env
              in
              Result.bind
                (prepare_fn
                   ~param_type_overrides:
                     (List.map Option.some predeclared_param_tys)
                   ~additional_inference_params:
                     (active_scc_inference_params env)
                   ~refine_inferred_env ~infer_parameters_only:true
                   ~refine_open_overrides:true scope env params body_forms)
                (fun parts ->
                  let env = !inferred_env in
                  match Env.find_opt key env with
                  | Some (binding : binding) -> (
                      match binding.ty with
                      | TFn (_, return_ty) ->
                          let parameter_tys =
                            parts.param_bindings
                            |> List.map (fun (_key, (binding : binding)) ->
                                   binding.ty)
                          in
                          (match
                             Type_solver.unify Type_solver.empty binding.ty
                               (TFn (parameter_tys, return_ty))
                           with
                          | Ok substitutions ->
                              infer
                                (apply_scc_substitutions substitutions env)
                                rest
                          | Error _ -> infer env rest)
                      | _ -> infer env rest)
                  | None -> infer env rest)
          | _ :: rest -> infer env rest
        in
        infer env function_definitions
      in
      let recursive_bindings item =
        let items = match item with Group items -> items | item -> [ item ] in
        let rec collect bindings = function
          | [] -> Ok (List.rev bindings)
          | Value_binding { pattern = Named name; expression } :: rest ->
              collect
                ({
                   name;
                   identity = None;
                   type_annotation = None;
                   expression;
                 }
                :: bindings)
                rest
          | Deferred_value_binding { name; expression; _ } :: rest ->
              collect
                ({
                   name;
                   identity = None;
                   type_annotation = None;
                   expression;
                 }
                :: bindings)
                rest
          | Recursive_value_binding
              { name; identity; type_annotation; expression } :: rest ->
              collect
                ({ name; identity; type_annotation; expression } :: bindings)
                rest
          | Recursive_value_bindings recursive :: rest ->
              collect (List.rev_append recursive bindings) rest
          | _ :: _ ->
              Error.error
                "recursive deftype methods must compile to named functions"
        in
        collect [] items
      in
      let rec compile_methods env next_type bindings = function
        | [] -> Ok (env, next_type, bindings)
        | method_form :: rest -> (
            match compile scope env next_type method_form with
            | Error _ as error -> error
            | Ok (_, env, next_type, item) -> (
                match recursive_bindings item with
                | Error _ as error -> error
                | Ok methods ->
                    compile_methods env next_type
                      (List.rev_append methods bindings)
                      rest))
      in
      let refine_predeclared_bindings env name predeclared_ty actual_ty =
        let open_counted_return = function
          | ty -> (
              match Types.protocol_constraint_info ty with
              | Some (protocol_id, _, value_ty)
                when Protocol_id.equal protocol_id Core_protocols.counted_id ->
                  contains_unresolved_type value_ty
              | Some _ | None -> false)
        in
        let seqable_return = function
          | TList _ | TVector _ | TSet _ | TSeq _ | TArray _ | TString ->
              true
          | ty ->
              Option.is_some (Types.next_seq_element ty)
              || Option.is_some (Types.seqable_constraint_info ty)
        in
        let counted_return_satisfied_by_seqable =
          match (predeclared_ty, actual_ty) with
          | TFn (predeclared_params, predeclared_return),
            TFn (actual_params, actual_return)
            when List.length predeclared_params = List.length actual_params
                 && open_counted_return predeclared_return
                 && seqable_return actual_return ->
              Type_solver.unify Type_solver.empty
                (TTuple predeclared_params) (TTuple actual_params)
              |> Result.to_option
          | _ -> None
        in
        let substitutions =
          match counted_return_satisfied_by_seqable with
          | Some substitutions -> Ok substitutions
          | None ->
              Type_solver.unify Type_solver.empty predeclared_ty actual_ty
        in
        match substitutions with
        | Error _ ->
            Error.error
              ("recursive function " ^ name
             ^ " implementation does not match its inferred signature: "
             ^ Types.source_name predeclared_ty ^ " vs "
             ^ Types.source_name actual_ty)
        | Ok substitutions ->
            Ok (apply_scc_substitutions substitutions env)
      in
      let rec compile_definitions env next_type row_items bindings = function
        | [] ->
            let env = generalize_function_bindings env in
            Ok
              ( scope,
                env,
                next_type,
                Group
                  (List.rev row_items
                  @ [ Recursive_value_bindings (List.rev bindings) ]) )
        | FList
            (FSymbol ("defn" | "defn-")
            :: (FSymbol name as name_form)
            :: (FList _ as first_clause)
            :: remaining_clauses)
          :: rest -> (
            let ocaml_name = Names.ocaml_binding_name scope name in
            match
              Expression_elaborator.prepare_multi_arity_fn ~ocaml_name scope env
                ~infer_state_return:true name
                (first_clause :: remaining_clauses)
            with
            | Error _ as error -> error
            | Ok prepared ->
                let env, next_type, local_type_items, prepared =
                  allocate_multi_arity_local_records env next_type prepared
                in
                let targets, overload_row_param_types, rows, arity_bindings =
                  Expression_elaborator.lower_prepared_multi_arity prepared
                in
                let binding =
                  Types.binding ~overload_targets:targets
                    ~overload_row_param_types ocaml_name
                    prepared.expr.ty
                in
                let env =
                  Env.add (Names.scoped_key scope name) binding env
                in
                let dispatch_binding =
                  {
                    name = ocaml_name;
                    identity =
                      Source_context.find_identity name_form;
                    type_annotation = None;
                    expression = prepared.expr.semantic_expr;
                  }
                in
                let new_bindings = arity_bindings @ [ dispatch_binding ] in
                compile_definitions env next_type
                  (List.rev_append (local_type_items @ rows) row_items)
                  (List.rev_append new_bindings bindings)
                  rest)
        | FList
            (FSymbol ("defn" | "defn-")
            :: (FSymbol name as name_form)
            :: params :: body_forms)
          :: rest -> (
            let explicit_return_ty, body_forms =
              match body_forms with
              | FList [ FSymbol "__return-type"; FSymbol annotation ] :: rest -> (
                  match Type_annotation.of_param_annotation annotation with
                  | Ok ty ->
                      ( Some
                          (Function_elaborator.infer_named_record scope env ty),
                        rest )
                  | Error _ -> (None, body_forms))
              | _ -> (None, body_forms)
            in
            let ocaml_name = Names.ocaml_binding_name scope name in
            let inferred_scc_env = ref env in
            let refine_inferred_env inferred env =
              let env = refine_scc_inference inferred env in
              inferred_scc_env := env;
              env
            in
            let recursive = function_is_recursive scope name body_forms in
            let predeclared_type =
              match sidecar_function_signature scope env name with
              | Some ty ->
                  Some
                    (Function_elaborator.infer_named_record scope env ty)
              | None ->
                  Env.find_opt (Names.scoped_key scope name) env
                  |> Option.map (fun (binding : binding) ->
                         Function_elaborator.infer_named_record scope env
                           binding.ty)
            in
            let declared_return_ty =
              match explicit_return_ty with
              | Some _ as return_ty -> return_ty
              | None -> (
              match predeclared_type with
              | Some (TFn (_, return_ty))
                when not (Types.equal return_ty TUnknown)
                     && not (Types.is_dynamic return_ty)
                     && not (contains_unresolved_type return_ty)
                     &&
                     (match return_ty with
                     | TMeta _ | TVar _ -> false
                     | _ -> true) ->
                  Some return_ty
              | Some _ | None -> None)
            in
            let predeclared_param_tys =
              match predeclared_type with
              | Some (TFn (parameter_tys, _)) -> Some parameter_tys
              | Some _ | None -> None
            in
            let linked_predeclared_return_ty =
              match (explicit_return_ty, predeclared_type) with
              | None, Some (TFn (parameter_tys, return_ty)) ->
                  linked_parameter_return parameter_tys return_ty
              | Some _, _ | None, (Some _ | None) -> None
            in
            let expected_return_ty =
              match declared_return_ty with
              | Some _ as return_ty -> return_ty
              | None -> linked_predeclared_return_ty
            in
            let prepared =
              match (recursive, params, declared_return_ty) with
              | true, FVector _, Some return_ty ->
                  prepare_recursive_fn ~ocaml_name scope env name return_ty
                    params body_forms
              | true, FVector _, None ->
                  prepare_inferred_recursive_fn ~ocaml_name scope env name
                    params body_forms
              | _ ->
                  let param_type_overrides =
                    predeclared_param_tys
                    |> Option.value ~default:[]
                    |> List.map Option.some
                  in
                  let refine_open_overrides =
                    predeclared_param_tys
                    |> Option.value ~default:[]
                    |> List.exists (fun ty ->
                           Type_solver.variables ty
                           |> List.exists (function
                                | Type_solver.Metavariable _ -> true
                                | Type_solver.Declared _ -> false))
                  in
                  prepare_fn ~param_type_overrides
                    ~additional_inference_params:
                      (active_scc_inference_params env)
                    ~refine_inferred_env ~refine_open_overrides
                    ~materialize_open_equality:false
                    ?expected_return_ty scope env params body_forms
            in
            match prepared with
            | Error error ->
                Error
                  (Error.with_location_if_missing
                     (Source_context.find name_form) error)
            | Ok parts ->
                let env = !inferred_scc_env in
                let env, next_type, local_type_items, parts =
                  allocate_function_local_records env next_type parts
                in
                let env, next_type, return_type_items, parts =
                  allocate_function_return_record env next_type parts
                in
                let param_tys =
                  parts.param_bindings
                  |> List.map (fun (_key, (binding : binding)) -> binding.ty)
                in
                let row_param_types =
                  row_param_type_names ~env ocaml_name param_tys
                in
                let expr =
                  fn_code ~demote:(Option.is_none predeclared_param_tys)
                    ~self_name:ocaml_name
                    ~row_param_type_names:row_param_types parts
                in
                let binding =
                  Expression_support.binding_of_expr ~row_param_types
                    ocaml_name expr
                in
                let refined_env =
                  match predeclared_type with
                  | Some predeclared_ty ->
                      refine_predeclared_bindings env name predeclared_ty
                        expr.ty
                  | None -> Ok env
                in
                Result.bind refined_env (fun env ->
                    let env =
                      Env.add (Names.scoped_key scope name) binding env
                    in
                    let type_annotation =
                      recursive_type_annotation scope env name
                    in
                    let rows =
                      return_type_items @ local_type_items
                      @ row_type_items row_param_types param_tys
                    in
                    let recursive_binding =
                      {
                        name = ocaml_name;
                        identity =
                          Source_context.find_identity name_form;
                        type_annotation =
                          type_annotation;
                        expression = expr.semantic_expr;
                      }
                    in
                    compile_definitions env next_type
                      (List.rev_append rows row_items)
                      (recursive_binding :: bindings)
                      rest))
        | _ :: _ ->
            Error.error
              "recursive definition groups only support functions and deftype methods"
      in
      let env =
        if requires_scc_inference then link_scc_forwarded_parameters env
        else env
      in
      Result.bind (infer_scc_parameters env) (fun env ->
      Result.bind (compile_methods env next_type [] method_definitions)
        (fun (env, next_type, method_bindings) ->
          let rec try_definition_orders first_error prefix = function
            | [] -> (
                match first_error with
                | Some error -> Error error
                | None ->
                    compile_definitions env next_type [] method_bindings [])
            | definition :: rest -> (
                let ordered = definition :: (rest @ List.rev prefix) in
                match
                  compile_definitions env next_type [] method_bindings ordered
                with
                | Ok _ as result -> result
                | Error error ->
                    try_definition_orders
                      (Option.value first_error ~default:error |> Option.some)
                      (definition :: prefix) rest)
          in
          try_definition_orders None [] function_definitions))
  | FList
      [
        FSymbol "defn-signature";
        FList
          (FSymbol ("defn" | "defn-")
          :: FSymbol name
          :: (FList _ as first_clause)
          :: remaining_clauses);
      ] -> (
      let ocaml_name = Names.ocaml_binding_name scope name in
      match
        Expression_elaborator.prepare_multi_arity_fn ~ocaml_name scope env name
          (first_clause :: remaining_clauses)
      with
      | Error _ ->
          Ok
            ( scope,
              env,
              next_type,
              Comment ("deferred function signature " ^ name) )
      | Ok prepared ->
          let targets, overload_row_param_types, _, _ =
            Expression_elaborator.lower_prepared_multi_arity prepared
          in
          let binding =
            Types.binding ~overload_targets:targets ~overload_row_param_types
              ocaml_name prepared.expr.ty
          in
          Ok
            ( scope,
              Env.add (Names.scoped_key scope name) binding env,
              next_type,
              Comment ("function signature " ^ name) ))
  | FList
      [
        FSymbol "defn-signature";
        FList
          (FSymbol ("defn" | "defn-") :: FSymbol name :: params :: body_forms);
      ] -> (
      let ocaml_name = Names.ocaml_binding_name scope name in
      let recursive = function_is_recursive scope name body_forms in
      let prepared =
        match (recursive, params) with
        | true, FVector _ ->
            prepare_inferred_recursive_fn ~ocaml_name scope env name params
              body_forms
        | _ ->
            prepare_fn ~materialize_open_equality:true scope env params
              body_forms
      in
      match prepared with
      | Error _ ->
          Ok
            ( scope,
              env,
              next_type,
              Comment ("deferred function signature " ^ name) )
      | Ok parts ->
          let param_tys =
            parts.param_bindings
            |> List.map (fun (_key, (binding : binding)) -> binding.ty)
          in
          let row_param_types = row_param_type_names ~env ocaml_name param_tys in
          let expression =
            fn_code ~self_name:ocaml_name
              ~row_param_type_names:row_param_types parts
          in
          let binding =
            binding_of_expr ~row_param_types ocaml_name expression
          in
          Ok
            ( scope,
              Env.add (Names.scoped_key scope name) binding env,
              next_type,
              Comment ("function signature " ^ name) ))
  | FList
      (FSymbol "module-signature"
      :: (FSymbol signature_name as name_form)
      :: item_forms) ->
      compile_module_signature
        ?location:(Source_context.find name_form)
        scope env next_type signature_name item_forms
  | FList (FSymbol "module-signature" :: _) ->
      Error.error "module-signature expects a name and signature items"
  | FList
      [ FSymbol "optional-sequential-adapter";
        FKeyword storage_annotation;
        FKeyword element_annotation;
        FSymbol adapter ] -> (
      match
        ( Type_annotation.of_keyword storage_annotation,
          Type_annotation.of_keyword element_annotation )
      with
      | (Error _ as error), _ | _, (Error _ as error) -> error
      | Ok storage_ty, Ok element_ty ->
          let storage_ty =
            Function_elaborator.infer_named_record scope env storage_ty
          in
          let element_ty =
            Function_elaborator.infer_named_record scope env element_ty
          in
          let adapter =
            match Env.find_opt (Names.scoped_key scope adapter) env with
            | Some binding -> binding.Types.ocaml_name
            | None -> adapter
          in
          Ok
            ( scope,
              Env.add_optional_sequential_adapter storage_ty element_ty adapter
                env,
              next_type,
              Comment
                ("optional sequential adapter " ^ Types.source_name storage_ty)
            ))
  | FList (FSymbol "optional-sequential-adapter" :: _) ->
      Error.error
        "optional-sequential-adapter expects storage type, element type, and adapter"
  | FList
      [ FSymbol "optional-map-adapter";
        FKeyword storage_annotation;
        FKeyword key_annotation;
        FKeyword value_annotation;
        FSymbol adapter ] -> (
      match
        ( Type_annotation.of_keyword storage_annotation,
          Type_annotation.of_keyword key_annotation,
          Type_annotation.of_keyword value_annotation )
      with
      | (Error _ as error), _, _
      | _, (Error _ as error), _
      | _, _, (Error _ as error) ->
          error
      | Ok storage_ty, Ok key_ty, Ok value_ty ->
          let infer = Function_elaborator.infer_named_record scope env in
          let storage_ty = infer storage_ty in
          let key_ty = infer key_ty in
          let value_ty = infer value_ty in
          let adapter =
            match Env.find_opt (Names.scoped_key scope adapter) env with
            | Some binding -> binding.Types.ocaml_name
            | None -> adapter
          in
          Ok
            ( scope,
              Env.add_optional_map_adapter storage_ty key_ty value_ty adapter
                env,
              next_type,
              Comment ("optional map adapter " ^ Types.source_name storage_ty)
            ))
  | FList (FSymbol "optional-map-adapter" :: _) ->
      Error.error
        "optional-map-adapter expects storage, key, value types, and adapter"
  | FList
      [ FSymbol "nil-value-adapter";
        FKeyword value_annotation;
        FSymbol adapter ] -> (
      match Type_annotation.of_keyword value_annotation with
      | Error _ as error -> error
      | Ok value_ty ->
          let value_ty =
            Function_elaborator.infer_named_record scope env value_ty
          in
          let adapter_binding =
            match Env.find_opt (Names.scoped_key scope adapter) env with
            | Some binding -> Some (binding.ty, binding.ocaml_name)
            | None ->
                Signature_overlay.find_value adapter (Env.signatures env)
                |> Option.map (fun ty -> (ty, adapter))
          in
          (match adapter_binding with
          | Some (TFn ([], return_ty), ocaml_name)
            when Types.equal return_ty value_ty ->
              Ok
                ( scope,
                  Env.add_nil_value_adapter value_ty ocaml_name env,
                  next_type,
                  Comment ("nil value adapter " ^ Types.source_name value_ty)
                )
          | Some _ ->
              Error.error
                "nil-value-adapter must have the exact type () -> T"
          | None ->
              Error.error ("unknown nil-value-adapter function " ^ adapter)))
  | FList (FSymbol "nil-value-adapter" :: _) ->
      Error.error "nil-value-adapter expects value type and adapter"
  | FList
      [ FSymbol "truthiness-adapter";
        FKeyword value_annotation;
        FSymbol adapter ] -> (
      match Type_annotation.of_keyword value_annotation with
      | Error _ as error -> error
      | Ok value_ty ->
          let value_ty =
            Function_elaborator.infer_named_record scope env value_ty
          in
          let adapter_binding =
            match Env.find_opt (Names.scoped_key scope adapter) env with
            | Some binding -> Some (binding.ty, binding.ocaml_name)
            | None ->
                Signature_overlay.find_value adapter (Env.signatures env)
                |> Option.map (fun ty -> (ty, adapter))
          in
          (match adapter_binding with
          | Some (TFn ([ parameter_ty ], TBool), ocaml_name)
            when Types.equal parameter_ty value_ty ->
              Ok
                ( scope,
                  Env.add_truthiness_adapter value_ty ocaml_name env,
                  next_type,
                  Comment ("truthiness adapter " ^ Types.source_name value_ty)
                )
          | Some _ ->
              Error.error
                "truthiness-adapter must have the exact type T -> bool"
          | None ->
              Error.error ("unknown truthiness-adapter function " ^ adapter)))
  | FList (FSymbol "truthiness-adapter" :: _) ->
      Error.error "truthiness-adapter expects value type and adapter"
  | FList
      [ FSymbol "exception-data-adapter";
        FKeyword value_annotation;
        FSymbol adapter ] -> (
      match Type_annotation.of_keyword value_annotation with
      | Error _ as error -> error
      | Ok value_ty ->
          let value_ty =
            Function_elaborator.infer_named_record scope env value_ty
          in
          let adapter_binding =
            match Env.find_opt (Names.scoped_key scope adapter) env with
            | Some binding -> Some (binding.ty, binding.ocaml_name)
            | None ->
                Signature_overlay.find_value adapter (Env.signatures env)
                |> Option.map (fun ty -> (ty, adapter))
          in
          let field_types =
            match value_ty with
            | TRecord fields | TNamed_record { fields; _ } ->
                Some (List.map (fun (field : field) -> field.ty) fields)
            | _ -> None
          in
          let matches_fields parameter_tys =
            match field_types with
            | Some field_tys ->
                List.length parameter_tys = List.length field_tys
                && List.for_all2 Types.equal parameter_tys field_tys
            | None -> false
          in
          (match adapter_binding with
          | Some (TFn (parameter_tys, return_ty), ocaml_name)
            when Types.equal return_ty (TOcaml "Lg_edn_backend.t")
                 && (match parameter_tys with
                    | [ parameter_ty ] -> Types.equal parameter_ty value_ty
                    | _ -> false) ->
              Ok
                ( scope,
                  Env.add_exception_data_adapter value_ty
                    (Env.Direct ocaml_name) env,
                  next_type,
                  Comment
                    ("exception data adapter " ^ Types.source_name value_ty) )
          | Some (TFn (parameter_tys, return_ty), ocaml_name)
            when Types.equal return_ty (TOcaml "Lg_edn_backend.t")
                 && matches_fields parameter_tys ->
              Ok
                ( scope,
                  Env.add_exception_data_adapter value_ty
                    (Env.Fields ocaml_name) env,
                  next_type,
                  Comment
                    ("exception data fields adapter "
                    ^ Types.source_name value_ty) )
          | Some (TFn (parameter_tys, _), _)
            when (match parameter_tys with
                 | [ parameter_ty ] -> Types.equal parameter_ty value_ty
                 | _ -> matches_fields parameter_tys) ->
              Error.error
                "exception-data-adapter must return Lg_edn_backend.t"
          | Some _ ->
              Error.error
                "exception-data-adapter parameters must match the declared value or its fields"
          | None ->
              Error.error
                ("unknown exception-data-adapter function " ^ adapter)))
  | FList (FSymbol "exception-data-adapter" :: _) ->
      Error.error
        "exception-data-adapter expects value type and adapter"
  | FList
      [ FSymbol "empty-map-default";
        FKeyword target_annotation;
        FSymbol factory ] -> (
      match Type_annotation.of_keyword target_annotation with
      | Error _ as error -> error
      | Ok target_ty ->
          let target_ty =
            Function_elaborator.infer_named_record scope env target_ty
          in
          let factory =
            match Env.find_opt (Names.scoped_key scope factory) env with
            | Some binding -> binding.Types.ocaml_name
            | None -> factory
          in
          Ok
            ( scope,
              Env.add_empty_map_default target_ty factory env,
              next_type,
              Comment ("empty map default " ^ Types.source_name target_ty) ))
  | FList (FSymbol "empty-map-default" :: _) ->
      Error.error "empty-map-default expects target type and factory"
  | FList
      (FSymbol constructor_directive
      :: FKeyword target_annotation
      :: constructor_forms)
    when String.equal constructor_directive "closed-sum-constructors"
         || String.equal constructor_directive
              "contextual-closed-sum-constructors" -> (
      let parse_constructor = function
        | FSymbol constructor -> Ok (constructor, [])
        | FList (FSymbol constructor :: payload_forms) ->
            let rec parse_payloads acc = function
              | [] -> Ok (constructor, List.rev acc)
              | FKeyword annotation :: rest -> (
                  match Type_annotation.of_keyword annotation with
                  | Error _ as error -> error
                  | Ok ty ->
                      let ty =
                        Function_elaborator.infer_named_record scope env ty
                      in
                      parse_payloads (ty :: acc) rest)
              | _ :: _ ->
                  Error.error
                    "closed-sum constructor payloads must be type annotations"
            in
            parse_payloads [] payload_forms
        | _ ->
            Error.error
              "closed-sum constructors must be symbols or constructor lists"
      in
      let rec parse acc = function
        | [] -> Ok (List.rev acc)
        | form :: rest -> (
            match parse_constructor form with
            | Error _ as error -> error
            | Ok constructor -> parse (constructor :: acc) rest)
      in
      match (Type_annotation.of_keyword target_annotation, parse [] constructor_forms) with
      | (Error _ as error), _ | _, (Error _ as error) -> error
      | Ok _, Ok [] ->
          Error.error "closed-sum-constructors expects at least one constructor"
      | Ok target_ty, Ok constructors ->
          let target_ty =
            Function_elaborator.infer_named_record scope env target_ty
          in
          let env =
            if
              String.equal constructor_directive
                "contextual-closed-sum-constructors"
            then Env.add_closed_sum_constructors target_ty constructors env
            else Env.add_predicate_sum_constructors target_ty constructors env
          in
          Ok
            ( scope,
              env,
              next_type,
              Comment ("closed sum constructors " ^ Types.source_name target_ty)
            ))
  | FList (FSymbol "closed-sum-constructors" :: _) ->
      Error.error
        "closed-sum-constructors expects a target type and constructors"
  | FList (FSymbol "contextual-closed-sum-constructors" :: _) ->
      Error.error
        "contextual-closed-sum-constructors expects a target type and constructors"
  | FList [ FSymbol "signature"; FSymbol name; fields ] ->
      compile_signature scope env next_type name fields
  | FList
      [ FSymbol "signature"; FSymbol name; type_parameters_form; fields ] -> (
      match parse_type_parameters type_parameters_form with
      | Error _ as error -> error
      | Ok type_parameters ->
          compile_signature ~type_parameters scope env next_type name fields)
  | FList (FSymbol "signature" :: _) ->
      Error.error
        "signature expects a name, optional type parameters, and a type or \
         record field map"
  | FList (FSymbol "dynamic-codec" :: _) ->
      Error.error
        "dynamic-codec is not supported; use explicit sum constructors"
  | FList [ FSymbol "extern-type"; (FSymbol name as name_form) ] ->
      Type_definition_elaborator.compile_opaque_type
        ?location:(Source_context.find name_form) scope env next_type name
  | FList (FSymbol "extern-type" :: _) ->
      Error.error "extern-type expects one type name"
  | FList [ FSymbol "type-alias"; (FSymbol name as name_form); manifest_form ]
    ->
      compile_type_alias
        ?location:(Source_context.find name_form)
        scope env next_type name [] manifest_form
  | FList
      [
        FSymbol "type-alias";
        (FSymbol name as name_form);
        FVector parameter_forms;
        manifest_form;
      ] -> (
      match parse_type_parameters (FVector parameter_forms) with
      | Error _ as err -> err
      | Ok type_parameters ->
          compile_type_alias
            ?location:(Source_context.find name_form)
            scope env next_type name type_parameters manifest_form)
  | FList
      (FSymbol "external-record"
      :: (FSymbol name as name_form)
      :: FVector parameter_forms
      :: field_forms) -> (
      match parse_type_parameters (FVector parameter_forms) with
      | Error _ as err -> err
      | Ok type_parameters ->
          Result.map
            (fun (scope, env, next_type, _) ->
              (scope, env, next_type, Comment ("external record " ^ name)))
            (compile_external_record
               ?location:(Source_context.find name_form)
               env next_type name type_parameters field_forms)
          |> Result.map (fun (_, env, next_type, item) ->
                 (scope, env, next_type, item)))
  | FList
      (FSymbol "external-record"
      :: (FSymbol name as name_form)
      :: field_forms) ->
      Result.map
        (fun (scope, env, next_type, _) ->
          (scope, env, next_type, Comment ("external record " ^ name)))
        (compile_external_record
           ?location:(Source_context.find name_form)
           env next_type name [] field_forms)
      |> Result.map (fun (_, env, next_type, item) ->
             (scope, env, next_type, item))
  | FList (FSymbol "external-record" :: _) ->
      Error.error "external-record expects a type name and fields"
  | FList
      (FSymbol "type-record"
      :: (FSymbol name as name_form)
      :: FVector parameter_forms
      :: field_forms) -> (
      match parse_type_parameters (FVector parameter_forms) with
      | Error _ as err -> err
      | Ok type_parameters ->
          compile_type_record
            ?location:(Source_context.find name_form)
            scope env next_type name type_parameters field_forms)
  | FList (FSymbol "type-record" :: (FSymbol name as name_form) :: field_forms)
    ->
      compile_type_record
        ?location:(Source_context.find name_form)
        scope env next_type name [] field_forms
  | FList (FSymbol "type-record" :: _) ->
      Error.error "type-record expects a name and fields"
  | FList
      (FSymbol "type-variant"
      :: (FSymbol name as name_form)
      :: FVector parameter_forms
      :: constructor_forms) -> (
      match parse_type_parameters (FVector parameter_forms) with
      | Error _ as err -> err
      | Ok type_parameters ->
          compile_type_variant
            ?location:(Source_context.find name_form)
            scope env next_type name type_parameters constructor_forms)
  | FList
      (FSymbol "type-variant"
      :: (FSymbol name as name_form)
      :: constructor_forms) ->
      compile_type_variant
        ?location:(Source_context.find name_form)
        scope env next_type name [] constructor_forms
  | FList [ FSymbol "open"; (FSymbol module_path as module_form) ] ->
      let env = open_module_bindings scope env module_path in
      Ok
        ( scope,
          env,
          next_type,
          Open_module
            {
              module_name = Names.module_path_to_ocaml module_path;
              location = Source_context.find module_form;
            } )
  | FList [ FSymbol "include"; (FSymbol module_path as module_form) ] ->
      let env = open_module_bindings scope env module_path in
      Ok
        ( scope,
          env,
          next_type,
          Include_module
            {
              module_name = Names.module_path_to_ocaml module_path;
              location = Source_context.find module_form;
            } )
  | FList (FSymbol "include" :: _) -> Error.error "include expects one module"
  | FList
      [
        FSymbol "module-alias";
        (FSymbol alias_name as alias_form);
        (FSymbol target_name as target_form);
      ] ->
      compile_module_alias
        ?location:(Source_context.find alias_form)
        ?target_location:(Source_context.find target_form)
        scope env next_type alias_name target_name
  | FList (FSymbol "module-alias" :: _) ->
      Error.error "module-alias expects alias and target modules"
  | FList
      (FSymbol "module-functor"
      :: (FSymbol functor_name as name_form)
      :: parameter_form :: body_forms) ->
      compile_module_functor
        ?location:(Source_context.find name_form)
        scope env next_type functor_name parameter_form body_forms
  | FList (FSymbol "module-functor" :: _) ->
      Error.error
        "module-functor expects a name, [parameter signature ...], and body"
  | FList
      (FSymbol "module-apply"
      :: (FSymbol module_name as name_form)
      :: (FSymbol functor_name as functor_form)
      :: (_ :: _ as argument_forms)) -> (
      let rec parse_arguments acc = function
        | [] -> Ok (List.rev acc)
        | (FSymbol name as form) :: rest ->
            parse_arguments
              ({ module_name = name; location = Source_context.find form }
              :: acc)
              rest
        | _ ->
            Error.error
              "module-apply expects result, functor, and one or more argument \
               modules"
      in
      match parse_arguments [] argument_forms with
      | Error _ as err -> err
      | Ok argument_names ->
          compile_module_apply
            ?location:(Source_context.find name_form)
            ?functor_location:(Source_context.find functor_form)
            scope env next_type module_name functor_name argument_names)
  | FList (FSymbol "module-apply" :: _) ->
      Error.error
        "module-apply expects result, functor, and one or more argument modules"
  | FList
      [
        FSymbol (("def" | "defonce") as definition);
        (FSymbol _ as name_form);
        FString _docstring;
        expr_form;
      ] ->
      compile scope env next_type
        (FList [ FSymbol definition; name_form; expr_form ])
  | FList
      [
        FSymbol ("def" | "defonce");
        FSymbol "^:dynamic";
        (FSymbol name as name_form);
        expr_form;
      ] -> (
      let expected_ty = sidecar_function_signature scope env name in
      let expr_env = Env.with_expected_type expected_ty env in
      match compile_source_expr scope expr_env expr_form with
      | Error _ as error -> error
      | Ok expr ->
          let expr =
            match expected_ty with
            | None -> Ok expr
            | Some expected when Types.equal expected expr.ty ->
                Ok { expr with ty = expected }
            | Some expected ->
                Result.map
                  (fun semantic_expr -> typed_ir expected semantic_expr)
                  (Call_elaborator.plan_and_emit_argument env ~expected expr)
          in
          Result.bind expr (fun expr ->
          let ocaml_name = Names.ocaml_binding_name scope name in
          let env_key = Names.scoped_key scope name in
          Result.map
            (fun () ->
              let binding =
                Types.binding ~dynamically_bindable:true ocaml_name (TRef expr.ty)
              in
              ( scope,
                Env.add env_key binding env,
                next_type,
                Value_binding
                  {
                    pattern =
                      located_value_pattern name_form (Named ocaml_name);
                    expression =
                      Semantic_ir.Apply
                        ( Semantic_ir.Ident
                            "Lg_runtime.Runtime_reference.of_value",
                          [
                            (match expected_ty with
                            | Some _ ->
                                Semantic_ir.Constraint
                                  ( expr.semantic_expr,
                                    Types.ocaml_name expr.ty )
                            | None -> expr.semantic_expr);
                          ] );
                  } ))
            (check_emitted_name_collision env ~source_key:env_key ~ocaml_name))
          )
  | FList
      [ FSymbol ("def" | "defonce"); (FSymbol name as name_form); expr_form ]
    -> (
      let expr_form, protocol_alias_ty, protocol_alias_binding_ty =
        match expr_form with
        | FSymbol source_name -> (
            match Protocol.lookup_marker scope env source_name with
            | Some marker
              when Option.is_none (Protocol.binding_protocol_id marker) ->
                let arity_form parameter_tys =
                  let parameters =
                    List.mapi
                      (fun index _ ->
                        FSymbol
                          ("__lg_protocol_alias_arg_" ^ string_of_int index))
                      parameter_tys
                  in
                  FList
                    [ FVector parameters;
                      FList (FSymbol source_name :: parameters);
                    ]
                in
                let alias_ty =
                  Env.find_opt (Names.scoped_key scope source_name) env
                  |> Option.map (fun (binding : Types.binding) -> binding.ty)
                  |> Option.fold
                       ~none:
                         (sidecar_function_signature scope env source_name
                         |> Option.map
                              (Function_elaborator.infer_named_record scope env)
                         |> Option.value ~default:marker.ty)
                       ~some:Fun.id
                in
                let statically_dispatchable = function
                  | receiver_ty :: _ ->
                      Option.is_some
                        (Protocol.lookup_marker_impl env marker source_name
                           receiver_ty)
                  | [] -> false
                in
                let alias_binding_ty =
                  match alias_ty with
                  | TFn (parameter_tys, _)
                    when statically_dispatchable parameter_tys ->
                      alias_ty
                  | TOverloaded_fn arities
                    when List.for_all
                           (fun arity ->
                             statically_dispatchable arity.fixed_params)
                           arities ->
                      alias_ty
                  | _ -> marker.ty
                in
                (match marker.ty with
                | TFn (parameter_tys, _) ->
                    let arity = arity_form parameter_tys in
                    (match arity with
                    | FList [ parameters; body ] ->
                        ( FList [ FSymbol "fn"; parameters; body ],
                          Some alias_ty,
                          Some alias_binding_ty )
                    | _ -> assert false)
                | TOverloaded_fn arities ->
                    ( FList
                        (FSymbol "fn"
                        :: List.map
                             (fun arity -> arity_form arity.fixed_params)
                             arities),
                      Some alias_ty,
                      Some alias_binding_ty )
                | _ -> (expr_form, None, None))
            | Some _ | None -> (expr_form, None, None))
        | _ -> (expr_form, None, None)
      in
      let expected_ty =
        sidecar_function_signature scope env name
        |> Option.map (Function_elaborator.infer_named_record scope env)
        |> Option.fold ~none:protocol_alias_ty ~some:Option.some
      in
      let expr_env = Env.with_expected_type expected_ty env in
      let expr =
        Result.bind (compile_source_expr scope expr_env expr_form) (fun expr ->
            match expected_ty with
            | None -> Ok expr
            | Some _ when Option.is_some protocol_alias_binding_ty ->
                Ok { expr with ty = Option.get protocol_alias_binding_ty }
            | Some expected when Types.equal expected expr.ty ->
                Ok { expr with ty = expected }
            | Some expected
              when (not (Type_solver.is_open expected))
                   && not
                        (Call_elaborator.argument_compatible expected expr.ty) ->
                let related =
                  Source_context.find name_form
                  |> Option.to_list
                  |> List.map (fun location ->
                         ({
                            Error.location;
                            message =
                              Printf.sprintf
                                "The annotation on %s requires %s."
                                name (Types.source_name expected);
                          }
                           : Error.related))
                in
                Error.error ~title:"ANNOTATION TYPE MISMATCH"
                  ?location:(Source_context.find expr_form) ~related
                  ~type_mismatch:
                    (Error.type_mismatch ~context:Error.Annotation
                       ~expected:(Types.diagnostic_type_term expected)
                       ~actual:(Types.diagnostic_type_term expr.ty))
                  ~hints:
                    [
                      Printf.sprintf
                        "Change this expression to %s, or update the annotation on %s."
                        (Types.source_name expected) name;
                    ]
                  (Printf.sprintf
                     "The annotation on %s expects %s, but this expression produces %s."
                     name (Types.source_name expected) (Types.source_name expr.ty))
            | Some expected ->
                Result.map
                  (fun semantic_expr -> typed_ir expected semantic_expr)
                  (Call_elaborator.plan_and_emit_argument env ~expected expr))
      in
      match expr with
      | Error _ as err -> err
      | Ok expr when unresolved_contextual_type expr.ty ->
          Error.error "empty list requires a contextual element type"
      | Ok expr -> (
          let ocaml_name = Names.ocaml_binding_name scope name in
          let env_key = Names.scoped_key scope name in
          match
            check_emitted_name_collision env ~source_key:env_key ~ocaml_name
          with
          | Error _ as err -> err
          | Ok () -> (
              match expr.ty with
          | TRecord fields when not (Types.is_homogeneous_record fields) ->
                  let nested =
                    allocate_nested_anonymous_records ~owner:"" env next_type
                      fields
                  in
                  let fields = nested.nested_fields in
              let identity =
                Source_context.find_identity name_form
              in
              let allocation =
                    allocate_anonymous_record ~owner:"" nested.env
                      nested.next_type fields
              in
              let fields = allocation.record.fields in
              let record_ty = TNamed_record allocation.record in
              let binding = Types.binding ocaml_name record_ty in
              let env = Env.add env_key binding allocation.env in
              if allocation.fresh then
                let item =
                  match expr.record_values with
                  | Some values ->
                          let values =
                            List.map
                              (fun (field, value) ->
                                let field =
                                  find_field field.keyword fields
                                  |> Option.value ~default:field
                                in
                                (field, value))
                              values
                          in
                      Record_def
                            {
                              var_name = ocaml_name;
                          identity;
                          type_id = allocation.record.type_id;
                          type_name = allocation.record.type_name;
                          type_parameters = allocation.record.type_parameters;
                              set_module_name =
                                allocation.record.set_module_name;
                          fields;
                              values;
                            }
                  | None ->
                      Projected_record_def
                            {
                              var_name = ocaml_name;
                          identity;
                          type_id = allocation.record.type_id;
                          type_name = allocation.record.type_name;
                          type_parameters = allocation.record.type_parameters;
                              set_module_name =
                                allocation.record.set_module_name;
                          fields;
                              source = expr.semantic_expr;
                            }
                    in
                    let item =
                      match nested.items with
                      | [] -> item
                      | items -> Group (items @ [ item ])
                in
                Ok (scope, env, allocation.next_type, item)
              else
                    let expr =
                      Structural_map.as_named_record allocation.record expr
                    in
                    let item =
                    Value_binding
                        {
                          pattern =
                            located_value_pattern name_form (Named ocaml_name);
                          expression = expr.semantic_expr;
                        }
                    in
                    let item =
                      match nested.items with
                      | [] -> item
                      | items -> Group (items @ [ item ])
                    in
                    Ok (scope, env, allocation.next_type, item)
          | _ ->
              let env, next_type, record_items, expr =
                allocate_top_level_local_records env next_type expr
              in
              let binding =
                match protocol_alias_binding_ty with
                | Some binding_ty ->
                    Types.binding ocaml_name binding_ty
                    |> Types.generalize_binding
                | None -> (
                match expr_form with
                | FSymbol source_name -> (
                    match Resolver.lookup_binding scope env source_name with
                    | Ok source_binding ->
                        {
                          source_binding with
                          ocaml_name;
                          ty = expr.ty;
                          host_reference = None;
                          forward_declared = false;
                          dynamically_bindable = false;
                        }
                    | Error _ -> binding_of_expr ocaml_name expr)
                | _ -> binding_of_expr ocaml_name expr)
              in
              let env = Env.add env_key binding env in
              let env =
                match expr_form with
                | FSymbol source_name -> (
                    match Env.find_inline_macro ~scope source_name env with
                    | Some definition ->
                        Env.add_inline_macro ~scope ~name definition env
                    | None -> env)
                | _ -> env
              in
              let item =
                Value_binding
                  {
                    pattern =
                      located_value_pattern name_form (Named ocaml_name);
                    expression =
                      (match expected_ty with
                      | Some _ ->
                          Semantic_ir.Constraint
                            (expr.semantic_expr, Types.ocaml_name expr.ty)
                      | None -> expr.semantic_expr);
                  }
              in
              let item =
                match record_items with
                | [] -> item
                | items -> Group (items @ [ item ])
              in
              Ok (scope, env, next_type, item))))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: FList
           [ FSymbol "__type-hint"; FSymbol annotation; FSymbol name ]
      :: forms) ->
      compile scope env next_type
        (FList
           (FSymbol definition :: FSymbol name :: FSymbol annotation :: forms))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _ as name_form)
      :: FSymbol annotation
      :: FString _docstring
      :: (FMap _ as attributes)
      :: forms)
    when String.starts_with ~prefix:"^" annotation ->
      compile scope env next_type
        (FList
           (FSymbol definition :: name_form :: attributes :: FSymbol annotation
          :: forms))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol name as name_form)
      :: FMap attributes
      :: rest) ->
      let inline_definition =
        attributes
        |> List.find_map (function
             | FKeyword ":inline", FList (FSymbol "fn" :: forms) ->
                 Some
                   (Macro_definition.create ~namespace:scope ~name forms)
             | _ -> None)
      in
      let inherited_inline_macros = Env.inline_macros env in
      let runtime_env = Env.clear_inline_macros env in
      Result.bind
        (compile scope runtime_env next_type
           (FList (FSymbol definition :: name_form :: rest)))
        (fun (scope, env, next_type, item) ->
          let env = Env.with_inline_macros inherited_inline_macros env in
          match inline_definition with
          | None -> Ok (scope, env, next_type, item)
          | Some (Error _ as error) -> error
          | Some (Ok inline_definition) ->
              Ok
                ( scope,
                  Env.add_inline_macro ~scope ~name inline_definition env,
                  next_type,
                  item ))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _ as name_form)
      :: FList [ FSymbol "__type-hint"; FSymbol annotation; params ]
      :: body_forms) ->
      compile scope env next_type
        (FList
           (FSymbol definition :: name_form :: FSymbol annotation :: params
          :: body_forms))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _ as name_form)
      :: FSymbol annotation
      :: FString _docstring
      :: forms)
    when String.starts_with ~prefix:"^" annotation ->
      compile scope env next_type
        (FList
           (FSymbol definition :: name_form :: FSymbol annotation :: forms))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _ as name_form)
      :: FSymbol annotation
      :: (FList _ as first_clause)
      :: remaining_clauses)
    when String.starts_with ~prefix:"^" annotation ->
      if annotation = "^:dynamic" then
        Type_annotation.reject_dynamic_type ()
      else
        let annotate_clause = function
          | FList (params :: body_forms) ->
              let body =
                match body_forms with
                | [ body ] -> body
                | body_forms -> FList (FSymbol "do" :: body_forms)
              in
              FList
                [
                  params;
                  FList [ FSymbol "__type-hint"; FSymbol annotation; body ];
                ]
          | clause -> clause
        in
        compile scope env next_type
          (FList
             (FSymbol definition :: name_form
             :: List.map annotate_clause
                  (first_clause :: remaining_clauses)))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol name as name_form)
      :: FSymbol annotation
      :: params :: body_forms)
    when String.starts_with ~prefix:"^" annotation -> (
      if annotation = "^:dynamic" then
        Type_annotation.reject_dynamic_type ()
      else if not (function_is_recursive scope name body_forms) then
        let body =
          match body_forms with
          | [ body ] -> body
          | body_forms -> FList (FSymbol "do" :: body_forms)
        in
        compile scope env next_type
          (FList
             [
               FSymbol definition;
               name_form;
               params;
               FList [ FSymbol "__type-hint"; FSymbol annotation; body ];
             ])
      else
      match Type_annotation.of_param_annotation annotation with
      | Error _ as error -> error
      | Ok _ ->
          compile scope env next_type
            (FList
               (FSymbol definition :: name_form :: params
              :: FList
                   [ FSymbol "__return-type"; FSymbol annotation ]
              :: body_forms)))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _ as name_form)
      :: FString _docstring
      :: forms) ->
      compile scope env next_type
        (FList (FSymbol definition :: name_form :: forms))
  | FList
      (FSymbol ("defn" | "defn-")
      :: (FSymbol name as name_form)
      :: (FList _ as first_clause)
      :: remaining_clauses) -> (
      let ocaml_name = Names.ocaml_binding_name scope name in
      let env_key = Names.scoped_key scope name in
      let recursive =
        function_is_recursive scope name (first_clause :: remaining_clauses)
      in
      match
        check_emitted_name_collision env ~source_key:env_key ~ocaml_name
      with
      | Error _ as err -> err
      | Ok () -> (
          let signature =
            match
              sidecar_function_signature scope env name
              |> Option.map (Function_elaborator.infer_named_record scope env)
            with
            | Some (TOverloaded_fn arities) -> Some arities
            | Some _ | None -> None
          in
          match
            Expression_elaborator.prepare_multi_arity_fn ?signature ~ocaml_name
              scope env name
              (first_clause :: remaining_clauses)
          with
          | Error _ as err -> err
          | Ok prepared ->
              let env, next_type, local_type_items, prepared =
                allocate_multi_arity_local_records env next_type prepared
              in
              let targets, overload_row_param_types, row_items,
                  recursive_bindings =
                Expression_elaborator.lower_prepared_multi_arity prepared
              in
              let binding =
                Types.binding ~overload_targets:targets
                  ~overload_row_param_types ocaml_name
                  prepared.expr.ty
                |> Types.generalize_binding
              in
              let binding, value_item =
                if
                  requires_stable_forward_binding env env_key
                    prepared.expr.semantic_expr
                then
                  let value_type = deferred_value_type env prepared.expr in
                  ( { binding with ty = value_type },
                    Deferred_value_binding
                      {
                        name = ocaml_name;
                        value_type;
                        return_param_index = prepared.expr.return_param_index;
                        expression = prepared.expr.semantic_expr;
                      } )
                else
                  ( binding,
                    Value_binding
                      {
                        pattern =
                          located_value_pattern name_form (Named ocaml_name);
                        expression = prepared.expr.semantic_expr;
                      } )
              in
              let arity_items =
                if recursive then
                  [ Recursive_value_bindings recursive_bindings ]
                else
                  List.map
                    (fun ({ name; expression; _ } : Lowered.recursive_value) ->
                      Value_binding
                        { pattern = Named name; expression })
                    recursive_bindings
              in
              Ok
                ( scope,
                  Env.add env_key binding env,
                  next_type,
                  Group
                    (local_type_items @ row_items
                    @ arity_items @ [ value_item ]) )))
  | FList
      (FSymbol (("defn" | "defn-") as definition)
      :: (FSymbol _name as name_form)
      :: (FVector params as params_form)
      :: body_forms)
    when List.exists (function FSymbol "&" -> true | _ -> false) params ->
      compile scope env next_type
        (FList
           [ FSymbol definition; name_form; FList (params_form :: body_forms) ])
  | FList
      (FSymbol ("defn" | "defn-")
      :: (FSymbol name as name_form)
      :: params
      :: ((FKeyword _ | FList [ FSymbol "__return-type"; FSymbol _ ]) as
          return_annotation)
      :: body_forms) -> (
      let return_type =
        match return_annotation with
        | FKeyword keyword -> Type_annotation.of_keyword keyword
        | FList [ FSymbol "__return-type"; FSymbol annotation ] ->
            Type_annotation.of_param_annotation annotation
        | _ -> assert false
      in
      match return_type with
      | Error _ as err -> err
      | Ok return_ty -> (
          let return_ty =
            Function_elaborator.infer_named_record scope env return_ty
          in
          let ocaml_name = Names.ocaml_binding_name scope name in
          match
             prepare_inferred_recursive_fn_with_return ~ocaml_name scope env
               name return_ty params body_forms
           with
          | Error _ as err -> err
          | Ok parts -> (
              let param_tys =
                parts.param_bindings
                |> List.map (fun (_key, (binding : binding)) -> binding.ty)
              in
              let row_param_types = row_param_type_names ~env ocaml_name param_tys in
              let expr = fn_code
                       ~demote:
                         (Option.is_none
                            (sidecar_function_signature scope env name))
                       ~self_name:ocaml_name
                       ~row_param_type_names:row_param_types parts in
              let env_key = Names.scoped_key scope name in
              match
                 check_emitted_name_collision env ~source_key:env_key ~ocaml_name
               with
              | Error _ as err -> err
              | Ok () ->
                  let binding =
                    binding_of_expr ~row_param_types ocaml_name expr
                  in
                  let type_items = row_type_items row_param_types param_tys in
                  let binding, value_item =
                    if
                      requires_stable_forward_binding env env_key
                        expr.semantic_expr
                    then
                      let value_type = deferred_value_type env expr in
                      ( { binding with ty = value_type },
                        Deferred_value_binding
                          {
                            name = ocaml_name;
                            value_type;
                            return_param_index = expr.return_param_index;
                            expression = expr.semantic_expr;
                          } )
                    else
                      ( binding,
                        Recursive_value_binding
                          {
                            name = ocaml_name;
                            identity =
                              Source_context.find_identity name_form;
                            type_annotation = None;
                            expression = expr.semantic_expr;
                          } )
                  in
                  Ok
                    ( scope,
                      add_defined_function scope env_key binding params body_forms
                        env,
                      next_type,
                      Group (type_items @ [ value_item ]) ))))
  | FList
      (FSymbol ("defn" | "defn-")
      :: (FSymbol name as name_form)
      :: params :: body_forms)
    when function_is_recursive scope name body_forms -> (
      let ocaml_name = Names.ocaml_binding_name scope name in
      let env_key = Names.scoped_key scope name in
      let sidecar_signature =
        sidecar_function_signature scope env name
        |> Option.map (Function_elaborator.infer_named_record scope env)
      in
      let prepared =
        match sidecar_signature with
        | Some (TFn (parameter_tys, return_ty) as signature_ty) ->
            let signature_env =
              Env.add env_key
                (Types.binding ocaml_name signature_ty)
                env
            in
            let parameter_count =
              match Destructure.parse_param_specs params with
              | Ok specs -> List.length specs
              | Error _ -> -1
            in
            if List.length parameter_tys <> parameter_count then
              Error.error
                ("function signature arity does not match recursive defn "
               ^ name)
            else
              prepare_recursive_fn ~ocaml_name scope signature_env name
                return_ty params body_forms
        | Some _ -> Error.error ("function signature expected for " ^ name)
        | None ->
            prepare_inferred_recursive_fn ~ocaml_name scope env name params
              body_forms
      in
      match prepared with
      | Error _ as err -> err
      | Ok parts -> (
          let param_tys =
            parts.param_bindings
            |> List.map (fun (_key, (binding : binding)) -> binding.ty)
          in
          let row_param_types = row_param_type_names ~env ocaml_name param_tys in
          let expr =
            fn_code ~demote:(Option.is_none sidecar_signature)
              ~self_name:ocaml_name
              ~row_param_type_names:row_param_types parts
          in
          match
            check_emitted_name_collision env ~source_key:env_key ~ocaml_name
          with
          | Error _ as err -> err
          | Ok () ->
              let binding = binding_of_expr ~row_param_types ocaml_name expr in
              let type_items = row_type_items row_param_types param_tys in
              let binding, value_item =
                if
                  requires_stable_forward_binding env env_key
                    expr.semantic_expr
                then
                  let value_type = deferred_value_type env expr in
                  ( { binding with ty = value_type },
                    Deferred_value_binding
                      {
                        name = ocaml_name;
                        value_type;
                        return_param_index = expr.return_param_index;
                        expression = expr.semantic_expr;
                      } )
                else
                  let recursive_binding =
                    Recursive_value_binding
                      {
                        name = ocaml_name;
                        identity =
                          Source_context.find_identity name_form;
                        type_annotation =
                          recursive_type_annotation scope env name;
                        expression = expr.semantic_expr;
                      }
                  in
                  let redefable =
                    source_scope_redefable_roots scope
                    && not (contains_unresolved_type binding.ty)
                  in
                  if redefable then
                    match compatible_redefinition_root env env_key binding.ty with
                    | Some root_name ->
                        ( { binding with redef_root_name = Some root_name },
                          Value_binding
                            {
                              pattern = Ignore_pattern;
                              expression =
                                reset_runtime_root root_name expr.semantic_expr;
                            } )
                    | None ->
                        let root_name = redef_root_name ocaml_name in
                        ( redefable_binding binding,
                          Group
                            [
                              recursive_binding;
                              Value_binding
                                {
                                  pattern = Named root_name;
                                  expression =
                                    runtime_root_expression
                                      (Semantic_ir.Ident ocaml_name);
                                };
                              Value_binding
                                {
                                  pattern =
                                    located_value_pattern name_form
                                      (Named ocaml_name);
                                  expression =
                                    redefable_function_wrapper root_name binding.ty;
                                };
                            ] )
                  else (binding, recursive_binding)
              in
              Ok
                ( scope,
                  add_defined_function scope env_key binding params body_forms env,
                  next_type,
                  Group (type_items @ [ value_item ]) )))
  | FList
      (FSymbol ("defn" | "defn-")
      :: (FSymbol name as name_form)
      :: params :: body_forms) -> (
      match prepare_function scope env name params body_forms with
      | Error _ as err -> err
      | Ok parts when unresolved_contextual_type parts.body.ty ->
          Error.error "empty list requires a contextual element type"
      | Ok parts -> (
          let env, next_type, local_type_items, parts =
            allocate_function_local_records env next_type parts
          in
          let env, next_type, return_type_items, parts =
            allocate_function_return_record env next_type parts
          in
          let ocaml_name = Names.ocaml_binding_name scope name in
          let param_tys =
            parts.param_bindings
            |> List.map (fun (_key, (binding : binding)) -> binding.ty)
          in
          let row_param_types = row_param_type_names ~env ocaml_name param_tys in
          let expr =
            fn_code
              ~demote:
                (Option.is_none (sidecar_function_signature scope env name))
              ~self_name:ocaml_name
              ~row_param_type_names:row_param_types parts
          in
          let env_key = Names.scoped_key scope name in
          match
            check_emitted_name_collision env ~source_key:env_key ~ocaml_name
          with
          | Error _ as err -> err
          | Ok () -> (
              match expr.ty with
              | TFn _ ->
                  let published_ty =
                    if
                      Option.is_some
                        (sidecar_function_signature scope env name)
                      || preserves_required_seqable_protocol_result expr
                    then
                      expr.ty
                    else Protocol.refine_source_function_type env expr.ty
                  in
                  let binding =
                    binding_of_expr ~row_param_types ocaml_name
                      { expr with ty = published_ty }
                  in
                  let type_items =
                    return_type_items @ local_type_items
                    @ row_type_items row_param_types param_tys
                  in
                  let binding, value_item =
                    if
                      requires_stable_forward_binding env env_key
                        expr.semantic_expr
                    then
                      let value_type = deferred_value_type env expr in
                      ( { binding with ty = value_type },
                        Deferred_value_binding
                          {
                            name = ocaml_name;
                            value_type;
                            return_param_index = expr.return_param_index;
                            expression = expr.semantic_expr;
                          } )
                    else
                      let redefable =
                        source_scope_redefable_roots scope
                        && not (contains_unresolved_type published_ty)
                      in
                      if redefable then
                        match
                          compatible_redefinition_root env env_key published_ty
                        with
                        | Some root_name ->
                            ( { binding with redef_root_name = Some root_name },
                              Value_binding
                                {
                                  pattern = Ignore_pattern;
                                  expression =
                                    reset_runtime_root root_name
                                      expr.semantic_expr;
                                } )
                        | None ->
                            let root_name = redef_root_name ocaml_name in
                            ( redefable_binding binding,
                              Group
                                [
                                  Value_binding
                                    {
                                      pattern = Named root_name;
                                      expression =
                                        runtime_root_expression
                                          expr.semantic_expr;
                                    };
                                  Value_binding
                                    {
                                      pattern =
                                        located_value_pattern name_form
                                          (Named ocaml_name);
                                      expression =
                                        redefable_function_wrapper root_name
                                          published_ty;
                                    };
                                ] )
                      else
                        ( binding,
                          Value_binding
                            {
                              pattern =
                                located_value_pattern name_form
                                  (Named ocaml_name);
                              expression = expr.semantic_expr;
                            } )
                  in
                  Ok
                    ( scope,
                      add_defined_function scope env_key binding params body_forms
                        env,
                      next_type,
                      Group (type_items @ [ value_item ]) )
          | _ -> Error.error "defn body did not compile to a function")))
  | FList
      (FSymbol "defprotocol"
      :: (FSymbol protocol_name as name_form)
      :: method_forms) ->
      compile_defprotocol
        ?location:(Source_context.find name_form)
        scope env next_type protocol_name method_forms
  | FList
      (FSymbol ("extend-type" | "extend-type-no-register")
      :: receiver_form :: implementations) ->
      let rec groups grouped current = function
        | [] -> (
            match current with
            | None -> Ok (List.rev grouped)
            | Some (protocol_name, methods) ->
                Ok (List.rev ((protocol_name, List.rev methods) :: grouped)))
        | FSymbol protocol_name :: rest ->
            let grouped =
              match current with
              | None -> grouped
              | Some (previous, methods) ->
                  (previous, List.rev methods) :: grouped
            in
            groups grouped (Some (protocol_name, [])) rest
        | (FList _ as method_form) :: rest -> (
            match current with
            | None -> Error.error "extend-type requires a protocol name"
            | Some (protocol_name, methods) ->
                groups grouped
                  (Some (protocol_name, method_form :: methods))
                  rest)
        | _ :: _ -> Error.error "invalid extend-type implementation"
      in
      let items_of = function Group items -> items | item -> [ item ] in
      Result.bind (groups [] None implementations) (fun groups ->
          let groups = order_protocol_groups groups in
          Result.bind
            (predeclare_protocol_groups scope env receiver_form groups)
            (fun env ->
          let compile_registrations _env = Ok [] in
          let rec compile_groups env next_type items = function
            | [] ->
                Result.map
                  (fun registrations ->
                    (scope, env, next_type, Group (items @ registrations)))
                  (compile_registrations env)
            | (protocol_name, methods) :: rest -> (
                match
                  compile_extend_type scope env next_type receiver_form
                    protocol_name methods
                with
                | Error _ as error -> error
                | Ok (_, env, next_type, item) ->
                    compile_groups env next_type (items @ items_of item) rest)
          in
          compile_groups env next_type [] groups))
  | FList (FSymbol "extend-protocol" :: FSymbol protocol_name :: implementations)
    -> (
      let is_receiver = function
        | FSymbol _ | FKeyword _ -> true
        | _ -> false
      in
      let rec groups grouped current = function
        | [] -> (
            match current with
            | None -> Ok (List.rev grouped)
            | Some (receiver, methods) ->
                Ok (List.rev ((receiver, List.rev methods) :: grouped)))
        | receiver :: rest when is_receiver receiver ->
            let grouped =
              match current with
              | None -> grouped
              | Some (previous, methods) ->
                  (previous, List.rev methods) :: grouped
            in
            groups grouped (Some (receiver, [])) rest
        | (FList _ as method_form) :: rest -> (
            match current with
            | None ->
                Error.error "extend-protocol method requires a receiver type"
            | Some (receiver, methods) ->
                groups grouped (Some (receiver, method_form :: methods)) rest)
        | _ :: _ -> Error.error "invalid extend-protocol implementation"
      in
      let items_of = function Group items -> items | item -> [ item ] in
      match groups [] None implementations with
      | Error _ as error -> error
      | Ok groups ->
          let rec compile_groups env next_type items = function
            | [] -> Ok (scope, env, next_type, Group items)
            | (receiver, methods) :: rest -> (
                match
                  compile scope env next_type
                    (FList
                       (FSymbol "extend-type" :: receiver
                      :: FSymbol protocol_name :: methods))
                with
                | Error _ as error -> error
                | Ok (_, env, next_type, item) ->
                    compile_groups env next_type (items @ items_of item) rest)
          in
          compile_groups env next_type [] groups)
  | FList
      (FSymbol "module"
      :: (FSymbol module_name as name_form)
      :: (FSymbol signature_name as signature_form)
      :: forms) -> (
      match
        compile_module
          ?location:(Source_context.find name_form)
          ~signature_name
          ?signature_location:(Source_context.find signature_form)
          scope env next_type module_name module_name forms
      with
      | Error _ as err -> err
      | Ok (scope, module_env, module_bindings, next_type, item) ->
          let env =
            env
            |> Env.with_protocols (Env.protocols module_env)
            |> Env.with_modules (Env.modules module_env)
            |> Env.with_types (Env.types module_env)
            |> Env.inherit_private_exports module_env
            |> Env.add_bindings module_bindings
          in
          Ok (scope, env, next_type, item))
  | FList (FSymbol "module" :: (FSymbol module_name as name_form) :: forms) -> (
      match
        compile_module
          ?location:(Source_context.find name_form)
          scope env next_type module_name module_name forms
      with
      | Error _ as err -> err
      | Ok (scope, module_env, module_bindings, next_type, item) ->
          let env =
            env
            |> Env.with_protocols (Env.protocols module_env)
            |> Env.with_modules (Env.modules module_env)
            |> Env.with_types (Env.types module_env)
            |> Env.inherit_private_exports module_env
            |> Env.add_bindings module_bindings
          in
          Ok (scope, env, next_type, item))
  | FList [ FSymbol "namespace-scope"; FSymbol namespace_name ] ->
      let env = Require.add_source_core_bindings env namespace_name in
      let env =
        Env.add (Names.scoped_key namespace_name "read-string")
          Core_edn.read_string_binding env
      in
      Ok
        (namespace_name, env, next_type, Comment ("namespace " ^ namespace_name))
  | FList (FSymbol "refer-clojure-exclude" :: names) ->
      let rec parse_names acc = function
        | [] -> Ok (List.rev acc)
        | FSymbol name :: rest -> parse_names (name :: acc) rest
        | _ -> Error.error ":refer-clojure :exclude expects a vector of symbols"
      in
      Result.map
        (fun names ->
          let env = Env.add_core_exclusions ~scope names env in
          let env =
            List.fold_left
              (fun env name -> Require.remove_source_core_binding env scope name)
              env names
          in
          (scope, env, next_type, Comment "refer-clojure exclude"))
        (parse_names [] names)
  | FList (FSymbol "defmacro" :: FSymbol name :: forms) ->
      Result.map
        (fun definition ->
          let env = Env.add_macro ~scope ~name definition env in
          (scope, env, next_type, Comment ("macro " ^ name)))
        (Macro_definition.create ~namespace:scope ~name forms)
  | FList (FSymbol "macro-helper-defn" :: FSymbol name :: forms) ->
      Result.map
        (fun definition ->
          let env = Env.add_macro_function ~scope ~name definition env in
          (scope, env, next_type, Comment ("macro helper " ^ name)))
        (Macro_definition.create ~namespace:scope ~name forms)
  | FList (FSymbol "macro-helper-def" :: FSymbol name :: forms) ->
      let value =
        match forms with [] -> FSymbol "nil" | value :: _ -> value
      in
      let env = Env.add_macro_value ~scope ~name value env in
      Ok (scope, env, next_type, Comment ("macro value " ^ name))
  | FList [ FSymbol ("def" as kind); FSymbol name ] ->
      compile scope env next_type
        (FList [ FSymbol kind; FSymbol name; FSymbol "nil" ])
  | FList (FSymbol "declare" :: names) ->
      let rec add_declarations env = function
        | [] -> Ok env
        | FSymbol name :: rest ->
            let key = Names.scoped_key scope name in
            let ocaml_name = Names.ocaml_binding_name scope name in
            let binding =
              match Env.find_opt key env with
              | Some binding
                when String.equal binding.ocaml_name ocaml_name
                     && not (Types.equal binding.ty (TOcaml "__declared_fn")) ->
                  binding
              | _ -> (
                  match sidecar_function_signature scope env name with
                  | Some ty ->
                      Types.binding ~forward_declared:true ocaml_name
                        (Function_elaborator.infer_named_record scope env ty)
                  | None ->
                      Types.binding ocaml_name (TOcaml "__declared_fn"))
            in
            let env = Env.add key binding env in
            add_declarations (Env.add_explicit_declaration key env) rest
        | _ -> Error.error "declare expects symbols"
      in
      Result.map
        (fun env -> (scope, env, next_type, Comment "declare"))
        (add_declarations env names)
  | FList (FSymbol "require" :: entries) -> (
      match Require.parse_entries entries with
      | Error _ as err -> err
      | Ok specs -> (
          let rec apply_specs env = function
            | [] -> Ok env
            | Require.Package _ :: rest -> apply_specs env rest
            | Require.Load { module_name } :: rest -> (
                let result =
                  if Require.core_namespace module_name then
                    Ok
                      (Require.add_core_alias_bindings env module_name
                         module_name)
                  else if String.starts_with ~prefix:"ocaml." module_name then
                    Ok
                      (Require.add_ocaml_alias_bindings env module_name
                         module_name)
                  else Require.ensure_namespace env module_name
                in
                match result with
                | Error _ as err -> err
                | Ok env -> apply_specs env rest)
            | Require.Alias { module_name; alias } :: rest -> (
                if String.starts_with ~prefix:"ocaml." module_name then
                  let env =
                    Require.add_ocaml_alias_bindings env module_name alias
                  in
                  apply_specs
                    (Env.add_namespace_alias ~scope ~alias ~target:module_name
                       env)
                    rest
                else if Require.core_namespace module_name then
                  let env =
                    Require.add_core_alias_bindings env module_name alias
                  in
                  apply_specs
                    (Env.add_namespace_alias ~scope ~alias ~target:module_name
                       env)
                    rest
                else
                  match Require.add_lg_alias_bindings env module_name alias with
                  | Error _ as err -> err
                  | Ok env ->
                      let env =
                        Env.add_namespace_alias ~scope ~alias
                          ~target:module_name env
                      in
                      apply_specs env rest)
            | Require.Refer { module_name; names } :: rest -> (
                let result =
                  if String.starts_with ~prefix:"ocaml." module_name then
                    Require.add_ocaml_refer_bindings env scope module_name names
                  else Require.add_lg_refer_bindings env scope module_name names
                in
                match result with
                | Error _ as err -> err
                | Ok env -> apply_specs env rest)
          in
          match apply_specs env specs with
          | Error _ as err -> err
          | Ok env -> Ok (scope, env, next_type, Comment "require")))
  | FList (FSymbol "loop" :: _) as form -> (
      match compile_expr scope env form with
      | Error _ as err -> err
      | Ok expr ->
          Ok
            ( scope,
              env,
              next_type,
              Value_binding
                { pattern = Ignore_pattern; expression = expr.semantic_expr } ))
  | FList (FSymbol "recur" :: _) ->
      Error.error "recur is only valid in a loop tail position"
  | FList
      [
        FSymbol operation;
        FSymbol array_name;
        _index;
        value;
      ] as form
    when operation = "aset" || operation = "__lg_aset"
         || operation = "unsafe-aset"
         || String.ends_with ~suffix:"/aset" operation
         || String.ends_with ~suffix:"/unsafe-aset" operation -> (
      match (compile_expr scope env value, compile_expr scope env form) with
      | (Error _ as error), _ | _, (Error _ as error) -> error
      | Ok value, Ok expr ->
          let key = Names.scoped_key scope array_name in
          let env =
            match Env.find_opt key env with
            | Some binding ->
                let element_ty =
                  match binding.ty with
                  | TArray
                      (TNullable (TUnknown | TMeta _ | TVar _)
                      | TOcaml_app
                          ("option", [ TUnknown | TMeta _ | TVar _ ])) ->
                      Some (TNullable value.ty)
                  | TArray (TUnknown | TMeta _ | TVar _) -> Some value.ty
                  | _ -> None
                in
                Option.fold ~none:env
                  ~some:(fun element_ty ->
                    Env.add key
                      { binding with ty = TArray element_ty; scheme = None }
                      env)
                  element_ty
            | None -> env
          in
          Ok
            ( scope,
              env,
              next_type,
              Value_binding
                {
                  pattern = Ignore_pattern;
                  expression = expr.semantic_expr;
                } ))
  | FList (FSymbol ("defn" | "defn-") :: _) ->
      Error.error "defn expects a name, parameter vector, and body"
  | FList (FSymbol "defonce" :: _) ->
      Error.error "defonce expects a name and value"
  | FList (FSymbol name :: args) as form -> (
      match Env.find_macro ~scope name env with
      | None -> (
          match compile_expr scope env form with
          | Error _ as error -> error
          | Ok expr -> (
              match expr.record_values with
              | Some _ ->
                  Error.error "top-level map literals must be bound with def"
              | None ->
                  Ok
                    ( scope,
                      env,
                      next_type,
                      Value_binding
                        {
                          pattern = Ignore_pattern;
                          expression = expr.semantic_expr;
                        } )))
      | Some definition -> (
          match
            Macro_expander.expand ~call_site:form ~scope ~compiler_env:env
              definition args
          with
          | Error _ as error -> error
          | Ok expanded -> compile scope env next_type expanded))
  | form -> (
      match compile_expr scope env form with
      | Error _ as err -> err
      | Ok expr -> (
          match expr.record_values with
          | Some _ ->
              Error.error "top-level map literals must be bound with def"
          | None ->
              Ok
                ( scope,
                  env,
                  next_type,
                  Value_binding
                    {
                      pattern = Ignore_pattern;
                      expression = expr.semantic_expr;
                    } )))
