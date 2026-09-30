open Ast
open Types
open Lowered

module Env = Compiler_environment

let compile_expr = Expression_elaborator.compile_expr

let applied_function_name expression =
  match Semantic_ir.unlocated expression with
  | Semantic_ir.Apply (callee, _) -> (
      match Semantic_ir.unlocated callee with
      | Semantic_ir.Ident name -> Some name
      | _ -> None)
  | _ -> None

let applied_function_return_type env expression =
  match Semantic_ir.unlocated expression with
  | Semantic_ir.Apply (callee, arguments) -> (
      match Semantic_ir.unlocated callee with
      | Semantic_ir.Ident name ->
          Env.bindings_emitted_as name env
          |> List.find_map (fun (_, (binding : Types.binding)) ->
                 match binding.ty with
                 | TFn (parameters, return_ty)
                   when List.length parameters = List.length arguments ->
                     Some return_ty
                 | TOverloaded_fn arities ->
                     arities
                     |> List.find_map (fun (arity : Types.fn_arity) ->
                            if
                              List.length arity.fixed_params
                              = List.length arguments
                              && Option.is_none arity.rest_param
                            then Some arity.return_ty
                            else None)
                 | _ -> None)
      | _ -> None)
  | _ -> None
let prepare_fn = Expression_elaborator.prepare_fn
let prepare_inferred_recursive_fn = Expression_elaborator.prepare_inferred_recursive_fn
let prepare_inferred_recursive_fn_with_return =
  Expression_elaborator.prepare_inferred_recursive_fn_with_return
let fn_code = Expression_elaborator.fn_code
let binding_of_expr = Expression_support.binding_of_expr
let allocate_anonymous_record = Expression_support.allocate_anonymous_record
let row_param_type_names = Expression_support.row_param_type_names
let row_type_items = Expression_support.row_type_items
let check_emitted_name_collision = Resolver.check_emitted_name_collision
let inherit_scope_ocaml_value_refers =
  Expression_support.inherit_scope_ocaml_value_refers
let compile_defprotocol = Protocol_elaborator.compile_defprotocol
let compile_extend_type = Protocol_elaborator.compile_extend_type

let module_id_of_path module_path =
  match String.rindex_opt module_path '.' with
  | None -> Module_id.create ~owner:[] ~name:module_path
  | Some separator ->
      let owner = String.sub module_path 0 separator in
      let name =
        String.sub module_path (separator + 1)
          (String.length module_path - separator - 1)
      in
      Module_id.create ~owner:[ owner ] ~name

let module_binding_key = Module_environment.binding_key
let module_binding_ocaml_name = Module_environment.binding_ocaml_name
let changed_bindings = Module_environment.changed_bindings
let open_module_bindings = Module_environment.open_bindings
let include_module_public_bindings = Module_environment.include_public_bindings
let alias_module_bindings = Module_environment.alias_bindings

let resolve_module_target_path scope env target_name =
  if scope = "" || String.contains target_name '.' then target_name
  else
    let local_id = Module_id.create ~owner:[ scope ] ~name:target_name in
    if Module_registry.mem_module local_id (Env.modules env) then
      scope ^ "." ^ target_name
    else target_name

let compile_module_alias ?semantic_target ?location ?target_location scope env
    next_type alias_name target_name =
  let target_path =
    Option.value semantic_target
      ~default:(resolve_module_target_path scope env target_name)
  in
  let alias_bindings = alias_module_bindings env alias_name target_path in
  let owner = if scope = "" then [] else [ scope ] in
  let alias_id = Module_id.create ~owner ~name:alias_name in
  let target_id = Module_id.of_string target_path in
  match Module_registry.declare_alias alias_id target_id (Env.modules env) with
  | Error _ as err -> err
  | Ok modules ->
      Ok
        ( scope,
          env |> Env.with_modules modules |> Env.add_bindings alias_bindings
          |> Env.remap_private_exports ~from_module:(Names.module_path_to_ocaml target_path)
               ~to_module:(Names.module_path_to_ocaml alias_name),
          next_type,
          Module_alias
            {
              alias_name = Names.module_segment_to_ocaml alias_name;
              location;
              target_name = Names.module_path_to_ocaml target_name;
              target_location;
            } )

let parse_type_parameters = Type_parameters.parse

let compile_module_signature ?location scope env next_type signature_name item_forms =
  Module_signature_elaborator.compile ?location scope env next_type signature_name
    item_forms

let compile_type_alias = Type_definition_elaborator.compile_type_alias
let compile_type_record = Type_definition_elaborator.compile_type_record
let record_type_public_binding =
  Type_definition_elaborator.record_type_public_binding
let compile_type_variant = Type_definition_elaborator.compile_type_variant

let variant_public_bindings module_path previous updated =
  let module_name = Names.module_path_to_ocaml module_path in
  changed_bindings previous updated
  |> List.map (fun (key, (binding : binding)) ->
         let constructor_name =
           match String.rindex_opt key '/' with
           | None -> key
           | Some index ->
               String.sub key (index + 1) (String.length key - index - 1)
         in
         ( key,
           { binding with
             ocaml_name = module_name ^ "." ^ constructor_name;
             ty = Types.qualify_module_type module_name binding.ty;
           } ))

let compile_module_apply ?location ?functor_location scope env next_type module_name
    functor_name arguments =
  let argument_names = List.map (fun (argument : Lowered.module_reference) -> argument.module_name) arguments in
  let applied_bindings =
    Module_metadata.apply_functor_result_bindings env module_name functor_name argument_names
  in
  let module_id =
    Module_id.create ~owner:(if scope = "" then [] else [ scope ])
      ~name:module_name
  in
  match
    Module_registry.declare_module module_id Applied (Env.modules env)
  with
  | Error _ as err -> err
  | Ok modules ->
      (match
         Module_registry.apply_functor_modules ~module_name ~functor_name modules
       with
      | Error _ as err -> err
      | Ok modules ->
          (match
             Module_registry.apply_functor_aliases ~module_name ~functor_name modules
           with
          | Error _ as err -> err
          | Ok modules -> (
              match Module_metadata.apply_functor_types env module_name functor_name argument_names with
              | Error _ as err -> err
              | Ok types ->
              let protocols =
                Module_metadata.apply_functor_protocols env module_name functor_name
              in
              Ok
                ( scope,
                  env |> Env.with_modules modules |> Env.with_protocols protocols
                  |> Env.with_types types |> Env.add_bindings applied_bindings
                  |> Env.remap_private_exports ~from_module:(Names.module_path_to_ocaml functor_name)
                       ~to_module:(Names.module_path_to_ocaml module_name),
                  next_type,
                  Module_apply
                    {
                      module_name = Names.module_segment_to_ocaml module_name;
                      location;
                      functor_name = Names.module_path_to_ocaml functor_name;
                      functor_location;
                      arguments =
                        List.map
                          (fun argument ->
                            { argument with
                              module_name =
                                Names.module_path_to_ocaml argument.module_name })
                          arguments;
                    } ))))

let rec compile_module ?location ?signature_name ?signature_location
    ?(register_module = true) scope env next_type module_path module_segment forms =
  let env = inherit_scope_ocaml_value_refers scope module_path env in
  let env = Require.add_source_core_bindings env module_path in
  let export_function definition public_bindings binding =
    if definition = "defn-" then public_bindings
    else public_bindings @ [ binding ]
  in
  let rec compile_module_form env public_bindings next_type items = function
    | FList
        (FSymbol "module-signature" :: ((FSymbol signature_name) as name_form)
        :: item_forms) -> (
        match
          compile_module_signature ?location:(Source_context.find name_form)
            module_path env next_type signature_name item_forms
        with
        | Error _ as err -> err
        | Ok (_scope, env, next_type, item) ->
            Ok (env, public_bindings, next_type, item :: items))
    | FList (FSymbol "module-signature" :: _) ->
        Error.error ~code:Error_code.Arity "module-signature expects a name and signature items"
    | FList [ FSymbol "extern-type"; ((FSymbol name) as name_form) ] -> (
        match Type_definition_elaborator.compile_opaque_type
          ?location:(Source_context.find name_form) module_path env next_type name with
        | Error _ as error -> error
        | Ok (_, env, next_type, item) ->
            Ok (env, public_bindings, next_type, item :: items))
    | FList (FSymbol "extern-type" :: _) ->
        Error.error ~code:Error_code.Arity "extern-type expects one type name"
    | FList
        [ FSymbol "type-alias";
          ((FSymbol name) as name_form);
          FVector parameter_forms;
          manifest_form ] -> (
        match parse_type_parameters (FVector parameter_forms) with
        | Error _ as err -> err
        | Ok type_parameters -> (
            match
              compile_type_alias ?location:(Source_context.find name_form)
                module_path env next_type name type_parameters manifest_form
            with
            | Error _ as err -> err
            | Ok (_scope, env, next_type, item) ->
                Ok (env, public_bindings, next_type, item :: items)))
    | FList
        [ FSymbol "type-alias"; ((FSymbol name) as name_form); manifest_form ] -> (
        match
          compile_type_alias ?location:(Source_context.find name_form) module_path
            env next_type name [] manifest_form
        with
        | Error _ as err -> err
        | Ok (_scope, env, next_type, item) ->
            Ok (env, public_bindings, next_type, item :: items))
    | FList
        (FSymbol "type-record" :: ((FSymbol name) as name_form)
        :: FVector parameter_forms
        :: field_forms) -> (
        match parse_type_parameters (FVector parameter_forms) with
        | Error _ as err -> err
        | Ok type_parameters -> (
            match
              compile_type_record ?location:(Source_context.find name_form)
                module_path env next_type name type_parameters field_forms
            with
            | Error _ as err -> err
            | Ok (_scope, env, next_type, item) -> (
                match record_type_public_binding module_path name env with
                | Error _ as err -> err
                | Ok public_binding ->
                    Ok
                      ( env,
                        public_bindings @ [ public_binding ],
                        next_type,
                        item :: items ))))
    | FList
        (FSymbol "type-record" :: ((FSymbol name) as name_form)
        :: field_forms) -> (
        match
          compile_type_record ?location:(Source_context.find name_form) module_path
            env next_type name [] field_forms
        with
        | Error _ as err -> err
        | Ok (_scope, env, next_type, item) -> (
            match record_type_public_binding module_path name env with
            | Error _ as err -> err
            | Ok public_binding ->
                Ok
                  ( env,
                    public_bindings @ [ public_binding ],
                    next_type,
                    item :: items )))
    | FList (FSymbol "type-record" :: _) ->
        Error.error ~code:Error_code.Arity "type-record expects a name and fields"
    | FList
        (FSymbol "type-variant" :: ((FSymbol name) as name_form)
        :: FVector parameter_forms
        :: constructor_forms) -> (
        match parse_type_parameters (FVector parameter_forms) with
        | Error _ as err -> err
        | Ok type_parameters -> (
            match
              compile_type_variant ?location:(Source_context.find name_form)
                module_path env next_type name type_parameters constructor_forms
            with
            | Error _ as err -> err
            | Ok (_scope, updated_env, next_type, item) ->
                let exported = variant_public_bindings module_path env updated_env in
                Ok
                  ( updated_env,
                    public_bindings @ exported,
                    next_type,
                    item :: items )))
    | FList
        (FSymbol "type-variant" :: ((FSymbol name) as name_form)
        :: constructor_forms) -> (
        match
          compile_type_variant ?location:(Source_context.find name_form) module_path
            env next_type name [] constructor_forms
        with
        | Error _ as err -> err
        | Ok (_scope, updated_env, next_type, item) ->
            let exported = variant_public_bindings module_path env updated_env in
            Ok
              ( updated_env,
                public_bindings @ exported,
                next_type,
                item :: items ))
    | FList [ FSymbol "open"; ((FSymbol opened_module) as module_form) ] ->
        let env = open_module_bindings module_path env opened_module in
        Ok
          ( env,
            public_bindings,
            next_type,
            Open_module
              { module_name = Names.module_path_to_ocaml opened_module;
                location = Source_context.find module_form }
            :: items )
    | FList [ FSymbol "include"; ((FSymbol included_module) as module_form) ] ->
        let included_public_bindings =
          include_module_public_bindings module_path env included_module
        in
        let env = open_module_bindings module_path env included_module in
        Ok
          ( env,
            public_bindings @ included_public_bindings,
            next_type,
            Include_module
              { module_name = Names.module_path_to_ocaml included_module;
                location = Source_context.find module_form }
            :: items )
    | FList (FSymbol "include" :: _) ->
        Error.error ~code:Error_code.Arity "include expects one module"
    | FList
        [ FSymbol "module-alias";
          ((FSymbol alias_name) as alias_form);
          ((FSymbol target_name) as target_form) ] ->
        let target_path = resolve_module_target_path module_path env target_name in
        let public_alias_path = module_path ^ "." ^ alias_name in
        let public_alias_bindings =
          alias_module_bindings env public_alias_path target_path
        in
        (match
           compile_module_alias ~semantic_target:target_path
             ?location:(Source_context.find alias_form)
             ?target_location:(Source_context.find target_form) module_path env next_type
             alias_name target_name
         with
        | Error _ as err -> err
        | Ok (_scope, env, next_type, item) ->
            Ok
              ( env,
                public_bindings @ public_alias_bindings,
                next_type,
                item :: items ))
    | FList (FSymbol "module-alias" :: _) ->
        Error.error ~code:Error_code.Protocol "module-alias expects alias and target modules"
    | FList
        (FSymbol "defprotocol" :: ((FSymbol protocol_name) as name_form)
        :: method_forms) -> (
        match
          compile_defprotocol ?location:(Source_context.find name_form) module_path env
            next_type protocol_name method_forms
        with
        | Error _ as err -> err
        | Ok (_scope, updated_env, next_type, item) ->
            let exported = changed_bindings env updated_env in
            Ok
              ( updated_env,
                public_bindings @ exported,
                next_type,
                item :: items ))
    | FList
        (FSymbol "extend-type" :: receiver_form :: FSymbol protocol_name
        :: method_forms) -> (
        match
          compile_extend_type module_path env next_type receiver_form protocol_name
            method_forms
        with
        | Error _ as err -> err
        | Ok (_scope, updated_env, next_type, item) ->
            let exported =
              changed_bindings env updated_env
              |> List.map (fun (key, (binding : binding)) ->
                     let qualified_ty =
                       Types.qualify_module_type
                         (Names.module_path_to_ocaml module_path)
                         binding.ty
                     in
                     let key =
                       match (String.rindex_opt key '/', qualified_ty) with
                       | Some separator, TFn (TNamed_record record :: _, _) ->
                           String.sub key 0 (separator + 1) ^ record.type_name
                       | _ -> key
                     in
                     ( key,
                       {
                         binding with
                         ocaml_name =
                           Names.module_path_to_ocaml module_path ^ "."
                           ^ binding.ocaml_name;
                         ty = qualified_ty;
                       } ))
            in
            Ok
              ( updated_env,
                public_bindings @ exported,
                next_type,
                item :: items ))
    | FList [ FSymbol "ffi"; (FSymbol name as name_form);
              FVector parameters; result; options ] ->
        let local_name = Names.sanitize_name name in
        Result.map
          (fun (foreign : Foreign_binding.t) ->
            let key = module_binding_key module_path name in
            let local_binding = Types.binding local_name foreign.value_type in
            let public_binding = Types.binding
                (Names.module_path_to_ocaml module_path ^ "." ^ local_name)
                (Types.qualify_module_type
                   (Names.module_path_to_ocaml module_path) foreign.value_type) in
            Env.add key local_binding env,
            public_bindings @ [key, public_binding], next_type,
            Foreign_binding foreign :: items)
          (Foreign_binding.parse ~target:(Env.target env)
             ~is_opaque:(function
               | TOcaml name -> (match Resolver.lookup_type_declaration module_path env name with
                   | Some { kind = Opaque; _ } -> true | _ -> false)
               | _ -> false)
             ~resolve_type:(Function_elaborator.infer_named_record module_path env)
             ~name:local_name ~location:(Source_context.find name_form)
             parameters result options)
    | FList (FSymbol "ffi" :: _) ->
        Error.error ~code:Error_code.Interop "ffi expects a name, argument type vector, result type, and options map"
    | FList
        [ FSymbol ("def" | "defonce"); ((FSymbol name) as name_form); expr_form ] -> (
        match compile_expr module_path env expr_form with
        | Error _ as err -> err
        | Ok expr ->
            let local_name = Names.sanitize_name name in
            let key = module_binding_key module_path name in
            let local_binding = binding_of_expr local_name expr in
            let public_binding =
              Types.binding
                ?return_param_index:(expr.return_param_index)
                (module_binding_ocaml_name module_path name)
                (Types.qualify_module_type
                   (Names.module_path_to_ocaml module_path)
                   expr.ty)
            in
            (match check_emitted_name_collision env ~source_key:key ~ocaml_name:local_name with
            | Error _ as err -> err
            | Ok () -> (match expr.ty with
            | TRecord fields
            | TNamed_record { nominal = false; fields; _ }
              when (match Semantic_ir.unlocated expr.semantic_expr with
                   | _ when (match expr.ty with TRecord _ -> true | _ -> false) ->
                       true
                   | _ -> (
                       match applied_function_name expr.semantic_expr with
                       | Some function_name ->
                           not
                             (String.starts_with ~prefix:"Lg_runtime."
                                function_name)
                       | None -> false)
                  ) ->
                let module_name = Names.module_path_to_ocaml module_path in
                let allocation =
                  allocate_anonymous_record ~owner:module_path env next_type fields
                in
                let local_record_ty = TNamed_record allocation.record in
                let public_record_ty =
                  Types.qualify_module_type module_name local_record_ty
                in
                let local_binding = Types.binding local_name local_record_ty in
                let public_binding =
                  Types.binding (module_binding_ocaml_name module_path name)
                    public_record_ty
                in
                let env = Env.add key local_binding allocation.env in
                let local_expr =
                  match expr.record_values with
                  | Some _ ->
                      Structural_map.as_named_record allocation.record expr
                  | None ->
                      let source_name = "__lg_record_source_" ^ local_name in
                      let source_ty =
                        applied_function_return_type env expr.semantic_expr
                        |> Option.value ~default:expr.ty
                      in
                      let source =
                        {
                          expr with
                          ty = source_ty;
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
                                  expr.semantic_expr );
                              ],
                              projected.semantic_expr );
                        record_values = None;
                      }
                in
                let value_item =
                  Value_binding
                    { pattern = Named local_name;
                      expression = local_expr.semantic_expr }
                in
                let item =
                  if allocation.fresh then
                    Group
                      [
                        Type_def
                          {
                            type_id = allocation.record.type_id;
                            type_name = allocation.record.type_name;
                            type_parameters = allocation.record.type_parameters;
                            fields = allocation.record.fields;
                            nominal = false;
                            location = Source_context.find name_form;
                          };
                        value_item;
                      ]
                  else value_item
                in
                Ok
                  ( env,
                    public_bindings @ [ (key, public_binding) ],
                    allocation.next_type,
                    item :: items )
            | _ ->
                let item =
                  Value_binding
                    { pattern = Named local_name; expression = expr.semantic_expr }
                in
                Ok
                  ( Env.add key local_binding env,
                    public_bindings @ [ (key, public_binding) ],
                    next_type,
                    item :: items ))))
    | FList
        (FSymbol (("defn" | "defn-") as definition)
        :: ((FSymbol name) as _name_form)
        :: ((FList _) as first_clause) :: remaining_clauses) ->
        let local_name = Names.sanitize_name name in
        let public_name = module_binding_ocaml_name module_path name in
        let key = module_binding_key module_path name in
        (match
           check_emitted_name_collision env ~source_key:key ~ocaml_name:local_name
         with
        | Error _ as err -> err
        | Ok () -> (
            match
              Expression_elaborator.prepare_multi_arity_fn ~ocaml_name:local_name
                module_path env name (first_clause :: remaining_clauses)
            with
            | Error _ as err -> err
            | Ok prepared ->
                let local_targets, overload_row_param_types, row_items,
                    recursive_bindings =
                  Expression_elaborator.lower_prepared_multi_arity prepared
                in
                let module_name = Names.module_path_to_ocaml module_path in
                let public_targets =
                  List.map (fun target -> module_name ^ "." ^ target) local_targets
                in
                let local_binding =
                  Types.binding ~overload_targets:local_targets
                    ~overload_row_param_types local_name
                    prepared.expr.ty
                in
                let public_binding =
                  Types.binding ~overload_targets:public_targets public_name
                    (Types.qualify_module_type module_name prepared.expr.ty)
                in
                let value_item =
                  Value_binding
                    { pattern = Named local_name;
                      expression = prepared.expr.semantic_expr }
                in
                Ok
                  ( Env.add key local_binding env,
                    export_function definition public_bindings
                      (key, public_binding),
                    next_type,
                    Group
                      (row_items
                      @ [ Recursive_value_bindings recursive_bindings; value_item ])
                    :: items )))
    | FList
        (FSymbol (("defn" | "defn-") as definition)
        :: ((FSymbol _name) as name_form)
        :: ((FVector params) as params_form) :: body_forms)
      when List.exists (function FSymbol "&" -> true | _ -> false) params ->
        compile_module_form env public_bindings next_type items
          (FList
             [ FSymbol definition;
               name_form;
               FList (params_form :: body_forms) ])
    | FList
        (FSymbol (("defn" | "defn-") as definition)
        :: ((FSymbol name) as name_form) :: params
        :: FKeyword return_keyword
        :: body_forms) -> (
        match Type_annotation.of_keyword return_keyword with
        | Error _ as err -> err
        | Ok return_ty ->
            let local_name = Names.sanitize_name name in
            (match
               prepare_inferred_recursive_fn_with_return ~ocaml_name:local_name module_path env name
                 (Function_elaborator.infer_named_record module_path env return_ty)
                 params body_forms
             with
            | Error _ as err -> err
            | Ok parts ->
                let public_name = module_binding_ocaml_name module_path name in
                let param_tys =
                  parts.param_bindings
                  |> List.map (fun (_key, (binding : binding)) -> binding.ty)
                in
                let local_row_types =
                  row_param_type_names ~env local_name param_tys
                in
                let public_row_types =
                  row_param_type_names ~env public_name param_tys
                in
                let expr = fn_code ~row_param_type_names:local_row_types parts in
                let key = module_binding_key module_path name in
                (match
                   check_emitted_name_collision env ~source_key:key
                     ~ocaml_name:local_name
                 with
                | Error _ as err -> err
                | Ok () ->
                    let local_binding =
                      binding_of_expr ~row_param_types:local_row_types local_name
                        expr
                    in
                    let public_binding =
                      Types.binding ~row_param_types:public_row_types public_name
                        (Types.qualify_module_type
                           (Names.module_path_to_ocaml module_path)
                           expr.ty)
                    in
                    let type_items = row_type_items local_row_types param_tys in
                    let value_item =
                      Recursive_value_binding
                        { name = local_name;
                          identity =
                            Source_context.find_identity name_form;
                          type_annotation = None;
                          expression = expr.semantic_expr;
                        }
                    in
                    Ok
                      ( Env.add key local_binding env,
                        export_function definition public_bindings
                          (key, public_binding),
                        next_type,
                        Group (type_items @ [ value_item ]) :: items ))))
    | FList
        (FSymbol (("defn" | "defn-") as definition) :: FSymbol name :: params
        :: body_forms) -> (
        let local_name = Names.sanitize_name name in
        let recursive =
          body_forms |> List.concat_map Dependency_graph.symbols
          |> List.exists (fun symbol -> symbol = name
               || symbol = Names.scoped_key module_path name)
        in
        let prepared =
          if recursive then
            prepare_inferred_recursive_fn ~ocaml_name:local_name module_path env
              name params body_forms
          else prepare_fn module_path env params body_forms
        in
        match prepared with
        | Error _ as err -> err
        | Ok parts -> (
            let local_name = Names.sanitize_name name in
            let public_name = module_binding_ocaml_name module_path name in
            let param_tys =
              parts.param_bindings
              |> List.map (fun (_key, (binding : binding)) -> binding.ty)
            in
            let local_row_types =
              row_param_type_names ~env local_name param_tys
            in
            let public_row_types =
              row_param_type_names ~env public_name param_tys
            in
            let expr = fn_code ~row_param_type_names:local_row_types parts in
            let key = module_binding_key module_path name in
            match
              check_emitted_name_collision env ~source_key:key ~ocaml_name:local_name
            with
            | Error _ as err -> err
            | Ok () -> (match expr.ty with
            | TFn _ ->
                let local_binding =
                  binding_of_expr ~row_param_types:local_row_types local_name expr
                in
                let public_binding =
                  Types.binding ~row_param_types:public_row_types
                    ?return_param_index:(expr.return_param_index) public_name
                    (Types.qualify_module_type
                       (Names.module_path_to_ocaml module_path)
                       expr.ty)
                in
                let type_items = row_type_items local_row_types param_tys in
                let value_item =
                  if recursive then
                    Recursive_value_binding
                      { name = local_name; identity = None; type_annotation = None;
                        expression = expr.semantic_expr }
                  else
                    Value_binding
                      { pattern = Named local_name; expression = expr.semantic_expr }
                in
                Ok
                  ( Env.add key local_binding env,
                    export_function definition public_bindings
                      (key, public_binding),
                    next_type,
                    Group (type_items @ [ value_item ]) :: items )
            | _ -> Error.error ~code:Error_code.Semantic "defn body did not compile to a function")))
    | FList
        (FSymbol "module" :: FSymbol nested_segment :: FSymbol nested_signature_name
        :: nested_forms) -> (
        let nested_path = module_path ^ "." ^ nested_segment in
        match
          compile_module ~signature_name:nested_signature_name scope env next_type
            nested_path nested_segment nested_forms
        with
        | Error _ as err -> err
        | Ok
            ( _scope,
              nested_env,
              nested_public_bindings,
              next_type,
              nested_item ) ->
            Ok
              ( Env.add_bindings nested_public_bindings nested_env,
                public_bindings @ nested_public_bindings,
                next_type,
                nested_item :: items ))
    | FList
        (FSymbol "module" :: ((FSymbol nested_segment) as name_form)
        :: nested_forms) -> (
        let nested_path = module_path ^ "." ^ nested_segment in
        match
          compile_module ?location:(Source_context.find name_form) scope env next_type
            nested_path nested_segment nested_forms
        with
        | Error _ as err -> err
        | Ok
            ( _scope,
              nested_env,
              nested_public_bindings,
              next_type,
              nested_item ) ->
            Ok
              ( Env.add_bindings nested_public_bindings nested_env,
                public_bindings @ nested_public_bindings,
                next_type,
                nested_item :: items ))
    | FList (FSymbol ("defn" | "defn-") :: _) ->
        Error.error ~code:Error_code.Arity "defn expects a name, parameter vector, and body"
    | FList (FSymbol "defonce" :: _) ->
        Error.error ~code:Error_code.Arity "defonce expects a name and value"
    | _ ->
        Error.error ~code:Error_code.Protocol
          "module forms must be module-signature, type-alias, type-record, type-variant, open, include, module-alias, defprotocol, extend-type, def, defonce, defn, defn-, or module"
  and loop env public_bindings next_type items = function
    | [] ->
        let module_name = Names.module_segment_to_ocaml module_segment in
        let protocols =
          Protocol_registry.qualify_implementations ~owner:[ module_path ]
            ~module_name:(Names.module_path_to_ocaml module_path)
            (Env.protocols env)
        in
        let env = Env.with_protocols protocols env in
        let qualify_local_name name =
          match Resolver.lookup_type_declaration module_path env name with
          | Some declaration
            when Type_id.owner declaration.type_id = [module_path] ->
              Type_registry.emitted_name ~scope:module_path
                (Names.sanitize_name (Type_id.name declaration.type_id))
          | _ -> name
        in
        let rec qualify_local_types = function
          | TOcaml name -> TOcaml (qualify_local_name name)
          | TOcaml_app (name, arguments) ->
              TOcaml_app (qualify_local_name name, List.map qualify_local_types arguments)
          | ty -> Semantic_type.map_children qualify_local_types ty
        in
        let public_bindings = List.map (fun (key, (binding : binding)) ->
          key, { binding with ty = qualify_local_types binding.ty }) public_bindings in
        let env =
          match signature_name with
          | None -> env
          | Some signature_name ->
              let signature_id =
                Signature_id.create
                  ~owner:(if scope = "" then [] else [ scope ])
                  ~name:signature_name
              in
              let types =
                Module_registry.abstract_signature_types signature_id
                  (Env.modules env)
                |> List.fold_left
                     (fun types type_name ->
                       Type_registry.hide_manifest ~scope:module_path type_name
                         types)
                     (Env.types env)
              in
              Env.with_types types env
        in
        let modules =
          if register_module then
            Module_registry.declare_module (module_id_of_path module_path)
              Concrete (Env.modules env)
          else Ok (Env.modules env)
        in
        (match modules with
        | Error _ as err -> err
        | Ok modules ->
            Ok
              ( scope,
                Env.with_modules modules env,
                public_bindings,
                next_type,
                Module_def
                  {
                    module_name;
                    location;
                    signature_name =
                      Option.map Names.module_path_to_ocaml signature_name;
                    signature_location;
                    items =
                      List.rev items
                      |> List.map
                           (Signature_contract.annotate
                              ~module_path:(Names.module_path_to_ocaml module_path)
                              env);
                  } ))
    | form :: rest -> (
        match compile_module_form env public_bindings next_type items form with
        | Error _ as err -> err
        | Ok (env, public_bindings, next_type, items) ->
            let env = match form, items with
              | FList (FSymbol "defn-" :: _), item :: _ ->
                  Interface_visibility.mark_private
                    ~module_path:(Names.module_path_to_ocaml module_path) env item
              | _ -> env
            in
            loop env public_bindings next_type items rest)
  in
  loop env [] next_type [] forms

let compile_module_functor ?location scope env next_type functor_name parameter_form
    body_forms =
  let rec parse_parameters acc = function
    | [] -> Ok (List.rev acc)
    | ((FSymbol parameter_name) as parameter_form)
      :: ((FSymbol parameter_signature) as signature_form)
      :: rest ->
        parse_parameters
          ({ parameter_name;
             parameter_location = Source_context.find parameter_form;
             signature_name = parameter_signature;
             signature_location = Source_context.find signature_form }
          :: acc)
          rest
    | [ _ ] ->
        Error.error ~code:Error_code.Semantic "module-functor parameters must be name/signature pairs"
    | _ -> Error.error ~code:Error_code.Semantic "module-functor parameters must be symbols"
  in
  match parameter_form with
  | FVector [] -> Error.error ~code:Error_code.Arity "module-functor parameter vector must not be empty"
  | FVector parameter_forms -> (
      match parse_parameters [] parameter_forms with
      | Error _ as err -> err
      | Ok parameters ->
          let rec collect_parameter_bindings bindings = function
            | [] -> Ok (List.rev bindings |> List.concat)
            | parameter :: rest -> (
                match
                  Module_metadata.signature_parameter_bindings env
                    parameter.parameter_name ~scope parameter.signature_name
                with
                | Error _ as err -> err
                | Ok parameter_bindings ->
                    collect_parameter_bindings
                      (parameter_bindings :: bindings) rest)
          in
          (match collect_parameter_bindings [] parameters with
          | Error _ as err -> err
          | Ok parameter_bindings ->
          let functor_env = Env.add_bindings parameter_bindings env in
          (match
             compile_module ~register_module:false scope functor_env next_type functor_name
               functor_name body_forms
           with
          | Error _ as err -> err
          | Ok (_scope, module_env, public_bindings, next_type, module_item) -> (
              match module_item with
              | Module_def { items; _ } ->
                  let functor_id =
                    Functor_id.create
                      ~owner:(if scope = "" then [] else [ scope ])
                      ~name:functor_name
                  in
                  let modules =
                    Module_registry.declare_module
                      (Module_id.create
                         ~owner:(if scope = "" then [] else [ scope ])
                         ~name:functor_name)
                      Functor (Env.modules env)
                  in
                  (match modules with
                  | Error _ as err -> err
                  | Ok modules ->
                      let modules =
                        Module_registry.store_functor_result functor_id
                          public_bindings modules
                        |> Module_registry.store_functor_parameters functor_id (List.map (fun parameter -> parameter.parameter_name) parameters)
                      in
                      let modules =
                        Module_registry.store_functor_protocols functor_id
                          (Env.protocols module_env) modules
                      in
                      let modules =
                        Module_registry.store_functor_types functor_id
                          (Env.types module_env) modules
                      in
                      let modules =
                        Module_registry.store_functor_modules functor_id
                          (Env.modules module_env) modules
                      in
                      let modules =
                        Module_registry.store_functor_aliases functor_id
                          (Env.modules module_env) modules
                      in
                      Ok
                        ( scope,
                          Env.with_modules modules env
                          |> Env.inherit_private_exports module_env,
                          next_type,
                          Module_functor
                            {
                              functor_name =
                                Names.module_segment_to_ocaml functor_name;
                              location;
                              parameters =
                                List.map
                                  (fun parameter ->
                                    { parameter with
                                      parameter_name =
                                        Names.module_segment_to_ocaml
                                          parameter.parameter_name;
                                      signature_name =
                                        Names.module_path_to_ocaml
                                          parameter.signature_name })
                                  parameters;
                              items;
                            } ))
              | _ ->
                  Error.error ~code:Error_code.Internal
                    "internal error: module functor body did not compile"))))
  | _ ->
      Error.error ~code:Error_code.Arity
        "module-functor expects a name, [parameter signature ...], and body"
