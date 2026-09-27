let compile_expr = Expression_elaborator.compile_expr
let compile_top_level = Top_level_elaborator.compile

type state = Compiler_state.t

let empty_state = Compiler_state.empty

let rec contains_inferred_type = function
  | Types.TPoly_variant row -> List.exists contains_inferred_type (List.filter_map snd row.tags)
  | Types.TUnknown | Types.TMeta _ | Types.TVar _ -> true
  | Types.TNullable ty | Types.TArray ty | Types.TRef ty | Types.TList ty
  | Types.TVector ty | Types.TSet ty | Types.TSeq ty ->
      contains_inferred_type ty
  | Types.TOcaml_app (_, arguments) | Types.TTuple arguments ->
      List.exists contains_inferred_type arguments
  | Types.TConstraint constraint_ ->
      List.exists contains_inferred_type
        (Types.constraint_children constraint_)
  | Types.TFn (parameters, return_ty) ->
      List.exists contains_inferred_type (return_ty :: parameters)
  | Types.TOverloaded_fn arities ->
      List.exists
        (fun (arity : Types.fn_arity) ->
          List.exists contains_inferred_type arity.fixed_params
          || (match arity.rest_param with
             | Some ty -> contains_inferred_type ty
             | None -> false)
          || contains_inferred_type arity.return_ty)
        arities
  | Types.TRecord fields | Types.TNamed_record { fields; _ } ->
      List.exists
        (fun (field : Types.field) -> contains_inferred_type field.ty)
        fields
  | Types.TInt | Types.TFloat | Types.TChar | Types.TString | Types.TRegex
  | Types.TMap_keys | Types.TSymbol | Types.TKeyword | Types.TBool | Types.TUnit
  | Types.TNil | Types.TOcaml _ ->
      false

let deferred_type_variables ty =
  let rec collect variables = function
    | Types.TPoly_variant row -> List.fold_left collect variables (List.filter_map snd row.tags)
    | Types.TUnknown | Types.TMeta _ | Types.TNil -> "a" :: variables
    | Types.TVar name -> name :: variables
    | Types.TNullable ty | Types.TArray ty | Types.TRef ty | Types.TList ty
    | Types.TVector ty | Types.TSet ty | Types.TSeq ty ->
        collect variables ty
    | Types.TOcaml_app (_, arguments) | Types.TTuple arguments ->
        List.fold_left collect variables arguments
    | Types.TConstraint constraint_ ->
        List.fold_left collect variables (Types.constraint_children constraint_)
    | Types.TFn (parameters, return_ty) ->
        List.fold_left collect (collect variables return_ty) parameters
    | Types.TOverloaded_fn arities ->
        List.fold_left
          (fun variables (arity : Types.fn_arity) ->
            let variables = collect variables arity.return_ty in
            let variables = List.fold_left collect variables arity.fixed_params in
            Option.fold ~none:variables ~some:(collect variables)
              arity.rest_param)
          variables arities
    | Types.TRecord fields ->
        List.fold_left
          (fun variables (field : Types.field) -> collect variables field.ty)
          variables fields
    | Types.TNamed_record record ->
        List.fold_left collect variables record.type_arguments
    | Types.TInt | Types.TFloat | Types.TChar | Types.TString | Types.TRegex
    | Types.TMap_keys | Types.TSymbol | Types.TKeyword | Types.TBool
    | Types.TUnit | Types.TOcaml _ ->
        variables
  in
  collect [] ty |> List.sort_uniq String.compare

let freshen_deferred_type ?return_param_index ty =
  let next = ref 0 in
  let fresh_variable () =
    let name = "lg_deferred_" ^ string_of_int !next in
    incr next;
    Types.TVar name
  in
  let rec freshen = function
    | Types.TPoly_variant _ as ty -> Semantic_type.map_children freshen ty
    | Types.TUnknown -> fresh_variable ()
    | Types.TMeta meta -> Type_solver.fresh ?location:meta.location ()
    | Types.TVar _ as ty -> ty
    | Types.TNullable ty -> Types.TNullable (freshen ty)
    | Types.TArray ty -> Types.TArray (freshen ty)
    | Types.TRef ty -> Types.TRef (freshen ty)
    | Types.TList ty -> Types.TList (freshen ty)
    | Types.TVector ty -> Types.TVector (freshen ty)
    | Types.TSet ty -> Types.TSet (freshen ty)
    | Types.TSeq ty -> Types.TSeq (freshen ty)
    | Types.TConstraint
        (Types.Seqable_constraint
          ({ element = element_ty; storage = value_ty; _ } as constraint_)) ->
        let erased =
          Types.equal element_ty Types.TUnknown
          && Types.equal value_ty Types.TUnknown
        in
        let element_ty =
          if Types.equal element_ty Types.TUnknown then
            Types.dynamic_constraint Types.TUnknown
          else freshen element_ty
        in
        let value_ty =
          if Types.equal value_ty Types.TUnknown then
            if erased then Types.dynamic_constraint Types.TUnknown
            else fresh_variable ()
          else freshen value_ty
        in
        Types.TConstraint
          (Types.Seqable_constraint
             { constraint_ with element = element_ty; storage = value_ty })
    | Types.TConstraint (Types.Protocol_constraint _) as constraint_ty ->
        freshen_protocol_constraint constraint_ty
    | Types.TConstraint constraint_ ->
        Types.TConstraint (Types.map_constraint freshen constraint_)
    | Types.TOcaml_app (name, arguments) ->
        Types.TOcaml_app (name, List.map freshen arguments)
    | Types.TTuple items -> Types.TTuple (List.map freshen items)
    | Types.TFn (parameters, return_ty) ->
        Types.TFn (List.map freshen parameters, freshen return_ty)
    | Types.TOverloaded_fn arities ->
        Types.TOverloaded_fn
          (List.map
             (fun (arity : Types.fn_arity) ->
               ({ fixed_params = List.map freshen arity.fixed_params;
                  rest_param = Option.map freshen arity.rest_param;
                  return_ty = freshen arity.return_ty;
                }
                 : Types.fn_arity))
             arities)
    | Types.TRecord fields ->
        Types.TRecord
          (List.map
             (fun (field : Types.field) ->
               { field with ty = freshen field.ty })
             fields)
    | Types.TNamed_record _ as ty -> ty
    | (Types.TInt | Types.TFloat | Types.TChar | Types.TString | Types.TRegex
      | Types.TMap_keys | Types.TSymbol | Types.TKeyword | Types.TBool
      | Types.TUnit | Types.TNil | Types.TOcaml _) as ty ->
        ty
  and freshen_protocol_constraint constraint_ty =
    let rec methods = function
      | Types.TUnit -> Some []
      | Types.TTuple [ method_ty; rest ] ->
          Option.map (fun rest -> method_ty :: rest) (methods rest)
      | _ -> None
    in
    let rec dynamic_unknowns = function
      | Types.TPoly_variant _ as ty -> ty
      | Types.TUnknown -> Types.dynamic_constraint Types.TUnknown
      | Types.TMeta _ as ty -> ty
      | Types.TVar _ as ty -> ty
      | Types.TNullable ty -> Types.TNullable (dynamic_unknowns ty)
      | Types.TArray ty -> Types.TArray (dynamic_unknowns ty)
      | Types.TRef ty -> Types.TRef (dynamic_unknowns ty)
      | Types.TList ty -> Types.TList (dynamic_unknowns ty)
      | Types.TVector ty -> Types.TVector (dynamic_unknowns ty)
      | Types.TSet ty -> Types.TSet (dynamic_unknowns ty)
      | Types.TSeq ty -> Types.TSeq (dynamic_unknowns ty)
      | Types.TOcaml_app (name, arguments) ->
          Types.TOcaml_app (name, List.map dynamic_unknowns arguments)
      | Types.TConstraint constraint_ ->
          Types.TConstraint
            (Types.map_constraint dynamic_unknowns constraint_)
      | Types.TTuple items -> Types.TTuple (List.map dynamic_unknowns items)
      | Types.TFn (parameters, return_ty) ->
          Types.TFn (List.map dynamic_unknowns parameters, dynamic_unknowns return_ty)
      | Types.TOverloaded_fn arities ->
          Types.TOverloaded_fn
            (List.map
               (fun (arity : Types.fn_arity) ->
                 ({ fixed_params = List.map dynamic_unknowns arity.fixed_params;
                    rest_param = Option.map dynamic_unknowns arity.rest_param;
                    return_ty = dynamic_unknowns arity.return_ty;
                  }
                   : Types.fn_arity))
               arities)
      | Types.TRecord fields ->
          Types.TRecord
            (List.map
               (fun (field : Types.field) ->
                 { field with ty = dynamic_unknowns field.ty })
               fields)
      | (Types.TNamed_record _ | Types.TInt | Types.TFloat | Types.TChar
      | Types.TString | Types.TRegex | Types.TMap_keys | Types.TSymbol
      | Types.TKeyword | Types.TBool | Types.TUnit | Types.TNil | Types.TOcaml _
        ) as ty ->
          ty
    in
    match Types.protocol_constraint_info constraint_ty with
    | None -> freshen constraint_ty
    | Some (protocol_id, witness_ty, value_ty) ->
        (* A witness whose receivers are already dynamic dispatches
           monomorphically in the implementation; freshening its container to a
           rigid variable would claim a polymorphism the generated code does
           not have. *)
        let dynamic_dispatch =
          match methods witness_ty with
          | Some method_tys ->
              List.exists
                (function
                  | Types.TFn (receiver :: _, _) -> Types.is_dynamic receiver
                  | _ -> false)
                method_tys
          | None -> false
        in
        let value_ty =
          if dynamic_dispatch then dynamic_unknowns value_ty
          else freshen value_ty
        in
        let freshened =
          match methods witness_ty with
        | None ->
            Types.protocol_constraint protocol_id [] value_ty
        | Some method_tys ->
            let freshen_method_position =
              if dynamic_dispatch then dynamic_unknowns else freshen
            in
            let method_tys =
              List.map
                (function
                  | Types.TFn (_receiver :: parameters, return_ty) ->
                      Types.TFn
                        ( Types.constraint_value_type value_ty
                          :: List.map freshen_method_position parameters,
                          freshen_method_position return_ty )
                  | method_ty -> freshen method_ty)
                method_tys
            in
            Types.protocol_constraint protocol_id method_tys value_ty
        in
        if Types.is_guarded_protocol_constraint constraint_ty then
          Types.guarded_protocol_constraint freshened
        else freshened
  in
  match ty with
  | Types.TFn (parameters, return_ty) ->
      let parameters = List.map freshen parameters in
      let return_ty =
        match (return_param_index, return_ty, parameters) with
        | None, Types.TUnknown, [ parameter ] ->
            Types.constraint_value_type parameter
        | Some index, _, _ -> (
            match List.nth_opt parameters index with
            | Some parameter -> (
                match freshen return_ty with
                | Types.TOcaml_app ("result", [ ok_ty; error_ty ])
                  when Types.equal ok_ty parameter
                       || Types.row_compatible ~expected:parameter
                            ~actual:ok_ty
                       || Types.row_compatible ~expected:ok_ty
                            ~actual:parameter ->
                    Types.TOcaml_app ("result", [ ok_ty; error_ty ])
                | _ -> Types.constraint_value_type parameter)
            | None -> freshen return_ty)
        | None, _, _ -> freshen return_ty
      in
      Types.TFn (parameters, return_ty)
  | ty -> freshen ty

let direct_deferred_self_calls name implementation_name expression =
  let recursive_name = implementation_name ^ "__recursive" in
  let rec direct = function
    | Semantic_ir.Typed (ty, expression) ->
        Semantic_ir.Typed (ty, direct expression)
    | Semantic_ir.Located (node_id, location, expression) ->
        Semantic_ir.Located (node_id, location, direct expression)
    | Semantic_ir.Fun (parameters, body) ->
        let found_self_call = ref false in
        let body =
          Semantic_ir.rewrite
            (function
              | Semantic_ir.Ident candidate
                when String.equal candidate name ->
                  found_self_call := true;
                  Semantic_ir.Ident recursive_name
              | expression -> expression)
            body
        in
        if !found_self_call then
          Semantic_ir.LetRecIn
            ( recursive_name,
              parameters,
              body,
              Semantic_ir.Ident recursive_name )
        else Semantic_ir.Fun (parameters, body)
    | expression -> expression
  in
  direct expression

let expand_deferred_binding name value_type return_param_index expression =
  let value_type = Types.align_deferred_param_types value_type expression in
  let value_type = freshen_deferred_type ?return_param_index value_type in
  let implementation_name = name ^ "__implementation" in
  let expression =
    direct_deferred_self_calls name implementation_name expression
  in
  let holder_type_name = implementation_name ^ "_holder" in
  let holder_field_name = "value" in
  let holder_type =
    Lowered.Polymorphic_holder_type
      { type_name = holder_type_name;
        field_name = holder_field_name;
        value_type;
        type_variables = deferred_type_variables value_type;
      }
  in
  let reference_type = Types.TRef (Types.TOcaml holder_type_name) in
  let reference =
    Lowered.Value_binding
      { pattern = Lowered.Named implementation_name;
        expression =
          Semantic_ir.annotate reference_type
            (Semantic_ir.Apply
               ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.of_value",
                 [ Semantic_ir.Record
                     ( [ ( holder_field_name,
                           Semantic_ir.Constructor ("None", None) ) ],
                       Some holder_type_name );
                 ] ));
      }
  in
  let implementation () =
    Semantic_ir.Apply
      ( Semantic_ir.Ident "Option.get",
        [ Semantic_ir.Field
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.deref",
                  [ Semantic_ir.Ident implementation_name ] ),
              holder_field_name );
        ] )
  in
  let parameter_patterns names parameter_types =
    List.map2
      (fun name ty ->
        if contains_inferred_type ty then Semantic_ir.PVar name
        else
          Semantic_ir.PConstraint
            (Semantic_ir.PVar name, Types.ocaml_name ty))
      names parameter_types
  in
  let wrapper =
    match value_type with
    | Types.TFn (parameter_types, _) ->
        let names =
          List.mapi
            (fun index _ -> "__lg_deferred_argument_" ^ string_of_int index)
            parameter_types
        in
        let patterns = parameter_patterns names parameter_types in
        Semantic_ir.Fun
          ( patterns,
            Semantic_ir.Apply
                ( implementation (),
                List.map (fun name -> Semantic_ir.Ident name) names ) )
    | Types.TOverloaded_fn arities ->
        let projection index =
          let rec descend expression remaining =
            if remaining = 0 then
              Semantic_ir.Apply (Semantic_ir.Ident "fst", [ expression ])
            else
              descend
                (Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ]))
                (remaining - 1)
          in
          descend (implementation ()) index
        in
        let arity_wrapper index (arity : Types.fn_arity) =
          let parameter_types =
            arity.fixed_params
            @ Option.fold ~none:[] ~some:(fun rest_ty -> [ Types.TSeq rest_ty ])
                arity.rest_param
          in
          let names =
            List.mapi
              (fun parameter_index _ ->
                "__lg_deferred_argument_" ^ string_of_int index ^ "_"
                ^ string_of_int parameter_index)
              parameter_types
          in
          Semantic_ir.Fun
            ( parameter_patterns names parameter_types,
              Semantic_ir.Apply
                ( projection index,
                  List.map (fun name -> Semantic_ir.Ident name) names ) )
        in
        let rec storage index = function
          | [] -> Semantic_ir.Unit
          | arity :: rest ->
              Semantic_ir.Tuple
                [ arity_wrapper index arity; storage (index + 1) rest ]
        in
        storage 0 arities
    | _ ->
        implementation ()
  in
  let wrapper =
    Lowered.Value_binding
      { pattern = Lowered.Named name;
        expression = Semantic_ir.annotate value_type wrapper;
      }
  in
  let initialize =
    Lowered.Value_binding
      { pattern = Lowered.Unit_pattern;
        expression =
          Semantic_ir.Apply
            ( Semantic_ir.Ident "ignore",
              [
                Semantic_ir.Apply
                  ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.reset",
                    [
                      Semantic_ir.Ident implementation_name;
                      Semantic_ir.Record
                        ( [ ( holder_field_name,
                              Semantic_ir.Constructor ("Some", Some expression) )
                            ],
                          Some holder_type_name );
                    ] );
              ] );
      }
  in
  ([ holder_type; reference; wrapper ], [ initialize ])

let rec value_pattern_name = function
  | Lowered.Named name -> Some name
  | Lowered.Located_value (_, _, pattern)
  | Lowered.Declared_value (pattern, _) -> value_pattern_name pattern
  | Lowered.Unit_pattern | Lowered.Ignore_pattern -> None

let rec provided_value_names = function
  | Lowered.Foreign_binding foreign -> [ foreign.name ]
  | Lowered.Value_binding { pattern; _ } ->
      Option.fold ~none:[] ~some:(fun name -> [ name ])
        (value_pattern_name pattern)
  | Lowered.Recursive_value_binding { name; _ }
  | Lowered.Deferred_value_binding { name; _ } ->
      [ name ]
  | Lowered.Recursive_value_bindings bindings ->
      List.map (fun (binding : Lowered.recursive_value) -> binding.name) bindings
  | Lowered.Record_def { var_name; _ }
  | Lowered.Projected_record_def { var_name; _ } ->
      [ var_name ]
  | Lowered.Group items -> List.concat_map provided_value_names items
  | Lowered.Polymorphic_holder_type _ | Lowered.Comment _
  | Lowered.Opaque_type _ | Lowered.Type_def _ | Lowered.Type_alias _ | Lowered.Type_variant _
  | Lowered.Module_def _ | Lowered.Module_alias _ | Lowered.Module_functor _
  | Lowered.Module_apply _ | Lowered.Module_signature _
  | Lowered.Open_module _ | Lowered.Include_module _ ->
      []

let rec item_references_identifier name = function
  | Lowered.Foreign_binding _ -> false
  | Lowered.Value_binding { expression; _ }
  | Lowered.Recursive_value_binding { expression; _ }
  | Lowered.Deferred_value_binding { expression; _ } ->
      Semantic_ir.exists_identifier (String.equal name) expression
  | Lowered.Recursive_value_bindings bindings ->
      List.exists
        (fun (binding : Lowered.recursive_value) ->
          Semantic_ir.exists_identifier (String.equal name) binding.expression)
        bindings
  | Lowered.Record_def { values; _ } ->
      List.exists
        (fun (_, expression) ->
          Semantic_ir.exists_identifier (String.equal name) expression)
        values
  | Lowered.Projected_record_def { source; _ } ->
      Semantic_ir.exists_identifier (String.equal name) source
  | Lowered.Group items -> List.exists (item_references_identifier name) items
  | Lowered.Module_def { items; _ } | Lowered.Module_functor { items; _ } ->
      List.exists (item_references_identifier name) items
  | Lowered.Polymorphic_holder_type _ | Lowered.Comment _
  | Lowered.Opaque_type _ | Lowered.Type_def _ | Lowered.Type_alias _ | Lowered.Type_variant _
  | Lowered.Module_alias _ | Lowered.Module_apply _
  | Lowered.Module_signature _ | Lowered.Open_module _
  | Lowered.Include_module _ ->
      false

let insert_after_leading_types insertions item =
  let is_leading_type = function
    | Lowered.Opaque_type _ | Lowered.Type_def _ | Lowered.Type_alias _ | Lowered.Type_variant _
    | Lowered.Polymorphic_holder_type _ | Lowered.Comment _ ->
        true
    | _ -> false
  in
  let rec split leading = function
    | item :: rest when is_leading_type item -> split (item :: leading) rest
    | rest -> List.rev_append leading (insertions @ rest)
  in
  match item with
  | Lowered.Group items -> Lowered.Group (split [] items)
  | item -> Lowered.Group (insertions @ [ item ])

let order_deferred_items items =
  let providers = List.map provided_value_names items in
  let item_count = List.length items in
  let scheduled = Array.make item_count [] in
  let hoisted = Array.make item_count [] in
  let earliest_reference name before =
    let rec find index =
      if index >= before then before
      else if item_references_identifier name (List.nth items index) then index
      else find (index + 1)
    in
    find 0
  in
  let schedule_initializer index expression initialize =
    let target =
      providers
      |> List.mapi (fun provider_index names ->
             if
               List.exists
                 (fun name ->
                   Semantic_ir.exists_identifier (String.equal name) expression)
                 names
             then provider_index
             else index)
      |> List.fold_left max index
    in
    scheduled.(target) <- initialize :: scheduled.(target)
  in
  let rec expand index = function
    | Lowered.Deferred_value_binding
        { name; value_type; return_param_index; expression } ->
        let immediate, deferred =
          expand_deferred_binding name value_type return_param_index expression
        in
        List.iter
          (fun (expression, initialize) ->
            schedule_initializer index expression initialize)
          (List.map (fun initialize -> (expression, initialize)) deferred);
        let target = earliest_reference name index in
        if target < index then (
          hoisted.(target) <- Lowered.Group immediate :: hoisted.(target);
          Lowered.Group [])
        else Lowered.Group immediate
    | Lowered.Group items -> Lowered.Group (List.map (expand index) items)
    | item -> item
  in
  let immediate =
    List.mapi (fun index item -> expand index item) items
  in
  immediate
  |> List.mapi (fun index item ->
         let item =
           match List.rev hoisted.(index) with
           | [] -> item
           | insertions -> insert_after_leading_types insertions item
         in
         match List.rev scheduled.(index) with
         | [] -> item
         | initializers -> (
             match item with
             | Lowered.Group items -> Lowered.Group (items @ initializers)
             | item -> Lowered.Group (item :: initializers)))

let share_expression ?(forbidden = []) shared_values expression =
  let shared_values = ref shared_values in
  let definitions = ref [] in
  let share name value =
    if
      Semantic_ir.exists_identifier
        (fun identifier -> List.mem identifier forbidden)
        value
    then value
    else if List.mem name !shared_values then Semantic_ir.Ident name
    else (
      shared_values := name :: !shared_values;
      definitions :=
        Lowered.Value_binding
          { pattern = Lowered.Named name; expression = value }
        :: !definitions;
      Semantic_ir.Ident name)
  in
  let shared_literal_name kind literal =
    let key = kind ^ ":" ^ literal in
    "__lg_const_"
    ^ String.sub (Digest.to_hex (Digest.string key)) 0 12
  in
  let generated_keyword_counts = Hashtbl.create 8 in
  let count_generated_keywords =
    Semantic_ir.rewrite (function
      | Semantic_ir.Apply
          ( Semantic_ir.Ident
              "Lg_runtime.Runtime_dynamic.keyword",
            [ Semantic_ir.String keyword ] ) as expression ->
          let name =
            shared_literal_name "keyword" (Printf.sprintf "%S" keyword)
          in
          Hashtbl.replace generated_keyword_counts name
            (1 + Option.value (Hashtbl.find_opt generated_keyword_counts name)
                   ~default:0);
          expression
      | expression -> expression)
  in
  ignore (count_generated_keywords expression);
  let expression =
    Semantic_ir.rewrite
      (function
        | Semantic_ir.SharedValue (name, value) -> share name value
        | Semantic_ir.Apply
            ( Semantic_ir.Ident
                "Lg_runtime.Runtime_dynamic.keyword",
              [ Semantic_ir.String keyword ] ) as expression ->
            let name =
              shared_literal_name "keyword" (Printf.sprintf "%S" keyword)
            in
            if
              List.mem name !shared_values
              || Option.value (Hashtbl.find_opt generated_keyword_counts name)
                   ~default:0
                 > 1
            then share name expression
            else expression
        | expression -> expression)
      expression
  in
  (List.rev !definitions, expression, !shared_values)

let share_expressions shared_values expressions =
  let rec loop shared_values definitions compiled = function
    | [] -> (List.rev definitions, List.rev compiled, shared_values)
    | expression :: rest ->
        let new_definitions, expression, shared_values =
          share_expression shared_values expression
        in
        loop shared_values
          (List.rev_append new_definitions definitions)
          (expression :: compiled) rest
  in
  loop shared_values [] [] expressions

let rec share_item_expressions shared_values item =
  let grouped definitions item =
    match definitions with
    | [] -> [ item ]
    | _ -> [ Lowered.Group (definitions @ [ item ]) ]
  in
  let share_single ?(forbidden = []) rebuild expression =
    let definitions, expression, shared_values =
      share_expression ~forbidden shared_values expression
    in
    (grouped definitions (rebuild expression), shared_values)
  in
  match item with
  | Lowered.Value_binding binding ->
      let forbidden =
        match binding.pattern with Lowered.Named name -> [ name ] | _ -> []
      in
      share_single ~forbidden
        (fun expression -> Lowered.Value_binding { binding with expression })
        binding.expression
  | Lowered.Recursive_value_binding binding ->
      share_single ~forbidden:[ binding.name ]
        (fun expression ->
          Lowered.Recursive_value_binding { binding with expression })
        binding.expression
  | Lowered.Recursive_value_bindings bindings ->
      let forbidden =
        List.map (fun (binding : Lowered.recursive_value) -> binding.name) bindings
      in
      let definitions, expressions, shared_values =
        let rec loop shared_values definitions compiled = function
          | [] -> (List.rev definitions, List.rev compiled, shared_values)
          | (binding : Lowered.recursive_value) :: rest ->
              let new_definitions, expression, shared_values =
                share_expression ~forbidden shared_values binding.expression
              in
              loop shared_values
                (List.rev_append new_definitions definitions)
                (expression :: compiled) rest
        in
        loop shared_values [] [] bindings
      in
      let bindings =
        List.map2
          (fun (binding : Lowered.recursive_value) expression ->
            { binding with expression })
          bindings expressions
      in
      ( grouped definitions (Lowered.Recursive_value_bindings bindings),
        shared_values )
  | Lowered.Deferred_value_binding binding ->
      share_single ~forbidden:[ binding.name ]
        (fun expression ->
          Lowered.Deferred_value_binding { binding with expression })
        binding.expression
  | Lowered.Record_def definition ->
      let definitions, expressions, shared_values =
        share_expressions shared_values (List.map snd definition.values)
      in
      let values =
        List.map2
          (fun (field, _) expression -> (field, expression))
          definition.values expressions
      in
      ( grouped definitions (Lowered.Record_def { definition with values }),
        shared_values )
  | Lowered.Projected_record_def definition ->
      share_single ~forbidden:[ definition.var_name ]
        (fun source ->
          Lowered.Projected_record_def { definition with source })
        definition.source
  | Lowered.Group items ->
      let items, shared_values = share_item_list shared_values items in
      ([ Lowered.Group items ], shared_values)
  | Lowered.Module_def definition ->
      let items, _ = share_item_list [] definition.items in
      ([ Lowered.Module_def { definition with items } ], shared_values)
  | Lowered.Module_functor definition ->
      let items, _ = share_item_list [] definition.items in
      ([ Lowered.Module_functor { definition with items } ], shared_values)
  | item -> ([ item ], shared_values)

and share_item_list shared_values items =
  let rec loop shared_values compiled = function
    | [] -> (List.rev compiled, shared_values)
    | item :: rest ->
        let items, shared_values =
          share_item_expressions shared_values item
        in
        loop shared_values (List.rev_append items compiled) rest
  in
  loop shared_values [] items

let rec form_references_unresolved_declaration scope env = function
  | Ast.FSymbol name -> (
      match Resolver.lookup_binding scope env name with
      | Ok (binding : Types.binding) ->
          Types.equal binding.ty (Types.TOcaml "__declared_fn")
          || (binding.forward_declared && contains_inferred_type binding.ty)
      | Error _ -> false)
  | Ast.FList (Ast.FSymbol ("quote" | "clojure.core/quote") :: _) -> false
  | Ast.FList forms | Ast.FVector forms ->
      List.exists (form_references_unresolved_declaration scope env) forms
  | Ast.FMap pairs ->
      List.exists
        (fun (key, value) ->
          form_references_unresolved_declaration scope env key
          || form_references_unresolved_declaration scope env value)
        pairs
  | Ast.FCoreSymbol _ | Ast.FKeyword _ | Ast.FString _ | Ast.FRegex _
  | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _ ->
      false

let rec form_references_names names = function
  | Ast.FSymbol name ->
      List.exists
        (fun provider ->
          name = provider || String.ends_with ~suffix:("/" ^ provider) name)
        names
  | Ast.FList (Ast.FSymbol ("quote" | "clojure.core/quote") :: _) -> false
  | Ast.FList forms | Ast.FVector forms ->
      List.exists (form_references_names names) forms
  | Ast.FMap pairs ->
      List.exists
        (fun (key, value) ->
          form_references_names names key || form_references_names names value)
        pairs
  | Ast.FCoreSymbol _ | Ast.FKeyword _ | Ast.FString _ | Ast.FRegex _
  | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _ ->
      false

let add_unresolved_names names form =
  List.fold_left
    (fun names name ->
      if List.mem name names then names else name :: names)
    names (Dependency_graph.provided_names form)

let remove_resolved_names names form =
  let resolved = Dependency_graph.provided_names form in
  List.filter (fun name -> not (List.mem name resolved)) names

let resolve_anonymous_record_patterns env items =
  let rec resolve_pattern = function
    | Semantic_ir.PPolyTag (name, payload) -> Semantic_ir.PPolyTag (name, Option.map resolve_pattern payload)
    | Semantic_ir.PLocated (node_id, location, pattern) ->
        Semantic_ir.PLocated
          (node_id, location, resolve_pattern pattern)
    | Semantic_ir.PTyped (pattern, Types.TRecord fields) -> (
        let owner = Source_context.anonymous_record_owner "" in
        let record =
          match
            Compiler_environment.find_oldest_anonymous_record ~owner fields env
          with
          | Some _ as record -> record
          | None ->
              Compiler_environment.find_oldest_anonymous_record_by_layout
                ~owner fields env
        in
        match record with
        | Some record ->
            Semantic_ir.PConstraint
              ( resolve_pattern pattern,
                Structural_map.record_type_application record )
        | None ->
            Semantic_ir.PTyped
              (resolve_pattern pattern, Types.TRecord fields))
    | Semantic_ir.PTyped (pattern, ty) ->
        Semantic_ir.PTyped (resolve_pattern pattern, ty)
    | Semantic_ir.PConstructor (name, payload) ->
        Semantic_ir.PConstructor (name, Option.map resolve_pattern payload)
    | Semantic_ir.PTuple patterns ->
        Semantic_ir.PTuple (List.map resolve_pattern patterns)
    | Semantic_ir.PList patterns ->
        Semantic_ir.PList (List.map resolve_pattern patterns)
    | Semantic_ir.PCons (head, tail) ->
        Semantic_ir.PCons (resolve_pattern head, resolve_pattern tail)
    | Semantic_ir.PRecord fields ->
        Semantic_ir.PRecord
          (List.map
             (fun (name, pattern) -> (name, resolve_pattern pattern))
             fields)
    | Semantic_ir.PAlias (pattern, name) ->
        Semantic_ir.PAlias (resolve_pattern pattern, name)
    | Semantic_ir.POr (left, right) ->
        Semantic_ir.POr (resolve_pattern left, resolve_pattern right)
    | Semantic_ir.PConstraint (pattern, type_name) ->
        Semantic_ir.PConstraint (resolve_pattern pattern, type_name)
    | (Semantic_ir.PVar _ | Semantic_ir.PAny | Semantic_ir.PUnit
      | Semantic_ir.PInt _ | Semantic_ir.PInt64 _ | Semantic_ir.PString _
      | Semantic_ir.PBool _) as pattern ->
        pattern
  in
  let resolve_expression expression =
    Semantic_ir.rewrite
      (function
        | Semantic_ir.Fun (patterns, body) ->
            Semantic_ir.Fun (List.map resolve_pattern patterns, body)
        | Semantic_ir.Let (bindings, body) ->
            Semantic_ir.Let
              (List.map
                 (fun (pattern, value) ->
                   (resolve_pattern pattern, value))
                 bindings,
               body)
        | Semantic_ir.LetRecGroup (bindings, body) ->
            Semantic_ir.LetRecGroup
              (List.map (fun (pattern, value) -> (resolve_pattern pattern, value))
                 bindings, body)
        | Semantic_ir.LetRec (name, patterns, body, arguments) ->
            Semantic_ir.LetRec
              (name, List.map resolve_pattern patterns, body, arguments)
        | Semantic_ir.LetRecIn (name, patterns, body, next) ->
            Semantic_ir.LetRecIn
              (name, List.map resolve_pattern patterns, body, next)
        | Semantic_ir.Match (target, cases) ->
            Semantic_ir.Match
              (target,
               List.map
                 (fun (pattern, body) ->
                   (resolve_pattern pattern, body))
                 cases)
        | Semantic_ir.Match_guarded (target, cases) ->
            Semantic_ir.Match_guarded
              (target,
               List.map
                 (fun (pattern, guard, body) ->
                   (resolve_pattern pattern, guard, body))
                 cases)
        | Semantic_ir.Try (body, cases) ->
            Semantic_ir.Try
              (body,
               List.map
                 (fun (pattern, guard, result) ->
                   (resolve_pattern pattern, guard, result))
                 cases)
        | expression -> expression)
      expression
  in
  let rec resolve_item = function
    | Lowered.Value_binding binding ->
        Lowered.Value_binding
          { binding with expression = resolve_expression binding.expression }
    | Lowered.Recursive_value_binding binding ->
        Lowered.Recursive_value_binding
          { binding with expression = resolve_expression binding.expression }
    | Lowered.Recursive_value_bindings bindings ->
        Lowered.Recursive_value_bindings
          (List.map
             (fun (binding : Lowered.recursive_value) ->
               { binding with
                 expression = resolve_expression binding.expression;
               })
             bindings)
    | Lowered.Deferred_value_binding binding ->
        Lowered.Deferred_value_binding
          { binding with expression = resolve_expression binding.expression }
    | Lowered.Record_def definition ->
        Lowered.Record_def
          { definition with
            values =
              List.map
                (fun (field, value) ->
                  (field, resolve_expression value))
                definition.values;
          }
    | Lowered.Projected_record_def definition ->
        Lowered.Projected_record_def
          { definition with source = resolve_expression definition.source }
    | Lowered.Group items -> Lowered.Group (List.map resolve_item items)
    | Lowered.Module_def definition ->
        Lowered.Module_def
          { definition with items = List.map resolve_item definition.items }
    | Lowered.Module_functor definition ->
        Lowered.Module_functor
          { definition with items = List.map resolve_item definition.items }
    | item -> item
  in
  List.map resolve_item items

let predeclare_adjacent_defrecords scope env pending =
  let rec declarations declared = function
    | (_, Ast.FList (Ast.FSymbol "defrecord" :: Ast.FSymbol name :: _)) :: rest
      ->
        declarations (name :: declared) rest
    | _ -> List.rev declared
  in
  match declarations [] pending with
  | [] -> env
  | names ->
      List.fold_left
        (fun env name ->
          let key = Resolver.record_type_key scope name in
          match Compiler_environment.find_opt key env with
          | Some _ -> env
          | None ->
              let type_name = Names.ocaml_binding_name scope name in
              let type_id =
                Type_id.create
                  ~owner:(if scope = "" then [] else [ scope ])
                  ~name
              in
              let record_ty =
                Types.named_record ~type_id ~nominal:false ~type_name
                  ~set_module_name:("Set_" ^ type_name) []
              in
              Compiler_environment.add key
                (Types.binding ~forward_declared:true type_name record_ty)
                env)
        env names

let compile_forms_incremental (state : Compiler_state.t) forms =
  let report_timings = Sys.getenv_opt "LG_COMPILE_TIMINGS" = Some "1" in
  let finish scope env next_type items =
    let items =
      items
      |> List.sort (fun (left, _) (right, _) -> Int.compare left right)
      |> List.map (fun (_, item) -> Signature_contract.annotate env item)
    in
    Ok (scope, env, next_type, items)
  in
  let rec compile_pending scope env next_type items unresolved_names pending =
    let env = predeclare_adjacent_defrecords scope env pending in
    let rec loop scope env next_type items unresolved_names deferred first_error
        made_progress = function
      | [] ->
          if deferred = [] then finish scope env next_type items
          else if made_progress then
            compile_pending scope env next_type items unresolved_names
              (List.rev deferred)
          else (
            match first_error with
            | Some error -> Error error
            | None -> Error.error "declared forms made no compilation progress")
      | (index, form) :: rest -> (
        let started_at = if report_timings then Sys.time () else 0.0 in
        let compiled = compile_top_level scope env next_type form in
        let elapsed = if report_timings then Sys.time () -. started_at else 0.0 in
        if report_timings && elapsed >= 0.01 then (
          let names = Dependency_graph.provided_names form in
          Printf.eprintf "lg: form %d%s: %.3fs\n%!" index
            (match names with
            | [] -> ""
            | _ -> " (" ^ String.concat ", " names ^ ")")
            elapsed);
        match compiled with
        | Error error ->
            let error =
              Error.with_location_if_missing (Source_context.find form) error
            in
            let can_defer =
              form_references_unresolved_declaration scope env form
              || form_references_names unresolved_names form
              || (unresolved_names <> []
                 && (String.starts_with
                       ~prefix:"missing protocol implementation for "
                       error.Error.message
                    || String.starts_with
                         ~prefix:"no protocol implementation for "
                         error.Error.message))
            in
            if can_defer then
              let first_error =
                match first_error with
                | Some _ -> first_error
                | None -> Some error
              in
              let unresolved_names =
                add_unresolved_names unresolved_names form
              in
              loop scope env next_type items unresolved_names
                ((index, form) :: deferred) first_error made_progress rest
            else Error error
        | Ok (scope, env, next_type, item) ->
            let env = match form with
              | Ast.FList (Ast.FSymbol "defn-" :: _) ->
                  Interface_visibility.mark_private env item
              | _ -> env
            in
            let unresolved_names =
              remove_resolved_names unresolved_names form
            in
            loop scope env next_type ((index, item) :: items) unresolved_names
              deferred first_error true rest)
    in
    loop scope env next_type items unresolved_names [] None false pending
  in
  let indexed_forms = List.mapi (fun index form -> (index, form)) forms in
  match
    compile_pending state.scope state.env state.next_type [] [] indexed_forms
  with
  | Error _ as err -> err
  | Ok (scope, env, next_type, new_items) ->
      let new_items =
        new_items |> order_deferred_items
        |> resolve_anonymous_record_patterns env
      in
      let new_items, _shared_values = share_item_list [] new_items in
      let next_state =
        {
          Compiler_state.scope;
          Compiler_state.env;
          next_type;
          items = state.items;
          shared_values = [];
        }
      in
      Ok (next_state, new_items)

let compile_forms forms =
  match compile_forms_incremental empty_state forms with
  | Error _ as err -> err
  | Ok (_state, items) -> Ok items
