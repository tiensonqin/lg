open Types
open Expression_support
module Env = Compiler_environment

let unique_named_records records =
  List.fold_left
    (fun unique record ->
      if
        List.exists
          (fun existing -> Type_id.equal existing.type_id record.type_id)
          unique
      then unique
      else record :: unique)
    [] records

let same_host_wrapper expected actual =
  let same_outer =
    match (expected, actual) with
    | TArray _, TArray _ | TRef _, TRef _ | TNullable _, TNullable _ -> true
    | TOcaml_app (expected_name, expected_args),
      TOcaml_app (actual_name, actual_args) ->
        expected_name = actual_name
        && List.length expected_args = List.length actual_args
    | TTuple expected_items, TTuple actual_items ->
        List.length expected_items = List.length actual_items
    | _ -> false
  in
  same_outer
  && Types.assignable ~policy:Host_boundary ~expected ~actual

let rec record_inference_compatible env ~allow_expected_dynamic expected_fields
    actual_fields =
  let rec has_record_requirement = function
    | TRecord (_ :: _) -> true
    | TRef payload | TNullable payload | TOcaml_app ("option", [ payload ]) ->
        has_record_requirement payload
    | _ -> false
  in
  let rec reference_payload_compatible expected actual =
    match expected, actual with
    | TRecord fields, (TRecord actual_fields | TNamed_record { fields = actual_fields; _ }) ->
        record_inference_compatible env ~allow_expected_dynamic fields actual_fields
    | (TNullable expected | TOcaml_app ("option", [ expected ])),
      (TNullable actual | TOcaml_app ("option", [ actual ]))
    | TRef expected, TRef actual -> reference_payload_compatible expected actual
    | _ -> false
  in
  expected_fields
  |> List.for_all (fun (expected : field) ->
         match find_field expected.keyword actual_fields with
         | None ->
             Option.is_some (Types.find_record_extension_field actual_fields)
         | Some actual ->
             (match expected.ty, actual.ty with
             | TRef expected, TRef actual when has_record_requirement expected ->
                 reference_payload_compatible expected actual
             | _ ->
             let expected_dynamic_compatible =
               match Types.dynamic_constraint_info expected.ty with
               | Some capability when not (Types.equal capability TUnknown) ->
                   Types.equal capability actual.ty
                   || Types.row_compatible ~expected:capability
                        ~actual:actual.ty
               | Some _ -> allow_expected_dynamic
               | None -> false
             in
             let open_type_compatible =
               match Type_solver.unify Type_solver.empty expected.ty actual.ty with
               | Ok _ -> true
               | Error _ -> false
             in
             let expected_protocol_compatible =
               match Types.protocol_constraint_info expected.ty with
               | Some (protocol_id, _, _) ->
                   Protocol.type_satisfies env protocol_id actual.ty
               | None -> false
             in
            let expected_seqable_compatible =
              Option.is_some (Types.seqable_constraint_info expected.ty)
               && Collection_capability.accepts_seqable env actual.ty
            in
            let expected_contains_compatible =
              Option.is_some (Types.contains_constraint_info expected.ty)
              && Collection_capability.accepts_contains actual.ty
            in
             Types.is_dynamic actual.ty
             || (match actual.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
             || (match expected.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false)
             || expected_dynamic_compatible
             || open_type_compatible
             || expected_protocol_compatible
             || expected_seqable_compatible
             || expected_contains_compatible
             || Types.equal expected.ty actual.ty
             || same_host_wrapper expected.ty actual.ty
             || Types.row_compatible ~expected:expected.ty ~actual:actual.ty))

let structural_named_record_can_rematch (record : named_record) =
  (not record.nominal)
  && (Type_id.owner record.type_id = []
      ||
      (String.length record.type_name > 1
       && record.type_name.[0] = 't'
       && String.for_all
            (fun character -> character >= '0' && character <= '9')
            (String.sub record.type_name 1 (String.length record.type_name - 1))))
  && not (String.contains record.type_name '.')

let rec infer_named_record ?(allow_dynamic_fields = false) ?preferred_record
    ?(required_protocols = []) scope env = function
  | TPoly_variant _ as ty -> Semantic_type.map_children (infer_named_record scope env) ty
  | TNamed_record record when structural_named_record_can_rematch record ->
      infer_named_record ?preferred_record ~allow_dynamic_fields
        ~required_protocols scope env (TRecord record.fields)
  | TNamed_record record as ty -> (
      match
        Resolver.lookup_record_type scope env (Type_id.to_string record.type_id)
      with
      | Ok canonical -> (
          match Types.refresh_named_record canonical ty with
          | TNamed_record refreshed when String.contains record.type_name '.' ->
              TNamed_record
                {
                  refreshed with
                  type_name = record.type_name;
                  set_module_name = record.set_module_name;
                }
          | refreshed -> refreshed)
      | Error _ -> ty)
  | TNullable inner ->
      TNullable (infer_named_record ~allow_dynamic_fields scope env inner)
  | TArray inner ->
      TArray (infer_named_record ~allow_dynamic_fields scope env inner)
  | TRef inner -> TRef (infer_named_record ~allow_dynamic_fields scope env inner)
  | TList inner ->
      TList (infer_named_record ~allow_dynamic_fields scope env inner)
  | TVector inner ->
      TVector (infer_named_record ~allow_dynamic_fields scope env inner)
  | TSet inner -> TSet (infer_named_record ~allow_dynamic_fields scope env inner)
  | TSeq inner -> TSeq (infer_named_record ~allow_dynamic_fields scope env inner)
  | TFn (parameters, return_ty) ->
      TFn
        ( List.map
            (infer_named_record ~allow_dynamic_fields scope env)
            parameters,
          infer_named_record ~allow_dynamic_fields scope env return_ty )
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun (arity : fn_arity) ->
             {
               fixed_params =
                 List.map
                   (infer_named_record ~allow_dynamic_fields scope env)
                   arity.fixed_params;
               rest_param =
                 Option.map
                   (infer_named_record ~allow_dynamic_fields scope env)
                   arity.rest_param;
               return_ty =
                 infer_named_record ~allow_dynamic_fields scope env
                   arity.return_ty;
             })
           arities)
  | TTuple items ->
      TTuple
        (List.map (infer_named_record ~allow_dynamic_fields scope env) items)
  | TOcaml_app ("option", [ inner ]) ->
      TOcaml_app
        ("option", [ infer_named_record ~allow_dynamic_fields scope env inner ])
  | ty when Types.is_dynamic ty -> (
      match Types.dynamic_constraint_info ty with
      | None -> assert false
      | Some capability -> (
          let open_record_capability =
            match capability with
            | TRecord fields ->
                Option.is_some (Types.find_record_extension_field fields)
            | _ -> false
          in
          let capability =
            match capability with
            | TRecord fields when open_record_capability ->
                TRecord
                  (List.map
                     (fun (field : field) ->
                       {
                         field with
                         ty =
                           infer_named_record ~allow_dynamic_fields:true scope
                             env field.ty;
                       })
                     fields)
            | capability ->
                infer_named_record ~allow_dynamic_fields:true scope env
                  capability
          in
          if open_record_capability then Types.dynamic_constraint capability
          else
            match Types.constraint_value_type capability with
            | TNamed_record _ -> capability
            | _ -> Types.dynamic_constraint capability))
  | ty when Option.is_some (Types.protocol_constraint_info ty) -> (
      match Types.protocol_constraint_info ty with
      | None -> assert false
      | Some (protocol_id, _, value_ty) ->
          Types.protocol_constraint_with_value ty
            (infer_named_record ~allow_dynamic_fields:true ?preferred_record
               ~required_protocols:(protocol_id :: required_protocols)
               scope env value_ty))
  | TConstraint
      (Seqable_constraint
        ({ element = TRecord fields; storage = container; _ } as constraint_)) ->
      let fields =
        List.map
          (fun (field : field) ->
            {
              field with
              ty =
                infer_named_record ~allow_dynamic_fields scope env field.ty;
            })
          fields
      in
      TConstraint
        (Seqable_constraint
           {
             constraint_ with
             element = TRecord fields;
             storage =
               infer_named_record ~allow_dynamic_fields scope env container;
           })
  | TOcaml_app (name, arguments) ->
      let arguments =
        List.map
          (infer_named_record ~allow_dynamic_fields scope env)
          arguments
      in
      let record_name =
        if String.starts_with ~prefix:"__lg_record_app:" name then
          String.sub name
            (String.length "__lg_record_app:")
            (String.length name - String.length "__lg_record_app:")
        else name
      in
      (match Resolver.lookup_type_declaration scope env record_name with
      | Some
          {
            kind = Alias;
            type_parameters;
            manifest = Some manifest;
            _;
          }
        when List.length type_parameters = List.length arguments ->
          let substitutions = List.combine type_parameters arguments in
          let resolved =
            Types.substitute_type_variables
              (Type_solver.of_list
                 (List.map
                    (fun (parameter, argument) ->
                      (Type_solver.Declared parameter, argument))
                    substitutions))
              manifest
          in
          if Types.equal resolved (TOcaml_app (name, arguments)) then
            TOcaml_app (name, arguments)
          else infer_named_record ~allow_dynamic_fields scope env resolved
      | Some { kind = Alias; _ } -> TOcaml_app (name, arguments)
      | Some { kind = (Record | Variant | Opaque); _ } | None ->
      (match
         (match Resolver.lookup_record_type scope env record_name with
         | Ok _ as record -> record
         | Error _ as error ->
             match Collection_capability.find_canonical_record env record_name with
             | Some record -> Ok record
             | None -> error)
       with
      | Ok record
        when List.length record.type_parameters = List.length arguments ->
          let parameters = List.map (fun _ -> Type_solver.fresh ()) arguments in
          let renamings =
            Type_solver.of_list
              (List.map2
                 (fun parameter argument -> Type_solver.Declared parameter, argument)
                 record.type_parameters parameters)
          in
          Types.instantiate_type ~templates:parameters ~actuals:arguments
            (Type_solver.apply renamings (TNamed_record record))
      | Ok _ | Error _ -> TOcaml_app (name, arguments)))
  | TOcaml name as ty ->
      let record_prefix = "__lg_record:" in
      let source_name =
        if String.starts_with ~prefix:record_prefix name then
          String.sub name (String.length record_prefix)
            (String.length name - String.length record_prefix)
        else name
      in
      (match Resolver.lookup_record_type scope env source_name with
      | Ok record -> TNamed_record record
      | Error _ ->
          (match Resolver.lookup_type_declaration scope env source_name with
          | Some
              {
                kind = Alias;
                type_parameters = [];
                manifest = Some manifest;
                _;
              }
            when not (Types.equal manifest ty) ->
              infer_named_record ~allow_dynamic_fields scope env manifest
          | Some { kind = Alias; _ } -> ty
          | Some { kind = (Variant | Opaque); type_id; _ } ->
              let type_name = Names.sanitize_name (Type_id.name type_id) in
              let owner = Type_id.owner type_id |> String.concat "." in
              let owner_is_module =
                owner <> ""
                && Module_registry.mem_module
                     (Module_id.create ~owner:[] ~name:owner)
                     (Env.modules env)
              in
              if
                (String.contains source_name '.'
                || String.contains source_name '/')
                && owner_is_module
              then
                TOcaml (Type_registry.emitted_name ~scope:owner type_name)
              else TOcaml type_name
          | Some { kind = Record; _ } | None ->
              Env.find_record_binding
                (fun _ (binding : binding) ->
                     match binding.ty with
                     | TNamed_record record
                       when String.equal record.type_name source_name ->
                       Some (TNamed_record record)
                     | _ -> None)
                env
              |> Option.value ~default:ty))
  | TRecord fields -> (
      let fields =
        List.map
          (fun (field : field) ->
            { field with ty = infer_named_record scope env field.ty })
          fields
      in
      let inferred = TRecord fields in
      let candidates =
        Env.filter_record_bindings
          (fun key (binding : binding) ->
            if String.starts_with ~prefix:"__record/" key then
              match binding.ty with
              | TNamed_record record ->
                  let compatible =
                    record_inference_compatible env
                      ~allow_expected_dynamic:allow_dynamic_fields fields
                      record.fields
                  in
                  if compatible
                  then Some record
                  else None
              | _ -> None
            else None)
          env
        |> unique_named_records
        |> List.filter (fun record ->
               List.for_all
                 (fun protocol_id ->
                   Protocol.type_satisfies env protocol_id
                     (TNamed_record record))
                 required_protocols)
      in
      let candidates =
        match preferred_record with
        | Some _ -> candidates
        | None when List.exists (fun (field : field) -> field.mutable_) fields ->
            List.filter
              (fun record ->
                List.for_all
                  (fun (field : field) ->
                    not field.mutable_
                    ||
                    match Types.find_field field.keyword record.fields with
                    | Some target -> target.mutable_
                    | None -> false)
                  fields)
              candidates
        | None -> candidates
      in
      let rec direct_match_count fields actual_fields =
        List.fold_left
             (fun count field ->
               match find_field field.keyword actual_fields with
               | Some actual when not (Types.is_record_extension_field actual) ->
                   count + 1 + nested_match_count field.ty actual.ty
               | Some _ | None -> count)
             0 fields
      and nested_match_count expected actual =
        match expected, actual with
        | TRef expected, TRef actual -> nested_match_count expected actual
        | TRecord expected, (TRecord actual | TNamed_record {fields = actual; _}) ->
            direct_match_count expected actual
        | _ -> 0
      in
      let direct_match_count record = direct_match_count fields record.fields in
      let best_direct_matches =
        candidates
        |> List.fold_left
             (fun best record -> max best (direct_match_count record))
             0
      in
      let candidates =
        if best_direct_matches = 0 then candidates
        else
          List.filter
            (fun record -> direct_match_count record = best_direct_matches)
            candidates
      in
      let selected =
        match candidates with
        | [ record ] -> Some record
        | _ -> (
            match preferred_record with
            | Some (TNamed_record preferred) ->
                List.find_opt
                  (fun record -> Type_id.equal record.type_id preferred.type_id)
                  candidates
            | Some _ | None -> None)
      in
      match selected with
      | Some record ->
          let matched_fields =
            record.fields
            |> List.filter_map (fun (template : field) ->
                   match find_field template.keyword fields with
                   | Some (actual : field)
                     when not (Types.equal actual.ty TUnknown) ->
                       Some (template.ty, actual.ty)
                   | Some _ | None -> None)
          in
          let templates, actuals = List.split matched_fields in
          Types.instantiate_type ~templates ~actuals (TNamed_record record)
      | None -> (
          (* No declared record matched: reuse the oldest anonymous record
             with this exact shape instead of materializing a duplicate one. *)
          match
            Env.find_oldest_anonymous_record
              ~owner:(Source_context.anonymous_record_owner "") fields env
          with
          | Some record -> TNamed_record record
          | None -> inferred))
  | TConstraint constraint_ ->
      TConstraint
        (Types.map_constraint
           (infer_named_record ~allow_dynamic_fields scope env) constraint_)
  | inferred -> inferred

let rec infer_parameter_named_record scope env = function
  | ty when Option.is_some (Types.protocol_constraint_info ty) -> (
      match Types.protocol_constraint_info ty with
      | Some (_, _, value_ty) ->
          Types.protocol_constraint_with_value ty
            (infer_parameter_named_record scope env value_ty)
      | None -> assert false)
  | TConstraint
      (Seqable_constraint
        ({
           element = TRecord (_ :: _ as fields);
           storage = container;
           _;
         } as constraint_))
    when (match Types.constraint_value_type container with
         | TUnknown | TMeta _ | TVar _ -> true
         | _ -> false) ->
      TConstraint
        (Seqable_constraint
           {
             constraint_ with
             element = infer_named_record scope env (TRecord fields);
             storage = infer_named_record scope env container;
           })
  | ty -> infer_named_record scope env ty

let rec collapse_static_record_protocols env ty =
  match ty with
  | TConstraint (Protocol_constraint { guarded = true; value = value_ty; _ }) ->
      Types.protocol_constraint_with_value ty
        (collapse_static_record_protocols env value_ty)
  | _ -> (
  match Types.protocol_constraint_info ty with
  | Some (protocol_id, _, value_ty) ->
      let value_ty = collapse_static_record_protocols env value_ty in
      (match value_ty with
      | TNamed_record _ when Protocol.type_satisfies env protocol_id value_ty ->
          value_ty
      | _ -> Types.protocol_constraint_with_value ty value_ty)
  | None -> (
      match ty with
      | TVector element_ty ->
          TVector (collapse_static_record_protocols env element_ty)
      | TRecord fields ->
          TRecord
            (List.map
               (fun (field : field) ->
                 {
                   field with
                   ty = collapse_static_record_protocols env field.ty;
                 })
               fields)
      | ty -> ty))

let rec protocol_witness_constraint_type receiver_ty = function
  | TUnknown | TMeta _ -> TOcaml "_"
  | TVar _ as ty -> ty
  | TNullable ty -> TNullable (protocol_witness_constraint_type receiver_ty ty)
  | TOcaml_app (name, arguments) ->
      TOcaml_app
        (name, List.map (protocol_witness_constraint_type receiver_ty) arguments)
  | TTuple items ->
      TTuple (List.map (protocol_witness_constraint_type receiver_ty) items)
  | TArray ty -> TArray (protocol_witness_constraint_type receiver_ty ty)
  | TRef ty -> TRef (protocol_witness_constraint_type receiver_ty ty)
  | TList ty -> TList (protocol_witness_constraint_type receiver_ty ty)
  | TVector ty -> TVector (protocol_witness_constraint_type receiver_ty ty)
  | TSet ty -> TSet (protocol_witness_constraint_type receiver_ty ty)
  | TSeq ty -> TSeq (protocol_witness_constraint_type receiver_ty ty)
  | TFn (parameters, return_type) ->
      let parameters =
        match parameters with
        | _receiver :: rest ->
            pattern_constraint_type (Types.constraint_value_type receiver_ty)
            :: List.map (protocol_witness_constraint_type receiver_ty) rest
        | [] -> []
      in
      TFn
        (parameters, protocol_witness_constraint_type receiver_ty return_type)
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             let fixed_params =
               match arity.fixed_params with
               | _receiver :: rest ->
                   pattern_constraint_type
                     (Types.constraint_value_type receiver_ty)
                   :: List.map
                        (protocol_witness_constraint_type receiver_ty)
                        rest
               | [] -> []
             in
             {
               fixed_params;
               rest_param =
                 Option.map
                   (protocol_witness_constraint_type receiver_ty)
                   arity.rest_param;
               return_ty =
                 protocol_witness_constraint_type receiver_ty arity.return_ty;
             })
           arities)
  | ty -> ty

and pattern_constraint_type = function
  | TUnknown | TMeta _ | TVar _ -> TOcaml "_"
  | TNullable ty -> TNullable (pattern_constraint_type ty)
  | TConstraint
      (Protocol_constraint ({ witness = witness_ty; value = value_ty; _ } as
       constraint_)) ->
      TConstraint
        (Protocol_constraint
           {
             constraint_ with
             witness = protocol_witness_constraint_type value_ty witness_ty;
             value = pattern_constraint_type value_ty;
           })
  | TConstraint constraint_ ->
      TConstraint (map_constraint pattern_constraint_type constraint_)
  | TOcaml_app (name, arguments) ->
      TOcaml_app (name, List.map pattern_constraint_type arguments)
  | TTuple items -> TTuple (List.map pattern_constraint_type items)
  | TArray ty ->
      TArray (pattern_constraint_type (Types.constraint_value_type ty))
  | TRef ty -> TRef (pattern_constraint_type ty)
  | TList ty -> TList (pattern_constraint_type ty)
  | TVector ty -> TVector (pattern_constraint_type ty)
  | TSet ty -> TSet (pattern_constraint_type ty)
  | TSeq ty -> TSeq (pattern_constraint_type ty)
  | TRecord fields as ty ->
      if Types.is_homogeneous_record fields then ty else TOcaml "_"
  | TFn (parameters, return_type) ->
      TFn
        ( List.map pattern_constraint_type parameters,
          pattern_constraint_type return_type )
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             {
               fixed_params =
                 List.map pattern_constraint_type arity.fixed_params;
               rest_param = Option.map pattern_constraint_type arity.rest_param;
               return_ty = pattern_constraint_type arity.return_ty;
             })
           arities)
  | TNamed_record record ->
      TNamed_record
        {
          record with
          type_arguments =
            List.map pattern_constraint_type record.type_arguments;
          fields =
            List.map
              (fun (field : field) ->
                { field with ty = pattern_constraint_type field.ty })
              record.fields;
        }
  | ty -> ty

let array_storage_type = function
  | TArray element_ty -> TArray (Types.constraint_value_type element_ty)
  | ty -> ty

let rec contains_open_type = function
  | TPoly_variant row -> List.exists contains_open_type (List.filter_map snd row.tags)
  | TUnknown | TMeta _ | TVar _ -> true
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      contains_open_type ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists contains_open_type arguments
  | TConstraint constraint_ ->
      List.exists contains_open_type (constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.exists contains_open_type parameters || contains_open_type return_ty
  | TOverloaded_fn arities ->
      List.exists
        (fun arity ->
          List.exists contains_open_type arity.fixed_params
          || (match arity.rest_param with
             | Some ty -> contains_open_type ty
             | None -> false)
          || contains_open_type arity.return_ty)
        arities
  | TRecord fields ->
      List.exists (fun (field : field) -> contains_open_type field.ty) fields
  | TNamed_record record ->
      List.exists contains_open_type record.type_arguments
      || List.exists
           (fun (field : field) -> contains_open_type field.ty)
           record.fields
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TOcaml _ ->
      false

let rec contains_structural_record = function
  | TPoly_variant row -> List.exists contains_structural_record (List.filter_map snd row.tags)
  | TRecord _ -> true
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      contains_structural_record ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists contains_structural_record arguments
  | TConstraint constraint_ ->
      List.exists contains_structural_record (constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.exists contains_structural_record parameters
      || contains_structural_record return_ty
  | TOverloaded_fn arities ->
      List.exists
        (fun arity ->
          List.exists contains_structural_record arity.fixed_params
          || Option.fold ~none:false ~some:contains_structural_record
               arity.rest_param
          || contains_structural_record arity.return_ty)
        arities
  | TNamed_record _ | TInt | TFloat | TChar | TString | TRegex | TMap_keys
  | TSymbol | TKeyword | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _ ->
      false

let shared_parameter_variables inferred =
  inferred
  |> List.fold_left
       (fun counts (_name, ty) ->
         Type_solver.variables ty
         |> List.fold_left
              (fun counts variable ->
                let count = List.assoc_opt variable counts |> Option.value ~default:0 in
                (variable, count + 1) :: List.remove_assoc variable counts)
              counts)
       []
  |> List.filter_map (fun (variable, count) ->
         if count > 1 then Some variable else None)

let reconcile_shared_parameter_variables original resolved =
  let shared = shared_parameter_variables original in
  let substitutions =
    List.fold_left2
      (fun substitutions (_name, template) (_name, actual) ->
        match Type_solver.unify substitutions template actual with
        | Ok substitutions -> substitutions
        | Error _ -> substitutions)
      Type_solver.empty original resolved
    |> Type_solver.filter (fun variable _ty -> List.mem variable shared)
  in
  List.map
    (fun (name, ty) -> (name, Type_solver.apply substitutions ty))
    resolved

let rec apply_row_constraint_type row_type_name = function
  | TRecord _ -> TOcaml (Types.ocaml_record_type_name row_type_name)
  | TNamed_record { nominal = false; _ } ->
      TOcaml (Types.ocaml_record_type_name row_type_name)
  | TConstraint
      (Seqable_constraint ({ element = TRecord _; _ } as constraint_)) ->
      TConstraint
        (Seqable_constraint
           {
             constraint_ with
             element = TOcaml (Types.ocaml_record_type_name row_type_name);
           })
  | TNullable ty -> TNullable (apply_row_constraint_type row_type_name ty)
  | TOcaml_app (name, arguments) ->
      TOcaml_app
        (name, List.map (apply_row_constraint_type row_type_name) arguments)
  | TTuple items ->
      TTuple (List.map (apply_row_constraint_type row_type_name) items)
  | TArray ty -> TArray (apply_row_constraint_type row_type_name ty)
  | TRef ty -> TRef (apply_row_constraint_type row_type_name ty)
  | TList ty -> TList (apply_row_constraint_type row_type_name ty)
  | TVector ty -> TVector (apply_row_constraint_type row_type_name ty)
  | TSet ty -> TSet (apply_row_constraint_type row_type_name ty)
  | TSeq ty -> TSeq (apply_row_constraint_type row_type_name ty)
  | TFn (parameters, return_type) ->
      TFn
        ( List.map (apply_row_constraint_type row_type_name) parameters,
          apply_row_constraint_type row_type_name return_type )
  | ty -> ty

let rec replace_post_result result_name = function
  | Ast.FSymbol "%" -> Ast.FSymbol result_name
  | Ast.FList forms ->
      Ast.FList (List.map (replace_post_result result_name) forms)
  | Ast.FVector forms ->
      Ast.FVector (List.map (replace_post_result result_name) forms)
  | Ast.FMap pairs ->
      Ast.FMap
        (List.map
           (fun (key, value) ->
             ( replace_post_result result_name key,
               replace_post_result result_name value ))
           pairs)
  | form -> form

let normalize_prepost_body = function
  | Ast.FMap pairs :: body_forms as original ->
      let clauses keyword =
        pairs
        |> List.find_map (function
             | Ast.FKeyword key, Ast.FVector forms when key = keyword ->
                 Some forms
             | _ -> None)
      in
      let pre = clauses ":pre" in
      let post = clauses ":post" in
      if Option.is_none pre && Option.is_none post then original
      else
        let assertions forms =
          List.map
            (fun form -> Ast.FList [ Ast.FSymbol "assert"; form ])
            forms
        in
        let pre = Option.value pre ~default:[] |> assertions in
        let post = Option.value post ~default:[] in
        if post = [] then pre @ body_forms
        else
          let result_name = "__lg_post_result" in
          let result =
            match body_forms with
            | [] -> Ast.FSymbol "nil"
            | [ form ] -> form
            | forms -> Ast.FList (Ast.FSymbol "do" :: forms)
          in
          let post =
            post
            |> List.map (replace_post_result result_name)
            |> assertions
          in
          pre
          @ [
              Ast.FList
                [
                  Ast.FSymbol "let";
                  Ast.FVector [ Ast.FSymbol result_name; result ];
                  Ast.FList
                    (Ast.FSymbol "do" :: post
                   @ [ Ast.FSymbol result_name ]);
                ];
            ]
  | body_forms -> body_forms

let returned_parameter_index scope env parameter_names body_forms =
  let parameter_index name =
    parameter_names
    |> List.mapi (fun index parameter -> (index, parameter))
    |> List.find_opt (fun (_, parameter) -> String.equal name parameter)
    |> Option.map fst
  in
  let merge_optional_index left right =
    match (left, right) with
    | Some left, Some right when left = right -> Some left
    | Some index, None | None, Some index -> Some index
    | Some _, Some _ | None, None -> None
  in
  let rec returned_parameter = function
    | Ast.FSymbol name -> parameter_index name
    | Ast.FList (Ast.FSymbol ("let" | "let*") :: _bindings :: forms) -> (
        match List.rev forms with
        | form :: _ -> returned_parameter form
        | [] -> None)
    | Ast.FList (Ast.FSymbol "try" :: forms) ->
        let rec collect body catches = function
          | Ast.FList (Ast.FSymbol "catch" :: _pattern :: catch_forms) :: rest ->
              let catch_return =
                match List.rev catch_forms with
                | form :: _ -> returned_parameter form
                | [] -> None
              in
              collect body (merge_optional_index catches catch_return) rest
          | Ast.FList (Ast.FSymbol "finally" :: _) :: rest ->
              collect body catches rest
          | form :: rest -> collect (Some form) catches rest
          | [] ->
              let body_return = Option.bind body returned_parameter in
              merge_optional_index body_return catches
        in
        collect None None forms
    | Ast.FList [ Ast.FSymbol "if"; _condition; then_form; else_form ] -> (
        match (returned_parameter then_form, returned_parameter else_form) with
        | Some left, Some right when left = right -> Some left
        | _ -> None)
    | Ast.FList
        [
          Ast.FSymbol ("__lg_if-some" | "__lg_if-let" | "if-some" | "if-let");
          Ast.FVector [ _binding; _option_form ];
          then_form;
          else_form;
        ] -> (
        match (returned_parameter then_form, returned_parameter else_form) with
        | Some left, Some right when left = right -> Some left
        | _ -> None)
    | Ast.FList
        (Ast.FSymbol ("__lg_assoc" | "assoc") :: target :: _pairs) ->
        returned_parameter target
    | Ast.FList [ Ast.FSymbol "Ok"; value ] ->
        returned_parameter value
    | Ast.FList (Ast.FSymbol "do" :: forms) -> (
        match List.rev forms with
        | form :: _ -> returned_parameter form
        | [] -> None)
    | Ast.FList [ Ast.FSymbol ("__lg_with-meta" | "with-meta"); value; _metadata ] ->
        returned_parameter value
    | Ast.FList (Ast.FSymbol method_name :: arguments) -> (
        match Protocol.lookup_marker scope env method_name with
        | Some { protocol_id = Some protocol_id; _ } -> (
            match
              Protocol.common_method_return_param_index env protocol_id
                (Protocol.method_basename method_name)
            with
            | Some argument_index -> (
                match List.nth_opt arguments argument_index with
                | Some argument -> returned_parameter argument
                | None -> None)
            | None -> None)
        | Some _ | None -> None)
    | Ast.FCoreSymbol _ | Ast.FKeyword _ | Ast.FString _ | Ast.FRegex _
    | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _
    | Ast.FVector _
    | Ast.FMap _ | Ast.FList _ ->
        None
  in
  let rec result_ok_returned_parameter = function
    | Ast.FList [ Ast.FSymbol "Ok"; value ] -> returned_parameter value
    | Ast.FList [ Ast.FSymbol "Error"; _ ] -> None
    | Ast.FList (Ast.FSymbol ("let" | "let*") :: _bindings :: forms) -> (
        match List.rev forms with
        | form :: _ -> result_ok_returned_parameter form
        | [] -> None)
    | Ast.FList [ Ast.FSymbol "if"; _condition; then_form; else_form ] ->
        merge_optional_index (result_ok_returned_parameter then_form)
          (result_ok_returned_parameter else_form)
    | Ast.FList
        [
          Ast.FSymbol ("__lg_if-some" | "__lg_if-let" | "if-some" | "if-let");
          Ast.FVector [ _binding; _option_form ];
          then_form;
          else_form;
        ] ->
        merge_optional_index (result_ok_returned_parameter then_form)
          (result_ok_returned_parameter else_form)
    | Ast.FList (Ast.FSymbol "do" :: forms) -> (
        match List.rev forms with
        | form :: _ -> result_ok_returned_parameter form
        | [] -> None)
    | Ast.FList [ Ast.FSymbol ("__lg_with-meta" | "with-meta"); value; _metadata ] ->
        result_ok_returned_parameter value
    | Ast.FSymbol _ | Ast.FCoreSymbol _ | Ast.FKeyword _ | Ast.FString _ | Ast.FRegex _
    | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _
    | Ast.FVector _ | Ast.FMap _ | Ast.FList _ ->
        None
  in
  match List.rev body_forms with
  | form :: _ -> (
      match returned_parameter form with
      | Some _ as index -> index
      | None -> result_ok_returned_parameter form)
  | [] -> None

let lexical_parameter_names specs =
  specs
  |> List.concat_map (fun (spec : Destructure.param_spec) ->
         spec.source_name :: Destructure.pattern_names spec.pattern)
  |> List.sort_uniq String.compare

let prepare ?(param_type_overrides = []) ?(additional_inference_params = [])
    ?refine_inferred_env ?preferred_record ?variadic_rest_index
    ?(materialize_open_equality = false) ?(refine_open_overrides = false)
    ?compile_function_body ?compile_default
    ~lookup_function_ty ~compile_body scope env params body_forms =
  match Destructure.parse_param_specs params with
  | Error _ as err -> err
  | Ok specs ->
      let normalize_variadic_rest_type ty =
        match ty with
        | TSeq _ -> ty
        | TMeta _ -> TSeq ty
        | TUnknown -> TSeq (Type_solver.fresh ())
        | ty -> TSeq ty
      in
      let parameter_names = lexical_parameter_names specs in
      let macro_env = Env.add_core_exclusions ~scope parameter_names env in
      Result.bind
        (Macro_expander.expand_all_forms ~scope ~compiler_env:macro_env body_forms)
        (fun body_forms ->
          let body_forms = normalize_prepost_body body_forms in
      let inference_params =
        specs
        |> List.mapi (fun index (spec : Destructure.param_spec) ->
            let param_ty =
              match spec.explicit_ty with
              | Some ty when not (Types.equal ty TUnknown) ->
                  let explicit_ty = infer_named_record scope env ty in
                  (match List.nth_opt param_type_overrides index with
                  | Some (Some override_ty) -> (
                      let override_ty = infer_named_record scope env override_ty in
                      match (explicit_ty, override_ty) with
                      | TNamed_record explicit, TNamed_record override
                        when Type_id.equal explicit.type_id override.type_id ->
                          override_ty
                      | _ -> explicit_ty)
                  | Some None | None -> explicit_ty)
              | _ -> (
                  match List.nth_opt param_type_overrides index with
                  | Some (Some ty) when not (Types.equal ty TUnknown) -> ty
                  | _ -> Type_solver.fresh ())
            in
            let param_ty =
              if Some index = variadic_rest_index then
                normalize_variadic_rest_type param_ty
              else param_ty
            in
               let destructured =
                 if spec.destructured then
                   let hints =
                     Destructure.pattern_type_hints spec.pattern param_ty
                   in
                   Destructure.pattern_names spec.pattern
                   |> List.map (fun name ->
                          ( name,
                            List.assoc_opt name hints
                            |> Option.value ~default:(Type_solver.fresh ()) ))
                 else []
               in
               (spec.source_name, param_ty) :: destructured)
        |> List.concat
        |> fun params ->
        params
        @ List.filter
            (fun (name, _) -> not (List.mem_assoc name params))
            additional_inference_params
      in
      let lookup_protocol_constraint = Protocol.constraint_type scope env in
      let lookup_dynamic_key_record_type =
        Expression_support.dynamic_key_record_type env
      in
      let resolve_named_record = infer_named_record scope env in
      let lookup_closed_sum_candidates payload_types =
        Env.closed_sum_candidates_for_payloads payload_types env
      in
      let lookup_closed_sum_constructors ty =
        Env.predicate_variant_constructors ty env
      in
      let lookup_successful_call_refinement name =
        match Resolver.lookup_binding scope env name with
        | Ok (binding : Types.binding) ->
            Env.find_successful_call_refinement binding.ocaml_name env
        | Error _ -> None
      in
      let lookup_function_ty name =
        Result.map resolve_named_record (lookup_function_ty name)
      in
      let infer_parameters parameters =
        Type_inference.infer_params ~materialize_open_equality
          ~lookup_call_ty:(Expression_support.lookup_call_ty scope env)
          ~expand_form:(Macro_expander.expand_all ~scope ~compiler_env:env)
          ~lookup_function_ty
          ~lookup_closed_sum_candidates
          ~lookup_closed_sum_constructors
          ~lookup_successful_call_refinement
          ~lookup_protocol_constraint ~lookup_dynamic_key_record_type
          ~lookup_key_record_type:
            (Expression_support.record_type_for_keyword ~scope env)
          ~resolve_named_record
          parameters body_forms
      in
      match infer_parameters inference_params with
      | Error _ as err -> err
      | Ok inferred -> (
          let env =
            match refine_inferred_env with
            | Some refine -> refine inferred env
            | None -> env
          in
          let rec matches_parameter_as_option name = function
            | Ast.FList
                (Ast.FSymbol "match" :: Ast.FSymbol target :: clauses)
              when String.equal name target ->
                List.exists
                  (function
                    | Ast.FList (Ast.FSymbol "Some" :: _)
                    | Ast.FSymbol "None" ->
                        true
                    | _ -> false)
                  clauses
            | Ast.FList (Ast.FSymbol "fn" :: _) -> false
            | Ast.FList forms | Ast.FVector forms ->
                List.exists (matches_parameter_as_option name) forms
            | Ast.FMap pairs ->
                List.exists
                  (fun (key, value) ->
                    matches_parameter_as_option name key
                    || matches_parameter_as_option name value)
                  pairs
            | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _
            | Ast.FString _
            | Ast.FRegex _ | Ast.FBool _ | Ast.FKeyword _ | Ast.FSymbol _
            | Ast.FCoreSymbol _ ->
                false
          in
          let option_matched_parameters =
            specs
            |> List.filter_map (fun (spec : Destructure.param_spec) ->
                   if
                     List.exists
                       (matches_parameter_as_option spec.source_name)
                       body_forms
                   then Some spec.source_name
                   else None)
          in
          let destructured_sources =
            specs
            |> List.filter_map (fun (spec : Destructure.param_spec) ->
                   if spec.destructured then Some spec.source_name else None)
          in
          let field_access_target_name = function
            | Ast.FSymbol name -> Some name
            | Ast.FList
                [
                  Ast.FSymbol "__type-hint";
                  Ast.FSymbol _;
                  Ast.FSymbol name;
                ] ->
                Some name
            | _ -> None
          in
          let rec hinted_field_access_parameters = function
            | Ast.FList
                [
                  Ast.FSymbol field_access;
                  Ast.FList
                    [
                      Ast.FSymbol "__type-hint";
                      Ast.FSymbol _;
                      Ast.FSymbol target;
                    ];
                ]
              when String.starts_with ~prefix:".-" field_access ->
                [ target ]
            | Ast.FList forms | Ast.FVector forms ->
                List.concat_map hinted_field_access_parameters forms
            | Ast.FMap pairs ->
                List.concat_map
                  (fun (key, value) ->
                    hinted_field_access_parameters key
                    @ hinted_field_access_parameters value)
                  pairs
            | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _
            | Ast.FString _
            | Ast.FRegex _ | Ast.FBool _ | Ast.FKeyword _ | Ast.FSymbol _
            | Ast.FCoreSymbol _ ->
                []
          in
          let hinted_field_access_parameters =
            body_forms
            |> List.concat_map hinted_field_access_parameters
            |> List.sort_uniq String.compare
          in
          let non_structural_record_like = function
            | TRecord _ -> false
            | ty -> Option.is_some (Types.record_fields ty)
          in
          let preserves_record_identity ~current ~expected =
            non_structural_record_like current
            && Option.is_some (Types.record_fields expected)
          in
          let rec pattern_bound_names = function
            | Ast.FSymbol name ->
                if String.equal name "_" then [] else [ name ]
            | Ast.FList
                [
                  Ast.FSymbol "__type-hint";
                  Ast.FSymbol _;
                  pattern;
                ] ->
                pattern_bound_names pattern
            | Ast.FVector forms ->
                List.concat_map pattern_bound_names forms
            | Ast.FMap _ as pattern -> Destructure.pattern_names pattern
            | Ast.FList (Ast.FSymbol _constructor :: payload_patterns) ->
                List.concat_map pattern_bound_names payload_patterns
            | _ -> []
          in
          let rec directly_accesses_field parameter = function
            | Ast.FList
                [ Ast.FSymbol field_access; target ]
              when String.starts_with ~prefix:".-" field_access
                   && Option.equal String.equal
                        (field_access_target_name target)
                        (Some parameter) ->
                true
            | Ast.FList forms | Ast.FVector forms ->
                List.exists (directly_accesses_field parameter) forms
            | Ast.FMap pairs ->
                List.exists
                  (fun (key, value) ->
                    directly_accesses_field parameter key
                    || directly_accesses_field parameter value)
                  pairs
            | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _
            | Ast.FString _
            | Ast.FRegex _ | Ast.FBool _ | Ast.FKeyword _ | Ast.FSymbol _
            | Ast.FCoreSymbol _ ->
                false
          in
          let directly_accessed_parameters =
            specs
            |> List.filter_map (fun (spec : Destructure.param_spec) ->
                   if
                     List.exists
                       (directly_accesses_field spec.source_name)
                       body_forms
                   then Some spec.source_name
                   else None)
          in
          let source_name_matches name expected =
            String.equal name expected
            || String.equal (Names.sanitize_name name)
                 (Names.sanitize_name expected)
            ||
            match String.rindex_opt name '/' with
            | Some index ->
                let local =
                  String.sub name (index + 1)
                    (String.length name - index - 1)
                in
                String.equal local expected
                || String.equal (Names.sanitize_name local)
                     (Names.sanitize_name expected)
            | None -> false
          in
          let rec condition_uses_parameter parameter = function
            | Ast.FList (Ast.FSymbol operator :: Ast.FSymbol condition :: _)
              when (source_name_matches operator "if"
                   || source_name_matches operator "when")
                   && String.equal condition parameter ->
                true
            | Ast.FList (Ast.FSymbol "fn" :: _) -> false
            | Ast.FList forms | Ast.FVector forms ->
                List.exists (condition_uses_parameter parameter) forms
            | Ast.FMap pairs ->
                List.exists
                  (fun (key, value) ->
                    condition_uses_parameter parameter key
                    || condition_uses_parameter parameter value)
                  pairs
            | Ast.FInt _ | Ast.FFloat _ | Ast.FDecimal _ | Ast.FChar _
            | Ast.FString _
            | Ast.FRegex _ | Ast.FBool _ | Ast.FKeyword _ | Ast.FSymbol _
            | Ast.FCoreSymbol _ ->
                false
          in
          let condition_parameters =
            specs
            |> List.filter_map (fun (spec : Destructure.param_spec) ->
                   if
                     List.exists
                       (condition_uses_parameter spec.source_name)
                       body_forms
                   then Some spec.source_name
                   else None)
          in
          let infer_structural_fields fields =
            TRecord
              (List.map
                 (fun (field : field) ->
                   {
                     field with
                     ty = infer_named_record scope env field.ty;
                   })
                 fields)
          in
          let infer_parameter_type name ty =
            if List.mem name destructured_sources then
              match ty with
              | TRecord fields -> infer_structural_fields fields
              | TNullable (TRecord fields) ->
                  TNullable (infer_structural_fields fields)
              | TOcaml_app ("option", [ TRecord fields ]) ->
                  TOcaml_app ("option", [ infer_structural_fields fields ])
              | ty -> infer_named_record scope env ty
            else
              match ty with
              | ty
                when List.mem name condition_parameters
                     && Option.is_some (Types.record_fields ty)
                     &&
                     (match ty with
                     | TNullable _ | TOcaml_app ("option", [ _ ]) -> false
                     | _ -> true) ->
                  TNullable (infer_named_record ?preferred_record scope env ty)
              | ty
                when List.mem name hinted_field_access_parameters
                     && non_structural_record_like ty ->
                  ty
              | TNullable (TRecord fields) ->
                  let structural = infer_structural_fields fields in
                  if List.mem name directly_accessed_parameters then
                    TNullable
                      (infer_named_record ?preferred_record scope env structural)
                  else TNullable structural
              | TOcaml_app ("option", [ TRecord fields ]) ->
                  let structural = infer_structural_fields fields in
                  if List.mem name directly_accessed_parameters then
                    TOcaml_app
                      ( "option",
                        [ infer_named_record ?preferred_record scope env structural ] )
                  else TOcaml_app ("option", [ structural ])
              | ty -> infer_named_record ?preferred_record scope env ty
          in
          let resolved_inferred =
            List.map
              (fun (name, ty) -> (name, infer_parameter_type name ty))
              inferred
          in
          let resolved_records =
            List.exists2
              (fun (_, before) (_, after) ->
                Type_solver.is_open before && not (Type_solver.is_open after))
              inferred resolved_inferred
          in
          let inferred =
            reconcile_shared_parameter_variables inferred resolved_inferred
          in
          let expected_parameter_types_from_body parameter_names inferred =
              let parameter_name name =
                List.exists
                  (fun parameter ->
                    String.equal name parameter
                    || String.equal name (Names.sanitize_name parameter))
                  parameter_names
              in
              let canonical_parameter_name name =
                List.find_opt
                  (fun parameter ->
                    String.equal name parameter
                    || String.equal name (Names.sanitize_name parameter))
                  parameter_names
                |> Option.value ~default:name
              in
              let arity_params argument_count (arity : fn_arity) =
                let fixed_count = List.length arity.fixed_params in
                if argument_count < fixed_count then None
                else
                  match arity.rest_param with
                  | None when argument_count = fixed_count ->
                      Some arity.fixed_params
                  | Some rest_ty ->
                      Some
                        (arity.fixed_params
                        @ List.init (argument_count - fixed_count) (fun _ ->
                              rest_ty))
                  | None -> None
              in
              let rec contains_record_shape ty =
                Option.is_some (Types.record_fields ty)
                ||
                match ty with
                | TNullable inner | TArray inner | TRef inner | TList inner
                | TVector inner | TSet inner | TSeq inner
                | TOcaml_app (_, [ inner ]) ->
                    contains_record_shape inner
                | TOcaml_app (_, arguments) | TTuple arguments ->
                    List.exists contains_record_shape arguments
                | TFn (parameters, return_ty) ->
                    List.exists contains_record_shape (return_ty :: parameters)
                | TOverloaded_fn arities ->
                    List.exists
                      (fun arity ->
                        List.exists contains_record_shape
                          (arity.return_ty :: arity.fixed_params)
                        || Option.fold ~none:false ~some:contains_record_shape
                             arity.rest_param)
                      arities
                | TConstraint constraint_ ->
                    List.exists contains_record_shape
                      (constraint_children constraint_)
                | TPoly_variant row ->
                    List.exists contains_record_shape
                      (List.filter_map snd row.tags)
                | TRecord _ | TNamed_record _ -> true
                | TInt | TFloat | TChar | TString | TRegex | TMap_keys
                | TSymbol | TKeyword | TBool | TUnit | TNil | TUnknown
                | TMeta _ | TVar _ | TOcaml _ ->
                    false
              in
              let add_expected acc parameter expected =
                let expected = infer_named_record scope env expected in
                if not (contains_record_shape expected) then acc
                else begin
                  let current =
                    List.assoc_opt parameter acc |> Option.value ~default:TUnknown
                  in
                  (parameter, Type_inference.refine_type current expected)
                  :: List.remove_assoc parameter acc
                end
              in
              let add_call locals acc name args =
                let parameter_tys =
                  match lookup_function_ty name with
                  | Ok (TFn (parameter_tys, _))
                    when List.length parameter_tys = List.length args ->
                      Some parameter_tys
                  | Ok (TOverloaded_fn arities) ->
                      arities
                      |> List.find_map (arity_params (List.length args))
                  | Ok _ | Error _ -> None
                in
                match parameter_tys with
                | None -> acc
                | Some parameter_tys ->
                    List.fold_left2
                      (fun acc expected -> function
                        | Ast.FSymbol argument
                          when parameter_name argument
                               && not (List.mem_assoc argument locals) ->
                            add_expected acc
                              (canonical_parameter_name argument)
                              expected
                        | _ -> acc)
                      acc parameter_tys args
              in
              let option_payload = function
                | TNullable payload | TOcaml_app ("option", [ payload ]) ->
                    payload
                | _ -> TUnknown
              in
              let symbol_has_source_name name expected =
                String.equal name expected
                || String.equal (Names.sanitize_name name)
                     (Names.sanitize_name expected)
                ||
                match String.rindex_opt name '/' with
                | Some index ->
                    let local =
                      String.sub name (index + 1)
                        (String.length name - index - 1)
                    in
                    String.equal local expected
                    || String.equal (Names.sanitize_name local)
                         (Names.sanitize_name expected)
                | None -> false
              in
              let function_binding_type name =
                match lookup_function_ty name with
                | Ok ty -> ty
                | Error _ -> TUnknown
              in
              let form_type locals form =
                let params =
                  locals @ inferred
                in
                let direct_call_return =
                  match form with
                  | Ast.FList (Ast.FSymbol name :: args) -> (
                      match lookup_function_ty name with
                      | Ok (TFn (parameter_tys, return_ty))
                        when List.length parameter_tys = List.length args ->
                          Some return_ty
                      | Ok (TOverloaded_fn arities) ->
                          arities
                          |> List.find_map (fun arity ->
                                 Option.map
                                   (fun _ -> arity.return_ty)
                                   (arity_params (List.length args) arity))
                      | Ok _ | Error _ -> None)
                  | _ -> None
                in
                match direct_call_return with
                | Some ty -> ty
                | None -> (
                    match
                      Type_inference.inferred_form_type
                        ~lookup_binding:function_binding_type params form
                    with
                    | TUnknown | TMeta _ | TVar _ ->
                        Type_inference.inferred_call_return_type
                          ~lookup_function_ty params form
                    | ty -> ty)
              in
              let rec bind_pattern locals pattern ty =
                match pattern with
                | Ast.FSymbol name when not (String.equal name "_") ->
                    (name, ty) :: List.remove_assoc name locals
                | Ast.FList [ Ast.FSymbol some_name; Ast.FSymbol name ]
                  when (symbol_has_source_name some_name "Some"
                       || symbol_has_source_name some_name "__lg_some")
                       && not (String.equal name "_") ->
                    (name, option_payload ty) :: List.remove_assoc name locals
                | Ast.FList (Ast.FSymbol tuple_name :: patterns)
                  when symbol_has_source_name tuple_name "tuple"
                       || symbol_has_source_name tuple_name "__lg_tuple" -> (
                    match ty with
                    | TTuple tys when List.length patterns = List.length tys ->
                        List.fold_left2 bind_pattern locals patterns tys
                    | _ -> locals)
                | pattern ->
                    pattern_bound_names pattern
                    |> List.fold_left
                         (fun locals name ->
                           if String.equal name "_" then locals
                           else (name, TUnknown) :: List.remove_assoc name locals)
                         locals
              in
              let add_parameter_call locals acc name args =
                if parameter_name name && not (List.mem_assoc name locals) then
                  let argument_tys =
                    List.map (fun arg -> form_type locals arg) args
                  in
                  add_expected acc
                    (canonical_parameter_name name)
                    (TFn (argument_tys, TUnknown))
                else acc
              in
              let rec visit locals acc = function
                | Ast.FList (Ast.FSymbol ("fn" | "fn*") :: _) -> acc
                | Ast.FList (Ast.FSymbol match_name :: scrutinee :: branches)
                  when symbol_has_source_name match_name "match"
                       || symbol_has_source_name match_name "__lg_match" ->
                    let acc = visit locals acc scrutinee in
                    let rec visit_branches acc = function
                      | pattern :: branch :: rest ->
                          let branch_locals =
                            bind_pattern locals pattern (form_type locals scrutinee)
                          in
                          visit_branches (visit branch_locals acc branch) rest
                      | [ pattern ] -> visit locals acc pattern
                      | [] -> acc
                    in
                    visit_branches acc branches
                | Ast.FList
                    (Ast.FSymbol let_name :: Ast.FVector bindings :: body_forms)
                  when symbol_has_source_name let_name "let"
                       || symbol_has_source_name let_name "let*" ->
                    let rec bind_pairs locals acc = function
                      | pattern :: value :: rest ->
                          let acc = visit locals acc value in
                          let value_ty = form_type locals value in
                          bind_pairs (bind_pattern locals pattern value_ty) acc rest
                      | [] -> (locals, acc)
                      | [ dangling ] -> (locals, visit locals acc dangling)
                    in
                    let body_locals, acc = bind_pairs locals acc bindings in
                    List.fold_left (visit body_locals) acc body_forms
                | Ast.FList (Ast.FSymbol name :: args as forms) ->
                    let acc = add_call locals acc name args in
                    let acc = add_parameter_call locals acc name args in
                    List.fold_left (visit locals) acc forms
                | Ast.FList forms | Ast.FVector forms ->
                    List.fold_left (visit locals) acc forms
                | Ast.FMap pairs ->
                    List.fold_left
                      (fun acc (key, value) ->
                        visit locals (visit locals acc key) value)
                      acc pairs
                | Ast.FSymbol _ | Ast.FCoreSymbol _ | Ast.FKeyword _
                | Ast.FString _ | Ast.FRegex _ | Ast.FInt _ | Ast.FFloat _
                | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _ ->
                    acc
              in
              List.fold_left (visit [])
                (List.map (fun name -> (name, TUnknown)) parameter_names)
                body_forms
              |> List.map (fun (name, expected) ->
                     let current =
                       List.assoc_opt name inferred
                       |> Option.value ~default:TUnknown
                     in
                     let refined =
                       match
                         ( Types.protocol_constraint_info current,
                           current,
                           expected )
                       with
                       | ( Some (_, _, value_ty),
                           _,
                           _ )
                         when Option.is_none
                                (Types.protocol_constraint_info expected) ->
                           Types.protocol_constraint_with_value current
                             (Type_inference.refine_type value_ty expected)
                       | None, current, expected
                         when preserves_record_identity ~current ~expected ->
                           current
                       | Some _, _, _ | None, _, _ ->
                           Type_inference.refine_type current expected
                     in
                     (name, refined))
          in
          let inferred =
              let parameter_names =
                specs
                |> List.map (fun (spec : Destructure.param_spec) ->
                       spec.source_name)
              in
              let call_expected =
                expected_parameter_types_from_body parameter_names inferred
              in
              List.map
                (fun (name, ty) ->
                  match List.assoc_opt name call_expected with
                  | Some expected ->
                      let refined =
                        match
                          ( Types.protocol_constraint_info ty,
                            Types.protocol_constraint_info expected )
                        with
                        | Some (_, _, value_ty), None ->
                            Types.protocol_constraint_with_value ty
                              (Type_inference.refine_type value_ty expected)
                        | ( Some (protocol_id, _, value_ty),
                            Some (expected_protocol_id, _, expected_value_ty) )
                          when Protocol_id.equal protocol_id
                                 expected_protocol_id ->
                            Types.protocol_constraint_with_value ty
                              (Type_inference.refine_type value_ty
                                 expected_value_ty)
                        | None, _
                          when preserves_record_identity ~current:ty
                                 ~expected ->
                            ty
                        | Some _, Some _ | None, _ ->
                            Type_inference.refine_type ty expected
                      in
                      (name, refined)
                  | None -> (name, ty))
                inferred
          in
          let ( let* ) = Result.bind in
          let* inferred =
            if refine_open_overrides && resolved_records
            then infer_parameters inferred
            else Ok inferred
          in
          let lookup_inferred name =
            inferred |> List.assoc_opt name |> Option.value ~default:TUnknown
          in
          let rec refine_destructured_type pattern ty =
            let refine_from_local name ty =
              let inferred_ty = lookup_inferred name in
              let refine ty inferred_ty =
                Type_solver.unify Type_solver.empty ty inferred_ty
                |> Result.map (fun substitutions ->
                       Type_solver.apply substitutions ty)
                |> Result.value ~default:ty
              in
              match (ty, inferred_ty) with
              | TNullable payload_ty, (TUnknown | TMeta _ | TVar _) ->
                  TNullable (refine payload_ty inferred_ty)
              | TOcaml_app ("option", [ payload_ty ]), (TUnknown | TMeta _ | TVar _) ->
                  TOcaml_app ("option", [ refine payload_ty inferred_ty ])
              | _ -> refine ty inferred_ty
            in
            match (pattern, ty) with
            | Ast.FSymbol name, ty -> refine_from_local name ty
            | ( Ast.FList
                  [
                    Ast.FSymbol "__type-hint";
                    Ast.FSymbol _;
                    pattern;
                  ],
                ty ) ->
                refine_destructured_type pattern ty
            | Ast.FMap pairs, TRecord fields -> (
                match Destructure.parse_map_pattern pairs with
                | Error _ -> ty
                | Ok parsed ->
                    let fields =
                      List.map
                        (fun (field : field) ->
                          if Types.is_static_record_source_field field then
                            match parsed.as_name with
                            | Some name ->
                                { field with ty = refine_from_local name field.ty }
                            | None -> field
                          else
                            match
                              List.find_opt
                                (fun binding ->
                                  binding.Destructure.keyword = field.keyword)
                                parsed.field_bindings
                            with
                            | None -> field
                            | Some binding ->
                                {
                                  field with
                                  ty =
                                    refine_destructured_type
                                      binding.binding_pattern field.ty;
                                })
                        fields
                    in
                    TRecord fields)
            | _, ty -> ty
          in
          let infer_spec_ty (spec : Destructure.param_spec) =
            if spec.destructured then
              Result.map
                (fun ty ->
                  let ty = infer_named_record scope env ty in
                  refine_destructured_type spec.pattern ty)
                (Destructure.infer_generator_pattern_type spec.pattern lookup_inferred)
            else Ok (lookup_inferred spec.source_name)
          in
          let rec build acc = function
            | [] -> Ok (List.rev acc)
            | spec :: rest -> (
                match infer_spec_ty spec with
                | Error _ as err -> err
                | Ok ty -> build ((spec, ty) :: acc) rest)
          in
          match build [] specs with
          | Error _ as err -> err
          | Ok typed_specs -> (
              let typed_specs =
                typed_specs
                |> List.mapi (fun index ((spec : Destructure.param_spec), inferred_ty) ->
                       let inferred_ty =
                         match inferred_ty with
                         | TMap_keys -> Types.dynamic_constraint TMap_keys
                         | TRecord fields ->
                             TRecord
                               (List.map
                                  (fun (field : field) ->
                                    {
                                      field with
                                      ty = infer_named_record scope env field.ty;
                                    })
                                  fields)
                         | ty -> ty
                       in
                       let inferred_ty =
                         collapse_static_record_protocols env inferred_ty
                       in
                       let inferred_ty =
                         if
                           List.mem spec.source_name
                             hinted_field_access_parameters
                           && non_structural_record_like inferred_ty
                         then inferred_ty
                         else infer_parameter_named_record scope env inferred_ty
                       in
                       let inferred_ty =
                         match inferred_ty with
                         | TNullable inner
                         | TOcaml_app ("option", [ inner ])
                           when Types.is_dynamic inner
                                && not
                                     (List.mem spec.source_name
                                        option_matched_parameters) ->
                             inner
                         | ty -> ty
                       in
                       let inferred_ty =
                         if Some index = variadic_rest_index then
                           normalize_variadic_rest_type inferred_ty
                         else inferred_ty
                       in
                       match spec.Destructure.explicit_ty with
                       | Some ty when not (Types.equal ty TUnknown) ->
                           let explicit_ty = infer_named_record scope env ty in
                           let ty =
                             match (explicit_ty, inferred_ty) with
                             | ( TNamed_record explicit,
                                 TNamed_record inferred )
                               when Type_id.equal explicit.type_id
                                      inferred.type_id ->
                                 inferred_ty
                             | TNamed_record _, inferred
                               when Option.is_some
                                      (Types.protocol_constraint_info inferred)
                               ->
                                 let value_ty =
                                   Type_inference.refine_type explicit_ty
                                     (Types.constraint_value_type inferred)
                                 in
                                 (match
                                    Types.protocol_constraint_info inferred
                                  with
                                 | Some (protocol_id, _, _)
                                   when Protocol.type_satisfies env protocol_id
                                          value_ty ->
                                     value_ty
                                 | Some _ ->
                                     Types.protocol_constraint_with_value
                                       inferred value_ty
                                 | None -> assert false)
                             | ( TFn
                                   ([ TUnknown; TUnknown ], TOcaml "int"),
                                 TFn ([ _; _ ], _) ) ->
                                 Type_inference.refine_type explicit_ty
                                   inferred_ty
                             | _ -> explicit_ty
                           in
                           (spec, ty)
                       | _ -> (
                           match List.nth_opt param_type_overrides index with
                           | Some (Some ty) ->
                               let ty =
                                 match ty with
                                 | TRecord _ -> ty
                                 | _ -> infer_named_record scope env ty
                               in
                               if Types.equal ty TUnknown
                                  || (spec.destructured
                                     && match ty with TMeta _ -> true | _ -> false)
                               then (spec, inferred_ty)
                               else if
                                 List.mem spec.source_name condition_parameters
                                 &&
                                 match inferred_ty with
                                 | TNullable inner
                                 | TOcaml_app ("option", [ inner ]) ->
                                     Types.assignable ~policy:Host_boundary
                                       ~expected:inner ~actual:ty
                                 | _ -> false
                               then (spec, inferred_ty)
                               else if
                                 Types.is_guarded_protocol_constraint inferred_ty
                                 && Option.is_none
                                      (Types.protocol_constraint_info ty)
                               then
                                 let rec storage_type ty =
                                   let value_ty =
                                     Types.constraint_value_type ty
                                   in
                                   if Types.equal value_ty ty then ty
                                   else storage_type value_ty
                                 in
                                 let storage_ty = storage_type inferred_ty in
                                 if
                                   Types.assignable ~policy:Host_boundary
                                     ~expected:ty ~actual:storage_ty
                                 then
                                   ( spec,
                                     Type_inference.refine_type ty storage_ty )
                                 else
                                 let value_ty =
                                   match
                                     Types.protocol_constraint_info inferred_ty
                                   with
                                   | Some (_, _, value_ty) -> value_ty
                                   | None -> assert false
                                 in
                                 ( spec,
                                   Types.protocol_constraint_with_value
                                     inferred_ty
                                     (Type_inference.refine_type value_ty ty) )
                               else if Types.equal ty TMap_keys then
                                 ( spec,
                                   Type_inference.refine_type ty inferred_ty )
                               else if
                                 ((refine_open_overrides
                                  || Option.is_some
                                       (Types.protocol_constraint_info
                                          inferred_ty))
                                 && (contains_open_type ty
                                    || contains_structural_record ty))
                                 || (Option.is_some
                                       (Types.seqable_constraint_info ty)
                                    && match inferred_ty with
                                       | TOcaml_app
                                           ( "Lg_runtime.Runtime_transient.map",
                                             [ _; _ ] ) ->
                                           true
                                       | inferred
                                         when Types.is_dynamic inferred -> (
                                           match
                                             Types.dynamic_constraint_info
                                               inferred
                                           with
                                           | Some
                                               (TOcaml_app
                                                  ( "Lg_runtime.Runtime_transient.map",
                                                    [ _; _ ] )) ->
                                               true
                                           | Some _ | None -> false)
                                       | _ -> false)
                              then
                                let refined =
                                  match (ty, inferred_ty) with
                                  | ( TConstraint
                                        (Seqable_constraint
                                          ({ element = expected_element; _ } as
                                           expected_seqable)),
                                      inferred )
                                    when Option.is_some
                                           (Types.seqable_constraint_info
                                              inferred) ->
                                      let _, inferred_element, _ =
                                        Types.seqable_constraint_info inferred
                                        |> Option.get
                                      in
                                      TConstraint
                                        (Seqable_constraint
                                           {
                                             expected_seqable with
                                             element =
                                               Type_inference.refine_type
                                                 expected_element
                                                 inferred_element;
                                           })
                                  | TNamed_record _, inferred
                                    when Option.is_some
                                           (Types.protocol_constraint_info
                                              inferred) ->
                                      let rec storage_type ty =
                                        let value_ty =
                                          Types.constraint_value_type ty
                                        in
                                        if Types.equal value_ty ty then ty
                                        else storage_type value_ty
                                      in
                                       Type_inference.refine_type ty
                                         (storage_type inferred)
                                   | TNamed_record _, inferred
                                     when Types.is_dynamic inferred ->
                                       ty
                                   | TRecord _, TNamed_record record
                                     when Types.row_compatible ~expected:ty
                                            ~actual:inferred_ty ->
                                       Type_inference.refine_type ty
                                         (TRecord record.fields)
                                   | _ ->
                                       Type_inference.refine_type ty inferred_ty
                                 in
                                 (spec, refined)
                               else
                                 (spec, ty)
                           | None | Some None -> (spec, inferred_ty)))
              in
              let typed_specs =
                List.map
                  (fun (spec, ty) -> (spec, array_storage_type ty))
                  typed_specs
              in
              let param_bindings =
                typed_specs
                |> List.map (fun ((spec : Destructure.param_spec), ty) ->
                       ( Names.scoped_key scope spec.source_name,
                         Types.binding spec.ocaml_name ty ))
              in
              let param_identities =
                typed_specs
                |> List.map (fun ((spec : Destructure.param_spec), _) ->
                       spec.identity)
              in
              let param_targets =
                typed_specs
                |> List.map (fun ((spec : Destructure.param_spec), ty) ->
                       (spec, typed_ir ty (Semantic_ir.Ident spec.ocaml_name)))
              in
              let destructured_bindings =
                let rec loop acc = function
                  | [] -> Ok (List.rev acc)
                  | (spec, target) :: rest -> (
                      if not spec.Destructure.destructured then loop acc rest
                      else
                        match
                          Destructure.bind_pattern ?compile_default ~env target
                            spec.pattern
                        with
                        | Error _ as err -> err
                        | Ok bindings ->
                            loop (List.rev_append bindings acc) rest)
                in
                loop [] param_targets
              in
              match destructured_bindings with
              | Error _ as err -> err
              | Ok destructured_bindings -> (
                  let local_bindings =
                    destructured_bindings
                    |> List.map (fun (binding : Destructure.local_binding) ->
                           ( Names.scoped_key scope binding.source_name,
                             Types.binding binding.ocaml_name binding.ty ))
                  in
                  let env =
                    env
                    |> Env.add_bindings param_bindings
                    |> Env.add_bindings local_bindings
                    |> Env.add_core_exclusions ~scope parameter_names
                  in
                  let body_forms =
                    match body_forms with
                    | [] -> [ Ast.FSymbol "nil" ]
                    | _ -> body_forms
                  in
                  let compiled_body =
                    match compile_function_body with
                    | Some compile ->
                        compile env
                          (List.map (fun (_spec, ty) -> ty) typed_specs)
                          body_forms
                    | None ->
                        compile_body scope
                          (Env.with_source_macros_expanded true env)
                          "function body requires at least one form" body_forms
                  in
                  match compiled_body with
                  | Error _ as err -> err
                  | Ok body ->
                      let return_param_index_hint =
                        returned_parameter_index scope env
                          (List.map
                             (fun ((spec : Destructure.param_spec), _) ->
                               spec.source_name)
                             typed_specs)
                          body_forms
                      in
                      Ok
                        {
                          param_bindings;
                          param_identities;
                          destructured_bindings;
                          return_param_index_hint;
                          body;
                        }))))

let fn_code ?(row_param_type_names = []) parts =
  let param_names =
    parts.param_bindings |> List.map (fun (_key, binding) -> binding.ocaml_name)
  in
  let param_tys =
    parts.param_bindings
    |> List.map (fun (_key, (binding : binding)) -> binding.ty)
    |> List.map array_storage_type
  in
  let sequence_first_arguments =
    match Semantic_ir.unlocated parts.body.semantic_expr with
    | Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_seq.first", arguments) ->
        Some arguments
    | _ -> None
  in
  let param_tys, body_storage_ty, body_semantic_expr =
    match (parts.body.ty, sequence_first_arguments) with
    | TUnknown, Some arguments ->
        let rec tie index reversed = function
          | [] -> None
          | TConstraint
              (Seqable_constraint ({ element = TUnknown; _ } as constraint_))
            :: rest ->
              let element_ty = Type_solver.fresh () in
              Some
                ( List.rev_append reversed
                    (TConstraint
                       (Seqable_constraint
                          { constraint_ with element = element_ty })
                    :: rest),
                  element_ty )
          | ty :: rest -> tie (index + 1) (ty :: reversed) rest
        in
        (match tie 0 [] param_tys with
        | Some (param_tys, element_ty) ->
            let return_ty = TNullable element_ty in
            ( param_tys,
              return_ty,
              Semantic_ir.annotate return_ty
                (Semantic_ir.Apply
                   ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.first_opt",
                     arguments )) )
        | None -> (param_tys, parts.body.ty, parts.body.semantic_expr))
    | return_ty, _ ->
        (param_tys, array_storage_type return_ty, parts.body.semantic_expr)
  in
  let return_ty = body_storage_ty in
  let rec capability_pattern ?value_type name ty =
    match Types.protocol_constraint_info ty with
    | Some (protocol_id, _, value_ty) ->
        Semantic_ir.PTuple
          [
            Semantic_ir.PVar (Types.protocol_witness_name name protocol_id);
            capability_pattern ?value_type name value_ty;
          ]
    | None -> (
        match Types.truthy_constraint_info ty with
        | Some value_ty ->
            Semantic_ir.PTuple
              [
                Semantic_ir.PVar (name ^ "__truthy");
                capability_pattern ?value_type name value_ty;
              ]
        | None -> (
            match Types.nil_predicate_constraint_info ty with
            | Some value_ty ->
                Semantic_ir.PTuple
                  [
                    Semantic_ir.PVar (name ^ "__nil");
                    capability_pattern ?value_type name value_ty;
                  ]
            | None -> (
            match Types.printable_constraint_info ty with
            | Some value_ty ->
                let witness_pattern suffix =
                  let pattern = Semantic_ir.PVar (name ^ suffix) in
                  let payload_ty = Types.constraint_value_type value_ty in
                  if not (concrete_constraint_type payload_ty) then pattern
                  else
                    Semantic_ir.PConstraint
                      (pattern, Types.ocaml_name (TFn ([payload_ty], TString)))
                in
                Semantic_ir.PTuple
                  [
                    Semantic_ir.PTuple
                      [ witness_pattern "__print";
                        witness_pattern "__pr";
                      ];
                    capability_pattern ?value_type name value_ty;
                  ]
            | None -> (
                match Types.exception_data_constraint_info ty with
                | Some value_ty ->
                    Semantic_ir.PTuple
                      [
                        Semantic_ir.PVar (name ^ "__ex_data");
                        capability_pattern ?value_type name value_ty;
                      ]
                | None -> (
                match Types.hashable_constraint_info ty with
                | Some value_ty ->
                    Semantic_ir.PTuple
                      [
                        Semantic_ir.PVar (name ^ "__hash");
                        capability_pattern ?value_type name value_ty;
                      ]
                | None -> (
                    match Types.comparable_constraint_info ty with
                    | Some value_ty ->
                        Semantic_ir.PTuple
                          [
                            Semantic_ir.PVar (name ^ "__compare");
                            capability_pattern ?value_type name value_ty;
                          ]
                    | None -> (
                        match Types.array_index_constraint_info ty with
                        | Some value_ty ->
                            Semantic_ir.PTuple
                              [
                                Semantic_ir.PVar (name ^ "__index");
                                capability_pattern ?value_type name value_ty;
                              ]
                        | None -> (
                match Types.symbol_predicate_constraint_info ty with
                | Some value_ty ->
                    Semantic_ir.PTuple
                      [
                        Semantic_ir.PVar (name ^ "__symbol");
                        capability_pattern ?value_type name value_ty;
                      ]
                | None -> (
        match Types.contains_constraint_info ty with
        | Some (_, value_ty) ->
            Semantic_ir.PTuple
              [
                Semantic_ir.PVar (name ^ "__contains");
                capability_pattern ?value_type name value_ty;
              ]
        | None -> (
        match ty with
        | TConstraint
            (Seqable_constraint { requirement; element; storage = value_ty; _ }) ->
            let sequence_name =
              if requirement = Required then name ^ "__seq"
              else name ^ "__seq_optional"
            in
            let sequence_pattern = Semantic_ir.PVar sequence_name in
            let sequence_pattern =
              match element with
              | TOcaml _ | TNamed_record _ ->
                  let adapter_type = "_ -> " ^ Types.ocaml_name (TSeq element) in
                  let adapter_type =
                    if requirement = Required then adapter_type
                    else "(" ^ adapter_type ^ ") option"
                  in
                  Semantic_ir.PConstraint
                    (sequence_pattern, adapter_type)
              | _ -> sequence_pattern
            in
            Semantic_ir.PTuple
              [
                sequence_pattern;
                capability_pattern ?value_type name value_ty;
              ]
        | _ ->
            let pattern = Semantic_ir.PVar name in
            Option.fold ~none:pattern
              ~some:(fun type_name ->
                if String.equal type_name "_" then pattern
                else Semantic_ir.PConstraint (pattern, type_name))
              value_type)
        )))))))))
  in
  let param_patterns =
    List.map2 (fun name ty -> (name, ty)) param_names param_tys
    |> List.mapi (fun index (name, ty) ->
           let row_type_name =
             List.nth_opt row_param_type_names index |> Option.join
           in
           let pattern =
             if
               Option.is_some (Types.protocol_constraint_info ty)
               || Option.is_some (Types.seqable_constraint_element ty)
               || Option.is_some (Types.truthy_constraint_info ty)
               || Option.is_some (Types.nil_predicate_constraint_info ty)
               || Option.is_some (Types.printable_constraint_info ty)
               || Option.is_some (Types.exception_data_constraint_info ty)
               || Option.is_some (Types.hashable_constraint_info ty)
               || Option.is_some (Types.comparable_constraint_info ty)
               || Option.is_some (Types.array_index_constraint_info ty)
               || Option.is_some
                    (Types.symbol_predicate_constraint_info ty)
               || Option.is_some (Types.contains_constraint_info ty)
             then
               let pattern_ty =
                 match row_type_name with
                 | Some type_name -> apply_row_constraint_type type_name ty
                 | None -> ty
               in
               let value_type =
                 pattern_ty |> Types.constraint_value_type
                 |> pattern_constraint_type |> Types.ocaml_name
               in
               capability_pattern ~value_type name pattern_ty
             else
               match row_type_name with
               | Some type_name ->
                   Semantic_ir.PConstraint
                     ( Semantic_ir.PVar name,
                       Types.ocaml_name (apply_row_constraint_type type_name ty) )
            | _ -> (
                match ty with
                | TRecord _ | TNamed_record _
                | TNullable (TRecord _ | TNamed_record _) ->
                    Semantic_ir.PTyped (Semantic_ir.PVar name, ty)
               | TFn _ when not (contains_open_type ty) ->
                    Semantic_ir.PTyped (Semantic_ir.PVar name, ty)
               | _ -> (
                   match param_constraint_name ty with
                   | Some _ ->
                        Semantic_ir.PConstraint
                          ( Semantic_ir.PVar name,
                            Types.ocaml_name (pattern_constraint_type ty) )
                   | None -> Semantic_ir.PVar name))
           in
           match List.nth_opt parts.param_identities index |> Option.join with
           | None -> pattern
           | Some (node_id, location) ->
               Semantic_ir.PLocated (node_id, location, pattern))
  in
  let body_expr =
    match parts.destructured_bindings with
    | [] -> body_semantic_expr
    | bindings ->
        Semantic_ir.Let
          ( List.map
              (fun (binding : Destructure.local_binding) ->
                let pattern =
                  if
                    Option.is_some (Types.protocol_constraint_info binding.ty)
                    || Option.is_some
                         (Types.seqable_constraint_element binding.ty)
                    || Option.is_some
                         (Types.truthy_constraint_info binding.ty)
                    || Option.is_some
                        (Types.nil_predicate_constraint_info binding.ty)
                    || Option.is_some
                         (Types.printable_constraint_info binding.ty)
                    || Option.is_some
                         (Types.exception_data_constraint_info binding.ty)
                    || Option.is_some
                         (Types.hashable_constraint_info binding.ty)
                    || Option.is_some
                         (Types.comparable_constraint_info binding.ty)
                    || Option.is_some
                         (Types.array_index_constraint_info binding.ty)
                    || Option.is_some
                         (Types.symbol_predicate_constraint_info binding.ty)
                    || Option.is_some
                         (Types.contains_constraint_info binding.ty)
                  then capability_pattern binding.ocaml_name binding.ty
                  else Semantic_ir.PVar binding.ocaml_name
                in
                let pattern =
                  match binding.identity with
                  | None -> pattern
                  | Some (node_id, location) ->
                      Semantic_ir.PLocated (node_id, location, pattern)
                in
                (pattern, binding.semantic_expr))
              bindings,
            body_semantic_expr )
  in
  let return_param_index =
    let same_nominal_type left right =
      match (left, right) with
      | TNamed_record left, TNamed_record right ->
          Type_id.equal left.type_id right.type_id
          && List.length left.type_arguments = List.length right.type_arguments
          && List.for_all2 Types.equal left.type_arguments right.type_arguments
      | _ -> Types.equal left right
    in
    let returned_name =
      match Semantic_ir.unlocated parts.body.semantic_expr with
      | Semantic_ir.Ident name -> Some name
      | Semantic_ir.Sequence expressions -> (
          match List.rev expressions with
          | expression :: _ -> (
              match Semantic_ir.unlocated expression with
              | Semantic_ir.Ident name -> Some name
              | _ -> None)
          | [] -> None)
      | _ -> None
    in
    match (parts.destructured_bindings, returned_name) with
    | [], Some returned_name ->
        param_names
        |> List.mapi (fun index name -> (index, name))
        |> List.find_opt (fun (_index, name) -> name = returned_name)
        |> Option.map fst
    | _ -> (
        match parts.return_param_index_hint with
        | Some _ as index -> index
        | None
          when (match return_ty with
               | TUnknown | TMeta _ | TVar _ -> false
               | _ -> true) ->
            param_tys
            |> List.mapi (fun index ty -> (index, ty))
            |> List.filter (fun (_, ty) -> same_nominal_type ty return_ty)
            |> (function
                 | [ index, _ ] -> Some index
                 | [] | _ :: _ :: _ -> None)
        | None -> None)
  in
  let return_ty =
    match return_param_index with
    | Some index -> (
        match List.nth_opt param_tys index with
        | Some parameter_ty -> (
            match return_ty with
            | TOcaml_app ("result", [ ok_ty; error_ty ])
              when Types.equal ok_ty parameter_ty
                   || Types.row_compatible ~expected:parameter_ty
                        ~actual:ok_ty
                   || Types.row_compatible ~expected:ok_ty
                        ~actual:parameter_ty ->
                TOcaml_app ("result", [ ok_ty; error_ty ])
            | _ -> (
            match Types.seqable_constraint_info parameter_ty with
            | Some (_, _, storage_ty) when Types.equal return_ty storage_ty ->
                return_ty
            | Some _ | None -> parameter_ty))
        | None -> return_ty)
    | None -> return_ty
  in
  let body_expr =
    if Types.equal return_ty body_storage_ty then body_expr
    else coerce_expression_to_type return_ty body_storage_ty body_expr
  in
  {
    (typed_ir
       (TFn (param_tys, return_ty))
       (Semantic_ir.Fun (param_patterns, body_expr)))
    with
    return_param_index;
  }
