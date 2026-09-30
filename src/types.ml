include Semantic_type

type binding = {
  ocaml_name : string;
  ty : ty;
  scheme : scheme option;
  protocol_id : Protocol_id.t option;
  row_param_types : string option list;
  host_reference : host_reference option;
  return_param_index : int option;
  overload_targets : string list;
  overload_row_param_types : string option list list;
  forward_declared : bool;
  constant_keyword : string option;
  false_non_nil_names : string list;
  dynamically_bindable : bool;
  redef_root_name : string option;
  multimethod : bool;
  multimethod_method_types : ty list;
  multimethod_definition : Semantic_ir.t option;
  never_returns : bool;
  gadt_constructor : bool;
}

and host_reference =
  | Ocaml_module of string
  | Ocaml_value of string

type typed_expr = {
  ty : ty;
  semantic_expr : Semantic_ir.t;
  record_values : (field * Semantic_ir.t) list option;
  return_param_index : int option;
}

let typed_ir ty semantic_expr =
  {
    ty;
    semantic_expr = Semantic_ir.annotate ty semantic_expr;
    record_values = None;
    return_param_index = None;
  }

let binding ?(row_param_types = []) ?host_reference ?protocol_id
    ?return_param_index ?(overload_targets = [])
    ?(overload_row_param_types = []) ?(forward_declared = false)
    ?constant_keyword ?(false_non_nil_names = []) ?(dynamically_bindable = false)
    ?redef_root_name ?(multimethod = false) ?(multimethod_method_types = [])
    ?multimethod_definition
    ?(never_returns = false) ?(gadt_constructor = false)
    ocaml_name ty =
  {
    ocaml_name;
    ty;
    scheme = None;
    protocol_id;
    row_param_types;
    host_reference;
    return_param_index;
    overload_targets;
    overload_row_param_types;
    forward_declared;
    constant_keyword;
    false_non_nil_names;
    dynamically_bindable;
    redef_root_name;
    multimethod;
    multimethod_method_types;
    multimethod_definition;
    never_returns;
    gadt_constructor;
  }

let is_runtime_root (binding : binding) =
  binding.dynamically_bindable || Option.is_some binding.redef_root_name

let runtime_root_value_type (binding : binding) =
  if binding.dynamically_bindable then
    match binding.ty with TRef value_ty -> Some value_ty | _ -> None
  else Option.map (fun _ -> binding.ty) binding.redef_root_name

let runtime_root_name (binding : binding) =
  if binding.dynamically_bindable then Some binding.ocaml_name
  else binding.redef_root_name

let generalize_binding (binding : binding) =
  match binding.ty with
  | TArray _ | TRef _ -> binding
  | _ ->
      let scheme = Type_solver.generalize binding.ty in
      (match scheme.quantified with
      | [] -> binding
      | _ -> { binding with ty = scheme.body; scheme = Some scheme })

let instantiate_binding (binding : binding) =
  match binding.scheme with
  | None -> binding
  | Some scheme -> { binding with ty = Type_solver.instantiate scheme }

let module_package_name = "__lg_module_package"
let module_package_type signature = TCompiler (Module_package signature)
let module_package_signature = function
  | TCompiler (Module_package signature) -> Some signature
  | TOcaml_app (name, [ TOcaml signature ]) when name = module_package_name ->
      Some signature
  | _ -> None

let constant_function_name = "__lg_constant_function"
let constant_function result_ty = TCompiler (Constant_function result_ty)
let constant_function_result = function
  | TCompiler (Constant_function result_ty) -> Some result_ty
  | TOcaml_app (name, [ result_ty ]) when name = constant_function_name ->
      Some result_ty
  | _ -> None

let reify_self_method_name = "__lg_self_returning_method"
let reify_self_method method_ty = TCompiler (Reify_self_method method_ty)

let reify_self_method_type = function
  | TCompiler (Reify_self_method method_ty) -> Some method_ty
  | TOcaml_app (name, [ method_ty ]) when name = reify_self_method_name ->
      Some method_ty
  | _ -> None

let seqable_constraint element_ty =
  TConstraint
    (Seqable_constraint
       { requirement = Required; element = element_ty; storage = TUnknown })

let seqable_constraint_with_value element_ty value_ty =
  TConstraint
    (Seqable_constraint
       { requirement = Required; element = element_ty; storage = value_ty })

let contains_constraint key_ty =
  TConstraint (Contains_constraint { key = key_ty; storage = TUnknown })

let contains_constraint_with_value key_ty value_ty =
  TConstraint (Contains_constraint { key = key_ty; storage = value_ty })

let contains_constraint_info = function
  | TConstraint (Contains_constraint { key; storage }) -> Some (key, storage)
  | _ -> None

let optional_seqable_constraint element_ty value_ty =
  TConstraint
    (Seqable_constraint
       { requirement = Optional; element = element_ty; storage = value_ty })

let optional_sequential_constraint element_ty value_ty =
  TConstraint
    (Seqable_constraint
       {
         requirement = Optional_sequential;
         element = element_ty;
         storage = value_ty;
       })

let truthy_constraint value_ty =
  TConstraint (Truthy_constraint value_ty)

let truthy_constraint_info = function
  | TConstraint (Truthy_constraint value_ty) -> Some value_ty
  | _ -> None

let nil_predicate_constraint value_ty =
  TConstraint (Nil_predicate_constraint value_ty)

let nil_predicate_constraint_info = function
  | TConstraint (Nil_predicate_constraint value_ty) -> Some value_ty
  | _ -> None

let printable_constraint value_ty =
  TConstraint (Printable_constraint value_ty)

let printable_constraint_info = function
  | TConstraint (Printable_constraint value_ty) -> Some value_ty
  | _ -> None

let exception_data_constraint value_ty =
  TConstraint (Exception_data_constraint value_ty)

let exception_data_constraint_info = function
  | TConstraint (Exception_data_constraint value_ty) -> Some value_ty
  | _ -> None

let hashable_constraint value_ty =
  TConstraint (Hashable_constraint value_ty)

let hashable_constraint_info = function
  | TConstraint (Hashable_constraint value_ty) -> Some value_ty
  | _ -> None

let comparable_constraint value_ty =
  TConstraint (Comparable_constraint value_ty)

let comparable_constraint_info = function
  | TConstraint (Comparable_constraint value_ty) -> Some value_ty
  | _ -> None

let array_index_constraint value_ty =
  TConstraint (Array_index_constraint value_ty)

let array_index_constraint_info = function
  | TConstraint (Array_index_constraint value_ty) -> Some value_ty
  | _ -> None

let symbol_predicate_constraint value_ty =
  TConstraint (Symbol_predicate_constraint value_ty)

let symbol_predicate_constraint_info = function
  | TConstraint (Symbol_predicate_constraint value_ty) -> Some value_ty
  | _ -> None

let dynamic_constraint capability =
  TConstraint (Open_boundary_constraint capability)

let dynamic_constraint_info = function
  | TConstraint (Open_boundary_constraint capability) -> Some capability
  | _ -> None

let is_dynamic ty = Option.is_some (dynamic_constraint_info ty)

let rec contains_dynamic = function
  | TPoly_variant row -> List.exists contains_dynamic (List.filter_map snd row.tags)
  | ty when is_dynamic ty -> true
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      contains_dynamic ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists contains_dynamic arguments
  | TCompiler marker ->
      List.exists contains_dynamic (compiler_marker_children marker)
  | TConstraint constraint_ -> (
      match constraint_ with
      | Seqable_constraint { element; storage; _ } ->
          contains_dynamic element || contains_dynamic storage
      | Contains_constraint { key; storage } ->
          contains_dynamic key || contains_dynamic storage
      | Truthy_constraint value
      | Nil_predicate_constraint value
      | Printable_constraint value
      | Exception_data_constraint value
      | Hashable_constraint value
      | Comparable_constraint value
      | Array_index_constraint value
      | Symbol_predicate_constraint value
      | Open_boundary_constraint value ->
          contains_dynamic value
      | Protocol_constraint { witness; value; _ } ->
          contains_dynamic witness || contains_dynamic value)
  | TFn (parameters, return_ty) ->
      List.exists contains_dynamic (return_ty :: parameters)
  | TOverloaded_fn arities ->
      List.exists
        (fun arity ->
          List.exists contains_dynamic (arity.return_ty :: arity.fixed_params)
          || Option.fold ~none:false ~some:contains_dynamic arity.rest_param)
        arities
  | TRecord fields ->
      List.exists (fun (field : field) -> contains_dynamic field.ty) fields
  | TNamed_record record ->
      List.exists contains_dynamic record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _ ->
      false

let normalize_nullable ty =
  let rec payload = function
    | TNullable inner | TOcaml_app ("option", [ inner ]) -> payload inner
    | inner -> inner
  in
  match ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      TNullable (payload inner)
  | ty -> ty

let weak_type_name = "Lg_runtime.Runtime_weak.t"
let weak_type value_ty = TOcaml_app (weak_type_name, [ value_ty ])

let weak_element = function
  | TOcaml_app (name, [ value_ty ]) when name = weak_type_name -> Some value_ty
  | _ -> None

let protocol_witness_type method_types =
  List.fold_right (fun method_ty rest -> TTuple [ method_ty; rest ])
    method_types TUnit

let rec protocol_witness_method_types = function
  | TUnit -> Some []
  | TTuple [ method_ty; rest ] ->
      Option.map
        (fun method_types -> method_ty :: method_types)
        (protocol_witness_method_types rest)
  | _ -> None

let protocol_constraint protocol_id method_types value_ty =
  TConstraint
    (Protocol_constraint
       {
         protocol_id;
         witness = protocol_witness_type method_types;
         value = value_ty;
         guarded = false;
       })

let sorted_constraint entry_ty key_ty value_ty =
  let protocol_id = Protocol_id.create ~owner:[] ~name:"ISorted" in
  let comparator_ty = TFn ([ key_ty; key_ty ], TInt) in
  protocol_constraint protocol_id
    [
      TFn ([ value_ty ], comparator_ty);
      TFn ([ value_ty; entry_ty ], key_ty);
      TFn ([ value_ty; TBool ], TSeq entry_ty);
      TFn ([ value_ty; key_ty; TBool ], TSeq entry_ty);
    ]
    value_ty

let map_entry_constraint key_ty value_ty storage_ty =
  let protocol_id = Protocol_id.create ~owner:[] ~name:"IMapEntry" in
  protocol_constraint protocol_id
    [ TFn ([ storage_ty ], key_ty); TFn ([ storage_ty ], value_ty) ]
    storage_ty

let guarded_protocol_constraint constraint_ty =
  match constraint_ty with
  | TConstraint (Protocol_constraint constraint_) ->
      TConstraint (Protocol_constraint { constraint_ with guarded = true })
  | _ -> constraint_ty

let is_guarded_protocol_constraint = function
  | TConstraint (Protocol_constraint { guarded; _ }) -> guarded
  | _ -> false

let protocol_constraint_info = function
  | TConstraint (Protocol_constraint { protocol_id; witness; value; _ }) ->
      Some (protocol_id, witness, value)
  | _ -> None

let sorted_constraint_info ty =
  match protocol_constraint_info ty with
  | Some (protocol_id, witness_ty, value_ty)
    when String.equal (Protocol_id.name protocol_id) "ISorted" -> (
      match protocol_witness_method_types witness_ty with
      | Some
          (TFn ([ _ ], TFn ([ key_ty; _ ], TInt))
          :: TFn ([ _; entry_ty ], _)
          :: TFn ([ _; TBool ], TSeq _)
          :: TFn ([ _; _; TBool ], TSeq _)
          :: []) ->
          Some (entry_ty, key_ty, value_ty)
      | Some _ | None -> None)
  | Some _ | None -> None

let capability_constraint_value ty =
  match protocol_constraint_info ty with
  | Some (_, _, value_ty) -> Some value_ty
  | None -> (
      match truthy_constraint_info ty with
      | Some value_ty -> Some value_ty
      | None -> (
          match nil_predicate_constraint_info ty with
          | Some value_ty -> Some value_ty
          | None -> (
              match printable_constraint_info ty with
              | Some value_ty -> Some value_ty
              | None -> (
                  match exception_data_constraint_info ty with
                  | Some value_ty -> Some value_ty
                  | None -> (
                  match hashable_constraint_info ty with
                  | Some value_ty -> Some value_ty
                  | None -> (
                      match comparable_constraint_info ty with
                      | Some value_ty -> Some value_ty
                      | None -> (
                          match array_index_constraint_info ty with
                          | Some value_ty -> Some value_ty
                          | None -> (
                          match symbol_predicate_constraint_info ty with
                          | Some value_ty -> Some value_ty
                          | None ->
                              Option.map snd (contains_constraint_info ty)))))))))

let rec nested_comparable_constraint_info ty =
  match comparable_constraint_info ty with
  | Some value_ty -> Some value_ty
  | None -> (
      match capability_constraint_value ty with
      | Some value_ty -> nested_comparable_constraint_info value_ty
      | None -> (
          match ty with
          | TConstraint (Seqable_constraint { storage; _ }) ->
              nested_comparable_constraint_info storage
          | _ -> None))

let rec seqable_constraint_element = function
  | TConstraint (Seqable_constraint { element; _ }) -> Some element
  | ty -> (
      match capability_constraint_value ty with
      | Some value_ty -> seqable_constraint_element value_ty
      | None -> None)

let rec seqable_constraint_info = function
  | TConstraint (Seqable_constraint { requirement; element; storage }) ->
      let requirement =
        match requirement with
        | Required -> `Required
        | Optional -> `Optional
        | Optional_sequential -> `Optional_sequential
      in
      Some (requirement, element, storage)
  | ty -> (
      match capability_constraint_value ty with
      | Some value_ty -> seqable_constraint_info value_ty
      | None -> None)

let rec constraint_value_type ty =
  match dynamic_constraint_info ty with
  | Some _ -> ty
  | None -> (
  match capability_constraint_value ty with
  | Some value_ty -> constraint_value_type value_ty
  | None -> (
      match ty with
      | TConstraint (Seqable_constraint { storage; _ }) ->
          constraint_value_type storage
      | value_ty -> value_ty))

let static_unary_constraint_value = function
  | TConstraint
      ( Truthy_constraint value
      | Nil_predicate_constraint value
      | Printable_constraint value
      | Exception_data_constraint value
      | Hashable_constraint value
      | Comparable_constraint value
      | Array_index_constraint value
      | Symbol_predicate_constraint value ) ->
      Some value
  | _ -> None

let rec remove_protocol_constraint protocol_id ty =
  match protocol_constraint_info ty with
  | Some (candidate_id, _, value_ty)
    when Protocol_id.equal candidate_id protocol_id ->
      remove_protocol_constraint protocol_id value_ty
  | Some (_, witness_ty, value_ty) -> (
      match ty with
      | TConstraint (Protocol_constraint constraint_) ->
          TConstraint
            (Protocol_constraint
               {
                 constraint_ with
                 witness = witness_ty;
                 value = remove_protocol_constraint protocol_id value_ty;
               })
      | _ -> ty)
  | None -> (
      match ty with
      | TConstraint (Seqable_constraint constraint_) ->
          TConstraint
            (Seqable_constraint
               {
                 constraint_ with
                 storage =
                   remove_protocol_constraint protocol_id constraint_.storage;
               })
      | TConstraint (Contains_constraint constraint_) ->
          TConstraint
            (Contains_constraint
               {
                 constraint_ with
                 storage =
                   remove_protocol_constraint protocol_id constraint_.storage;
               })
      | TConstraint (Truthy_constraint value) ->
          TConstraint
            (Truthy_constraint (remove_protocol_constraint protocol_id value))
      | TConstraint (Nil_predicate_constraint value) ->
          TConstraint
            (Nil_predicate_constraint
               (remove_protocol_constraint protocol_id value))
      | TConstraint (Printable_constraint value) ->
          TConstraint
            (Printable_constraint (remove_protocol_constraint protocol_id value))
      | TConstraint (Exception_data_constraint value) ->
          TConstraint
            (Exception_data_constraint
               (remove_protocol_constraint protocol_id value))
      | TConstraint (Hashable_constraint value) ->
          TConstraint
            (Hashable_constraint (remove_protocol_constraint protocol_id value))
      | TConstraint (Comparable_constraint value) ->
          TConstraint
            (Comparable_constraint
               (remove_protocol_constraint protocol_id value))
      | TConstraint (Array_index_constraint value) ->
          TConstraint
            (Array_index_constraint
               (remove_protocol_constraint protocol_id value))
      | TConstraint (Symbol_predicate_constraint value) ->
          TConstraint
            (Symbol_predicate_constraint
               (remove_protocol_constraint protocol_id value))
      | TConstraint (Open_boundary_constraint _) | _ -> ty)

let protocol_witness_with_receiver value_ty witness_ty =
  let receiver_ty = constraint_value_type value_ty in
  let with_receiver = function
    | TFn (_ :: parameters, return_ty) ->
        TFn (receiver_ty :: parameters, return_ty)
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun arity ->
               match arity.fixed_params with
               | _ :: parameters ->
                   { arity with fixed_params = receiver_ty :: parameters }
               | [] -> arity)
             arities)
    | ty -> ty
  in
  match protocol_witness_method_types witness_ty with
  | Some method_types ->
      protocol_witness_type (List.map with_receiver method_types)
  | None -> witness_ty

let rec deduplicate_protocol_constraints ty =
  match protocol_constraint_info ty with
  | Some (protocol_id, witness_ty, value_ty) -> (
      match ty with
      | TConstraint (Protocol_constraint constraint_) ->
          let value_ty =
            value_ty |> deduplicate_protocol_constraints
            |> remove_protocol_constraint protocol_id
          in
          let witness_ty =
            protocol_witness_with_receiver value_ty witness_ty
          in
          TConstraint
            (Protocol_constraint
               { constraint_ with witness = witness_ty; value = value_ty })
      | _ -> ty)
  | None -> ty

let rec require_guarded_protocol_constraint protocol_id = function
  | TConstraint
      (Protocol_constraint ({ protocol_id = candidate; _ } as constraint_))
    when Protocol_id.equal protocol_id candidate ->
      Some
        (TConstraint
           (Protocol_constraint { constraint_ with guarded = false })
        |> deduplicate_protocol_constraints)
  | TConstraint (Protocol_constraint constraint_) ->
      Option.map
        (fun value ->
          TConstraint (Protocol_constraint { constraint_ with value })
          |> deduplicate_protocol_constraints)
        (require_guarded_protocol_constraint protocol_id constraint_.value)
  | _ -> None

let protocol_constraint_with_value constraint_ty value_ty =
  match constraint_ty with
  | TConstraint
      (Protocol_constraint ({ protocol_id; witness; _ } as constraint_)) ->
      let value_ty = remove_protocol_constraint protocol_id value_ty in
      let witness = protocol_witness_with_receiver value_ty witness in
      TConstraint
        (Protocol_constraint { constraint_ with witness; value = value_ty })
      |> deduplicate_protocol_constraints
  | ty -> ty

let reify_protocol_payload_prefix = "__lg_reify_protocol:"

let reify_protocol_payload protocol_id methods rest =
  TCompiler
    (Reify_protocol_payload (Protocol_id.to_string protocol_id, methods, rest))

let reify_protocol_payload_info = function
  | TCompiler (Reify_protocol_payload (id, methods, rest)) ->
      Some (id, methods, rest)
  | TOcaml_app (name, [ methods; rest ])
    when String.starts_with ~prefix:reify_protocol_payload_prefix name ->
      Some
        ( String.sub name
            (String.length reify_protocol_payload_prefix)
            (String.length name - String.length reify_protocol_payload_prefix),
          methods,
          rest )
  | _ -> None

let protocol_witness_name value_name protocol_id =
  value_name ^ "__protocol_"
  ^ String.sub (Digest.to_hex (Digest.string (Protocol_id.to_string protocol_id)))
      0 12

let next_seq_type_name = "__lg_next_seq"
let reversible_next_seq_type_name = "__lg_reversible_next_seq"

let is_next_seq_type_name name =
  name = next_seq_type_name || name = reversible_next_seq_type_name

let next_seq inner = TCompiler (Next_seq inner)

let reversible_next_seq inner = TCompiler (Reversible_next_seq inner)

let next_seq_element = function
  | TCompiler (Next_seq inner | Reversible_next_seq inner) -> Some inner
  | TOcaml_app (name, [ inner ]) when is_next_seq_type_name name -> Some inner
  | _ -> None

let reversible_next_seq_element = function
  | TCompiler (Reversible_next_seq inner) -> Some inner
  | TOcaml_app (name, [ inner ]) when name = reversible_next_seq_type_name ->
      Some inner
  | _ -> None

let reduced_type_name = "Lg_runtime.Runtime_reduced.t"
let reduced inner = TOcaml_app (reduced_type_name, [ inner ])

let maybe_reduced_callback_type_name = "__lg_maybe_reduced_callback_result"

let maybe_reduced_callback_result inner =
  TCompiler (Maybe_reduced_callback inner)

let optional_map_adapter_type_name = "__lg_optional_map_adapter"

let optional_map_adapter key_ty value_ty =
  TCompiler (Optional_map_adapter (key_ty, value_ty))

let optional_map_adapter_info = function
  | TCompiler (Optional_map_adapter (key_ty, value_ty)) ->
      Some (key_ty, value_ty)
  | _ -> None

let record_marker_prefix = "__lg_record:"
let record_app_marker_prefix = "__lg_record_app:"

let named_record_marker name = TCompiler (Named_record_marker name)

let named_record_marker_name = function
  | TCompiler (Named_record_marker name) -> Some name
  | TOcaml name when String.starts_with ~prefix:record_marker_prefix name ->
      Some
        (String.sub name
           (String.length record_marker_prefix)
           (String.length name - String.length record_marker_prefix))
  | _ -> None

let named_record_app_marker name args =
  TCompiler (Named_record_app_marker (name, args))

let named_record_app_marker_info = function
  | TCompiler (Named_record_app_marker (name, args)) -> Some (name, args)
  | TOcaml_app (name, args)
    when String.starts_with ~prefix:record_app_marker_prefix name ->
      Some
        ( String.sub name
            (String.length record_app_marker_prefix)
            (String.length name - String.length record_app_marker_prefix),
          args )
  | _ -> None

let compiler_marker_type_name = function
  | Module_package _ -> module_package_name
  | Constant_function _ -> constant_function_name
  | Reify_self_method _ -> reify_self_method_name
  | Reify_protocol_payload (id, _, _) -> reify_protocol_payload_prefix ^ id
  | Next_seq _ -> next_seq_type_name
  | Reversible_next_seq _ -> reversible_next_seq_type_name
  | Maybe_reduced_callback _ -> maybe_reduced_callback_type_name
  | Optional_map_adapter _ -> optional_map_adapter_type_name
  | Named_record_marker name -> record_marker_prefix ^ name
  | Named_record_app_marker (name, _) -> record_app_marker_prefix ^ name
  | Protocol_marker -> "__lg_protocol_marker"
  | Date_millis -> "__lg_date_millis"

let dynamic_map key value =
  TOcaml_app ("Lg_runtime.Runtime_map.t", [ key; value ])

let record_extension_keyword = ":__lg/extmap"
let record_metadata_key = "\000lg-record-metadata"
let record_identity_keyword = ":__lg/identity"

let dynamic_map_types = function
  | TOcaml_app ("Lg_runtime.Runtime_map.t", [ key; value ]) ->
      Some (key, value)
  | _ -> None

let rec edn_compatible_static_type = function
  | TUnknown | TMeta _ | TVar _ -> true
  | TNil | TBool | TString | TChar | TSymbol | TKeyword | TInt | TFloat
  | TRegex ->
      true
  | TOcaml "int" | TOcaml "int64" | TOcaml "float" | TOcaml "string"
  | TOcaml "bool" ->
      true
  | TList element | TSeq element | TVector element | TArray element
  | TOcaml_app ("array", [ element ])
  | TSet element
  | TNullable element
  | TOcaml_app ("option", [ element ]) ->
      edn_compatible_static_type element
  | TRecord fields | TNamed_record { fields; nominal = false; _ } ->
      List.for_all
        (fun (field : field) -> edn_compatible_static_type field.ty)
        fields
  | TOcaml_app ("Lg_runtime.Runtime_map.t", [ key_ty; value_ty ]) ->
      edn_compatible_static_type key_ty
      && edn_compatible_static_type value_ty
  | _ -> false

let reduced_element = function
  | TOcaml_app (name, [ inner ]) when name = reduced_type_name -> Some inner
  | _ -> None

let maybe_reduced_callback_element = function
  | TCompiler (Maybe_reduced_callback inner) -> Some inner
  | TOcaml_app (name, [ inner ])
    when name = maybe_reduced_callback_type_name ->
      Some inner
  | _ -> None

let rec equal left right =
  match (left, right) with
  | TPoly_variant left, TPoly_variant right ->
      left.bound = right.bound && List.length left.tags = List.length right.tags
      && List.for_all2 (fun (ln, lt) (rn, rt) -> ln = rn && Option.equal equal lt rt) left.tags right.tags
  | TUnknown, TUnknown -> true
  | TMeta left, TMeta right -> left.id = right.id
  | TVar left, TVar right -> left = right
  | TInt, TOcaml "int" | TOcaml "int", TInt -> true
  | TInt, TInt
  | TFloat, TFloat
  | TChar, TChar
  | TString, TString
  | TRegex, TRegex
  | TMap_keys, TMap_keys
  | TSymbol, TSymbol
  | TKeyword, TKeyword
  | TBool, TBool
  | TUnit, TUnit
  | TNil, TNil ->
      true
  | TNullable left, TNullable right -> equal left right
  | TOcaml left, TOcaml right -> left = right
  | TOcaml_app (left_name, left_args), TOcaml_app (right_name, right_args) ->
      left_name = right_name
      && List.length left_args = List.length right_args
      && List.for_all2 equal left_args right_args
  | TCompiler left, TCompiler right -> equal_compiler_marker left right
  | TConstraint left, TConstraint right -> equal_constraint left right
  | TTuple left, TTuple right ->
      List.length left = List.length right && List.for_all2 equal left right
  | TArray left, TArray right | TRef left, TRef right -> equal left right
  | TList left, TList right -> equal left right
  | TVector left, TVector right -> equal left right
  | TSet left, TSet right -> equal left right
  | TSeq left, TSeq right -> equal left right
  | TFn (left_args, left_ret), TFn (right_args, right_ret) ->
      List.length left_args = List.length right_args
      && List.for_all2 equal left_args right_args
      && equal left_ret right_ret
  | TOverloaded_fn left, TOverloaded_fn right ->
      List.length left = List.length right
      && List.for_all2 equal_fn_arity left right
  | TRecord left, TRecord right ->
      List.length left = List.length right
      &&
      if
        List.for_all (fun (field : field) -> field.runtime_map) left
        && List.for_all (fun (field : field) -> field.runtime_map) right
      then
        List.for_all
          (fun left_field ->
            match
              List.find_opt
                (fun right_field ->
                  left_field.keyword = right_field.keyword)
                right
            with
            | Some right_field -> equal left_field.ty right_field.ty
            | None -> false)
          left
      else
        List.for_all2
          (fun l r ->
            l.keyword = r.keyword
            && l.runtime_map = r.runtime_map
            && l.quantified = r.quantified
            && equal l.ty r.ty)
          left right
  | TNamed_record left, TNamed_record right ->
      Type_id.equal left.type_id right.type_id
  | _ -> false

and equal_constraint left right =
  match (left, right) with
  | ( Seqable_constraint
        { requirement = left_requirement; element = left_element; storage = left_storage },
      Seqable_constraint
        {
          requirement = right_requirement;
          element = right_element;
          storage = right_storage;
        } ) ->
      left_requirement = right_requirement
      && equal left_element right_element
      && equal left_storage right_storage
  | ( Contains_constraint { key = left_key; storage = left_storage },
      Contains_constraint { key = right_key; storage = right_storage } ) ->
      equal left_key right_key && equal left_storage right_storage
  | Truthy_constraint left, Truthy_constraint right
  | Nil_predicate_constraint left, Nil_predicate_constraint right
  | Printable_constraint left, Printable_constraint right
  | Exception_data_constraint left, Exception_data_constraint right
  | Hashable_constraint left, Hashable_constraint right
  | Comparable_constraint left, Comparable_constraint right
  | Array_index_constraint left, Array_index_constraint right
  | Symbol_predicate_constraint left, Symbol_predicate_constraint right
  | Open_boundary_constraint left, Open_boundary_constraint right ->
      equal left right
  | ( Protocol_constraint
        {
          protocol_id = left_id;
          witness = left_witness;
          value = left_value;
          guarded = left_guarded;
        },
      Protocol_constraint
        {
          protocol_id = right_id;
          witness = right_witness;
          value = right_value;
          guarded = right_guarded;
        } ) ->
      Protocol_id.equal left_id right_id
      && left_guarded = right_guarded
      && equal left_witness right_witness
      && equal left_value right_value
  | _ -> false

and equal_fn_arity left right =
  List.length left.fixed_params = List.length right.fixed_params
  && List.for_all2 equal left.fixed_params right.fixed_params
  && Option.equal equal left.rest_param right.rest_param
  && equal left.return_ty right.return_ty

and equal_compiler_marker left right =
  match (left, right) with
  | Module_package left, Module_package right -> left = right
  | Constant_function left, Constant_function right
  | Reify_self_method left, Reify_self_method right
  | Next_seq left, Next_seq right
  | Reversible_next_seq left, Reversible_next_seq right
  | Maybe_reduced_callback left, Maybe_reduced_callback right ->
      equal left right
  | ( Reify_protocol_payload (left_id, left_methods, left_rest),
      Reify_protocol_payload (right_id, right_methods, right_rest) ) ->
      left_id = right_id
      && equal left_methods right_methods
      && equal left_rest right_rest
  | ( Optional_map_adapter (left_key, left_value),
      Optional_map_adapter (right_key, right_value) ) ->
      equal left_key right_key && equal left_value right_value
  | Named_record_marker left, Named_record_marker right -> left = right
  | ( Named_record_app_marker (left_name, left_args),
      Named_record_app_marker (right_name, right_args) ) ->
      left_name = right_name
      && List.length left_args = List.length right_args
      && List.for_all2 equal left_args right_args
  | Protocol_marker, Protocol_marker | Date_millis, Date_millis -> true
  | _ -> false

let homogeneous_record_value_type fields =
  let concrete_storage_type = function
    | TNullable _ -> None
    | ty when Option.is_some (capability_constraint_value ty) -> None
    | ty when Option.is_some (seqable_constraint_info ty) -> None
    | ty -> Some ty
  in
  if
    fields = []
    || not (List.for_all (fun (field : field) -> field.runtime_map) fields)
    || List.exists
         (fun (field : field) -> field.keyword = record_extension_keyword)
         fields
  then None
  else
    match fields with
    | [] -> None
    | (first : field) :: rest ->
        Option.bind (concrete_storage_type first.ty) (fun first_ty ->
            if
              List.for_all
                (fun (field : field) ->
                  match concrete_storage_type field.ty with
                  | Some field_ty -> equal first_ty field_ty
                  | None -> false)
                rest
            then Some first_ty
            else None)

let is_homogeneous_record fields =
  Option.is_some (homogeneous_record_value_type fields)

let is_numeric = function TInt | TFloat -> true | _ -> false

let rec row_compatible ~expected ~actual =
  match (expected, actual) with
  | TPoly_variant expected, TPoly_variant actual ->
      Variant_row.compatible_payloads (fun expected actual -> row_compatible ~expected ~actual) expected actual
  | expected, actual when equal expected actual -> true
  | TUnknown, _ | _, TUnknown | TMeta _, _ | _, TMeta _ | TVar _, _
  | _, TVar _ ->
      true
  | TNullable expected, TNullable actual
  | TNullable expected, TOcaml_app ("option", [ actual ])
  | TOcaml_app ("option", [ expected ]), TNullable actual
  | TArray expected, TArray actual
  | TRef expected, TRef actual
  | TList expected, TList actual
  | TVector expected, TVector actual
  | TSet expected, TSet actual
  | TSeq expected, TSeq actual ->
      row_compatible ~expected ~actual
  | TOcaml_app (expected_name, expected_args),
    TOcaml_app (actual_name, actual_args)
    when expected_name = actual_name
         && List.length expected_args = List.length actual_args ->
      List.for_all2
        (fun expected actual -> row_compatible ~expected ~actual)
        expected_args actual_args
  | TConstraint expected, TConstraint actual ->
      constraint_compatible row_compatible expected actual
  | TTuple expected, TTuple actual
    when List.length expected = List.length actual ->
      List.for_all2
        (fun expected actual -> row_compatible ~expected ~actual)
        expected actual
  | TFn (expected_params, expected_return),
    TFn (actual_params, actual_return)
    when List.length expected_params = List.length actual_params ->
      List.for_all2
        (fun expected actual -> row_compatible ~expected ~actual)
        expected_params actual_params
      && row_compatible ~expected:expected_return ~actual:actual_return
  | TNamed_record expected, TNamed_record actual
    when expected.nominal || actual.nominal ->
      Type_id.equal expected.type_id actual.type_id
  | (TRecord expected_fields | TNamed_record { fields = expected_fields; _ }),
    (TRecord actual_fields | TNamed_record { fields = actual_fields; _ }) ->
      expected_fields
      |> List.for_all (fun expected_field ->
             match
               List.find_opt
                 (fun actual_field -> actual_field.keyword = expected_field.keyword)
                 actual_fields
             with
             | Some actual_field ->
                 expected_field.ty = TUnknown || actual_field.ty = TUnknown
                 || is_dynamic expected_field.ty
                 || is_dynamic actual_field.ty
                 || equal expected_field.ty actual_field.ty
                 || (match (expected_field.ty, actual_field.ty) with
                    | TRef _, TRef _ -> true
                    | _ -> false)
                 || row_compatible ~expected:expected_field.ty
                      ~actual:actual_field.ty
             | None -> expected_field.keyword = record_extension_keyword)
  | TMap_keys, (TRecord _ | TNamed_record _) -> true
  | _ -> false

and constraint_compatible compatible left right =
  let compatible_pair left_first left_second right_first right_second =
    compatible ~expected:left_first ~actual:right_first
    && compatible ~expected:left_second ~actual:right_second
  in
  match (left, right) with
  | ( Seqable_constraint left,
      Seqable_constraint right ) ->
      left.requirement = right.requirement
      && compatible_pair left.element left.storage right.element right.storage
  | Contains_constraint left, Contains_constraint right ->
      compatible_pair left.key left.storage right.key right.storage
  | Truthy_constraint left, Truthy_constraint right
  | Nil_predicate_constraint left, Nil_predicate_constraint right
  | Printable_constraint left, Printable_constraint right
  | Exception_data_constraint left, Exception_data_constraint right
  | Hashable_constraint left, Hashable_constraint right
  | Comparable_constraint left, Comparable_constraint right
  | Array_index_constraint left, Array_index_constraint right
  | Symbol_predicate_constraint left, Symbol_predicate_constraint right
  | Open_boundary_constraint left, Open_boundary_constraint right ->
      compatible ~expected:left ~actual:right
  | Protocol_constraint left, Protocol_constraint right ->
      Protocol_id.equal left.protocol_id right.protocol_id
      && left.guarded = right.guarded
      && compatible_pair left.witness left.value right.witness right.value
  | _ -> false

let rec same_shape left right =
  let named_host_shape record name arguments =
    (record.type_name = name || Type_id.name record.type_id = name)
    && List.length record.type_arguments = List.length arguments
    && List.for_all2 same_shape record.type_arguments arguments
  in
  equal left right
  ||
  match (left, right) with
  | TNamed_record record, TOcaml name
  | TOcaml name, TNamed_record record ->
      named_host_shape record name []
  | TNamed_record record, TOcaml_app (name, arguments)
  | TOcaml_app (name, arguments), TNamed_record record ->
      named_host_shape record name arguments
  | TNamed_record record, TCompiler (Named_record_marker name)
  | TCompiler (Named_record_marker name), TNamed_record record ->
      named_host_shape record name []
  | ( TNamed_record record,
      TCompiler (Named_record_app_marker (name, arguments)) )
  | ( TCompiler (Named_record_app_marker (name, arguments)),
      TNamed_record record ) ->
      named_host_shape record name arguments
  | TCompiler _, TNamed_record _ | TNamed_record _, TCompiler _ -> false
  | _ ->
      row_compatible ~expected:left ~actual:right
      && row_compatible ~expected:right ~actual:left

let host_owned = function
  | TOcaml _ | TOcaml_app _ | TTuple _ | TArray _ | TRef _ | TCompiler _ ->
      true
  | _ -> false

let defer_to_ocaml ~expected ~actual = host_owned expected || host_owned actual

type assignability =
  | Equal
  | Unknown
  | Row_compatible
  | Deferred_to_ocaml
  | Incompatible

type assignability_policy = Nominal | Structural | Host_boundary

let classify_assignability ~expected ~actual =
  match (expected, actual) with
  | TUnknown, _ | _, TUnknown | TMeta _, _ | _, TMeta _ | TVar _, _
  | _, TVar _ ->
      Unknown
  | _ ->
      if equal expected actual then Equal
      else if
        row_compatible ~expected ~actual || row_compatible ~expected:actual ~actual:expected
      then Row_compatible
      else if defer_to_ocaml ~expected ~actual then Deferred_to_ocaml
      else Incompatible

let rec assignable ~policy ~expected ~actual =
  match (expected, actual) with
  | TPoly_variant expected, TPoly_variant actual ->
      Variant_row.compatible_payloads (fun expected actual -> assignable ~policy ~expected ~actual) expected actual
  | expected, actual when is_dynamic expected <> is_dynamic actual -> false
  | expected, actual
    when Option.is_some (static_unary_constraint_value expected) ->
      assignable ~policy
        ~expected:(Option.get (static_unary_constraint_value expected))
        ~actual:
          (Option.value (static_unary_constraint_value actual) ~default:actual)
  | expected, actual
    when Option.is_some (static_unary_constraint_value actual) ->
      assignable ~policy ~expected
        ~actual:(Option.get (static_unary_constraint_value actual))
  | TNullable _, TNil -> true
  | TNullable expected, TNullable actual ->
      assignable ~policy ~expected ~actual
  | TNullable expected, actual ->
      assignable ~policy ~expected ~actual
  | TVector expected, TVector actual
  | TList expected, TList actual
  | TSet expected, TSet actual
  | TSeq expected, TSeq actual ->
      assignable ~policy ~expected ~actual
  | TSeq expected, TCompiler (Next_seq actual | Reversible_next_seq actual)
  | TCompiler (Next_seq expected | Reversible_next_seq expected), TSeq actual
    ->
      assignable ~policy ~expected ~actual
  | TNamed_record expected, TNamed_record actual
    when expected.type_name = actual.type_name ->
      equal (TNamed_record expected) (TNamed_record actual)
      ||
      (policy = Host_boundary
      && not expected.nominal
      && not actual.nominal)
  | TNamed_record expected, TRecord actual when policy = Host_boundary ->
      let extensible =
        List.exists
          (fun field -> field.keyword = record_extension_keyword)
          expected.fields
      in
      List.for_all
        (fun actual_field ->
          extensible
          || List.exists
               (fun expected_field ->
                 expected_field.keyword = actual_field.keyword)
               expected.fields)
        actual
  | TRecord expected, TNamed_record actual when policy = Host_boundary ->
      let extensible =
        List.exists
          (fun field -> field.keyword = record_extension_keyword)
          actual.fields
      in
      List.for_all
        (fun expected_field ->
          extensible
          || List.exists
               (fun actual_field ->
                 actual_field.keyword = expected_field.keyword)
               actual.fields)
        expected
  | TFn (expected_params, expected_return), TFn (actual_params, actual_return)
    when List.length expected_params = List.length actual_params ->
      List.for_all2
        (fun expected actual -> assignable ~policy ~expected ~actual)
        expected_params actual_params
      && assignable ~policy ~expected:expected_return ~actual:actual_return
  | _ -> (
      match classify_assignability ~expected ~actual with
      | Equal -> true
      | Unknown -> policy = Host_boundary
      | Row_compatible -> policy = Structural || policy = Host_boundary
      | Deferred_to_ocaml -> policy = Host_boundary
      | Incompatible -> false)

let rec source_name = function
  | TPoly_variant row ->
      (match row.bound with Exact_row -> "variant" | Lower_row -> "variant-open" | Upper_row -> "variant-upper" | Bounded_row tags -> "variant-required(" ^ String.concat "," tags ^ ")")
      ^ "<" ^ String.concat ";" (List.map (fun (tag, payload) ->
        tag ^ Option.fold ~none:"" ~some:(fun ty -> ":" ^ source_name ty) payload) row.tags) ^ ">"
  | TCompiler (Module_package signature) -> "module<" ^ signature ^ ">"
  | TInt -> "int"
  | TFloat -> "float"
  | TChar -> "char"
  | TString -> "string"
  | TRegex -> "regex"
  | TMap_keys -> "map"
  | TSymbol -> "symbol"
  | TKeyword -> "keyword"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TNil -> "nil"
  | TNullable inner -> "option<" ^ source_name inner ^ ">"
  | TUnknown -> "any"
  | TMeta _ -> "inference-variable"
  | TVar name -> "param/" ^ name
  | TOcaml name -> name
  | TConstraint (Seqable_constraint { element; _ }) ->
      "seqable<" ^ source_name element ^ ">"
  | TConstraint (Contains_constraint { key; _ }) ->
      "contains<" ^ source_name key ^ ">"
  | TConstraint (Open_boundary_constraint capability) ->
      "dynamic<" ^ source_name capability ^ ">"
  | TConstraint (Truthy_constraint value_ty) ->
      "truthy<" ^ source_name value_ty ^ ">"
  | TConstraint (Nil_predicate_constraint value_ty) ->
      "nil-predicate<" ^ source_name value_ty ^ ">"
  | TConstraint (Printable_constraint value_ty) ->
      "printable<" ^ source_name value_ty ^ ">"
  | TConstraint (Exception_data_constraint value_ty) ->
      "exception-data<" ^ source_name value_ty ^ ">"
  | TConstraint (Hashable_constraint value_ty) ->
      "hashable<" ^ source_name value_ty ^ ">"
  | TConstraint (Comparable_constraint value_ty) ->
      "comparable<" ^ source_name value_ty ^ ">"
  | TConstraint (Array_index_constraint value_ty) ->
      "array-index<" ^ source_name value_ty ^ ">"
  | TConstraint (Symbol_predicate_constraint value_ty) ->
      "symbol-predicate<" ^ source_name value_ty ^ ">"
  | (TConstraint (Protocol_constraint _) as ty)
    when Option.is_some (sorted_constraint_info ty) ->
      let entry_ty, key_ty, value_ty = Option.get (sorted_constraint_info ty) in
      "sorted<" ^ source_name entry_ty ^ ";" ^ source_name key_ty ^ ";"
      ^ source_name value_ty ^ ">"
  | TConstraint
      (Protocol_constraint { protocol_id; value = value_ty; guarded; _ }) ->
      let protocol_name = Protocol_id.to_string protocol_id in
      let prefix = if guarded then "optional-protocol" else "protocol" in
      prefix ^ "<" ^ protocol_name ^ ";" ^ source_name value_ty ^ ">"
  | TOcaml_app (name, [ inner ]) when name = weak_type_name ->
      "weak<" ^ source_name inner ^ ">"
  | TCompiler (Next_seq inner | Reversible_next_seq inner) ->
      "seq<" ^ source_name inner ^ ">"
  | TCompiler marker -> source_name_compiler_marker marker
  | TOcaml_app (name, [ inner ]) when is_next_seq_type_name name ->
      "seq<" ^ source_name inner ^ ">"
  | TOcaml_app (name, [ inner ]) when name = reduced_type_name ->
      "reduced<" ^ source_name inner ^ ">"
  | TOcaml_app (name, args) ->
      name ^ "<"
      ^ (args |> List.map source_name |> String.concat ",")
      ^ ">"
  | TTuple args ->
      "tuple<" ^ (args |> List.map source_name |> String.concat ",") ^ ">"
  | TArray inner -> "array<" ^ source_name inner ^ ">"
  | TRef inner -> "ref<" ^ source_name inner ^ ">"
  | TList ty -> "list<" ^ source_name ty ^ ">"
  | TVector ty -> "vector<" ^ source_name ty ^ ">"
  | TSet ty -> "set<" ^ source_name ty ^ ">"
  | TSeq ty -> "seq<" ^ source_name ty ^ ">"
  | TFn (args, ret) ->
      "fn<(" ^ (args |> List.map source_name |> String.concat ", ") ^ ") -> "
      ^ source_name ret ^ ">"
  | TOverloaded_fn arities ->
      "fn<"
      ^ (arities
        |> List.map (fun arity ->
               let fixed = List.map source_name arity.fixed_params in
               let params =
                 match arity.rest_param with
                 | None -> fixed
                 | Some rest -> fixed @ [ "& " ^ source_name rest ]
               in
               "(" ^ String.concat ", " params ^ ") -> "
               ^ source_name arity.return_ty)
        |> String.concat "; ")
      ^ ">"
  | TRecord fields ->
      let field_name (field : field) =
        field.keyword ^ ":" ^ source_name field.ty
      in
      "record<{" ^ String.concat "," (List.map field_name fields) ^ "}>"
  | TNamed_record record when not record.nominal ->
      source_name (TRecord record.fields)
  | TNamed_record record ->
      record.type_name
      ^
      match record.type_arguments with
      | [] -> ""
      | arguments ->
          "<" ^ String.concat "," (List.map source_name arguments) ^ ">"

and source_name_compiler_marker = function
  | Module_package signature -> "module<" ^ signature ^ ">"
  | Constant_function inner ->
      constant_function_name ^ "<" ^ source_name inner ^ ">"
  | Reify_self_method inner ->
      reify_self_method_name ^ "<" ^ source_name inner ^ ">"
  | Reify_protocol_payload (id, methods, rest) ->
      reify_protocol_payload_prefix ^ id ^ "<" ^ source_name methods ^ ","
      ^ source_name rest ^ ">"
  | Next_seq inner | Reversible_next_seq inner ->
      "seq<" ^ source_name inner ^ ">"
  | Maybe_reduced_callback inner ->
      "maybe-reduced<" ^ source_name inner ^ ">"
  | Optional_map_adapter (key_ty, value_ty) ->
      optional_map_adapter_type_name ^ "<" ^ source_name key_ty ^ ","
      ^ source_name value_ty ^ ">"
  | Named_record_marker name -> record_marker_prefix ^ name
  | Named_record_app_marker (name, args) ->
      record_app_marker_prefix ^ name ^ "<"
      ^ (args |> List.map source_name |> String.concat ",")
      ^ ">"
  | Protocol_marker -> "__lg_protocol_marker"
  | Date_millis -> "__lg_date_millis"

let rec diagnostic_type_term = function
  | TInt -> Error.Type_atom "int"
  | TFloat -> Error.Type_atom "float"
  | TChar -> Error.Type_atom "char"
  | TString -> Error.Type_atom "string"
  | TRegex -> Error.Type_atom "regex"
  | TMap_keys -> Error.Type_atom "map"
  | TSymbol -> Error.Type_atom "symbol"
  | TKeyword -> Error.Type_atom "keyword"
  | TBool -> Error.Type_atom "bool"
  | TUnit -> Error.Type_atom "unit"
  | TNil -> Error.Type_atom "nil"
  | TUnknown -> Error.Type_atom "any"
  | TMeta _ -> Error.Type_atom "inference-variable"
  | TVar name -> Error.Type_atom ("param/" ^ name)
  | TOcaml name -> Error.Type_atom name
  | TNullable inner ->
      Error.Type_application ("option", [ diagnostic_type_term inner ])
  | TCompiler marker -> diagnostic_compiler_marker_term marker
  | TOcaml_app (name, arguments) ->
      Error.Type_application (name, List.map diagnostic_type_term arguments)
  | TTuple items -> Error.Type_tuple (List.map diagnostic_type_term items)
  | TArray inner ->
      Error.Type_application ("array", [ diagnostic_type_term inner ])
  | TRef inner -> Error.Type_application ("ref", [ diagnostic_type_term inner ])
  | TList inner ->
      Error.Type_application ("list", [ diagnostic_type_term inner ])
  | TVector inner ->
      Error.Type_application ("vector", [ diagnostic_type_term inner ])
  | TSet inner -> Error.Type_application ("set", [ diagnostic_type_term inner ])
  | TSeq inner -> Error.Type_application ("seq", [ diagnostic_type_term inner ])
  | TFn (parameters, return_type) ->
      Error.Type_function
        (List.map diagnostic_type_term parameters, diagnostic_type_term return_type)
  | TRecord fields ->
      Error.Type_record
        (List.map
           (fun (field : field) ->
             (field.keyword, diagnostic_type_term field.ty))
           fields)
  | TNamed_record record ->
      Error.Type_application
        (record.type_name, List.map diagnostic_type_term record.type_arguments)
  | (TPoly_variant _ | TConstraint _ | TOverloaded_fn _) as ty -> Error.Type_atom (source_name ty)

and diagnostic_compiler_marker_term = function
  | Module_package signature ->
      Error.Type_application (module_package_name, [ Error.Type_atom signature ])
  | Constant_function inner ->
      Error.Type_application
        (constant_function_name, [ diagnostic_type_term inner ])
  | Reify_self_method inner ->
      Error.Type_application
        (reify_self_method_name, [ diagnostic_type_term inner ])
  | Reify_protocol_payload (id, methods, rest) ->
      Error.Type_application
        ( reify_protocol_payload_prefix ^ id,
          [ diagnostic_type_term methods; diagnostic_type_term rest ] )
  | Next_seq inner ->
      Error.Type_application
        (next_seq_type_name, [ diagnostic_type_term inner ])
  | Reversible_next_seq inner ->
      Error.Type_application
        (reversible_next_seq_type_name, [ diagnostic_type_term inner ])
  | Maybe_reduced_callback inner ->
      Error.Type_application
        (maybe_reduced_callback_type_name, [ diagnostic_type_term inner ])
  | Optional_map_adapter (key_ty, value_ty) ->
      Error.Type_application
        ( optional_map_adapter_type_name,
          [ diagnostic_type_term key_ty; diagnostic_type_term value_ty ] )
  | Named_record_marker name -> Error.Type_atom (record_marker_prefix ^ name)
  | Named_record_app_marker (name, args) ->
      Error.Type_application
        ( record_app_marker_prefix ^ name,
          List.map diagnostic_type_term args )
  | Protocol_marker -> Error.Type_atom "__lg_protocol_marker"
  | Date_millis -> Error.Type_atom "__lg_date_millis"

let ocaml_record_type_name name =
  let local_name separator name =
    match String.rindex_opt name separator with
    | Some index when index < String.length name - 1 ->
        String.sub name (index + 1) (String.length name - index - 1)
    | _ -> name
  in
  if String.contains name ':' || String.contains name '/' then
    name |> local_name ':' |> local_name '/' |> String.uncapitalize_ascii
  else name

let rec ocaml_name = function
  | TPoly_variant row ->
      (match row.bound with Exact_row -> "[ " | Lower_row -> "[> " | Upper_row | Bounded_row _ -> "[< ")
      ^ String.concat " | " (List.map (fun (tag, payload) ->
        "`" ^ tag ^ Option.fold ~none:"" ~some:(fun ty -> " of " ^ ocaml_name ty) payload) row.tags) ^ (match row.bound with Bounded_row tags -> " > " ^ String.concat " " (List.map (fun tag -> "`" ^ tag) tags) | _ -> "") ^ " ]"
  | TCompiler (Module_package signature) -> "(module " ^ signature ^ ")"
  | TOcaml_app (name, [TOcaml signature]) when name = module_package_name ->
      "(module " ^ signature ^ ")"
  | TInt -> "int"
  | TFloat -> "float"
  | TChar -> "char"
  | TString -> "string"
  | TRegex -> "string"
  | TMap_keys -> "string Lg_runtime.Core_set.String_set.t"
  | TSymbol -> "string"
  | TKeyword -> "string"
  | TBool -> "bool"
  | TUnit -> "unit"
  | TNil -> "'a option"
  | TNullable inner -> ocaml_type_argument_name inner ^ " option"
  | TUnknown -> "'a"
  | TMeta _ -> "_"
  | TVar name -> "'" ^ name
  | TCompiler (Named_record_marker name) -> (
      match String.rindex_opt name '/' with
      | Some index ->
          let owner = String.sub name 0 index in
          let local_name =
            String.sub name (index + 1) (String.length name - index - 1)
          in
          Names.ocaml_binding_name owner local_name
      | None -> Names.sanitize_name name)
  | TOcaml name when String.starts_with ~prefix:record_marker_prefix name ->
      let source_name =
        String.sub name
          (String.length record_marker_prefix)
          (String.length name - String.length record_marker_prefix)
      in
      (match String.rindex_opt source_name '/' with
      | Some index ->
          let owner = String.sub source_name 0 index in
          let local_name =
            String.sub source_name (index + 1)
              (String.length source_name - index - 1)
          in
          Names.ocaml_binding_name owner local_name
      | None -> Names.sanitize_name source_name)
  | TOcaml name -> name
  | TOcaml_app (name, []) -> name
  | TConstraint (Open_boundary_constraint _) ->
      "Lg_runtime.Runtime_dynamic.t"
  | TConstraint (Truthy_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> bool) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Nil_predicate_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> bool) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Printable_constraint value_ty) ->
      "(((" ^ ocaml_name value_ty ^ " -> string) * ("
      ^ ocaml_name value_ty ^ " -> string)) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Exception_data_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> Lg_edn_backend.t) * "
      ^ ocaml_name value_ty ^ ")"
  | TConstraint (Hashable_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> int) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Comparable_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> " ^ ocaml_name value_ty
      ^ " -> int) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Array_index_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> int) * " ^ ocaml_name value_ty ^ ")"
  | TConstraint (Symbol_predicate_constraint value_ty) ->
      "((" ^ ocaml_name value_ty ^ " -> string option) * "
      ^ ocaml_name value_ty ^ ")"
  | TConstraint
      (Seqable_constraint { requirement = Required; element; storage }) ->
      "((" ^ ocaml_name (constraint_value_type storage) ^ " -> "
      ^ ocaml_name element ^ " Seq.t) * " ^ ocaml_name storage ^ ")"
  | TConstraint (Contains_constraint { key; storage }) ->
      "((" ^ ocaml_name key ^ " -> bool) * " ^ ocaml_name storage ^ ")"
  | TConstraint
      (Seqable_constraint
        { requirement = (Optional | Optional_sequential); element; storage }) ->
      "((" ^ ocaml_name (constraint_value_type storage) ^ " -> "
      ^ ocaml_name element ^ " Seq.t) option * " ^ ocaml_name storage ^ ")"
  | TConstraint (Protocol_constraint { witness; value; _ }) ->
      "(" ^ ocaml_name witness ^ " option * " ^ ocaml_name value ^ ")"
  | TCompiler (Reify_self_method method_ty) -> ocaml_name method_ty
  | TCompiler (Reify_protocol_payload (_, methods, rest)) ->
      ocaml_name (TTuple [ methods; rest ])
  | TCompiler (Next_seq inner | Reversible_next_seq inner) ->
      ocaml_name inner ^ " Seq.t"
  | TCompiler (Maybe_reduced_callback inner) ->
      ocaml_name (reduced inner)
  | TCompiler marker -> ocaml_compiler_marker_name marker
  | TOcaml_app (name, [ inner ]) when is_next_seq_type_name name ->
      ocaml_name inner ^ " Seq.t"
  | TOcaml_app (name, [ arg ]) ->
      let arg_name =
        match arg with
        | TFn _ -> "(" ^ ocaml_name arg ^ ")"
        | _ -> ocaml_name arg
      in
      arg_name ^ " " ^ name
  | TOcaml_app (name, args) ->
      "(" ^ (args |> List.map ocaml_name |> String.concat ", ") ^ ") " ^ name
  | TTuple args ->
      let tuple_item ty =
        match ty with
        | TFn _ -> "(" ^ ocaml_name ty ^ ")"
        | _ -> ocaml_name ty
      in
      "(" ^ (args |> List.map tuple_item |> String.concat " * ") ^ ")"
  | TArray inner -> ocaml_type_argument_name inner ^ " array"
  | TRef inner -> ocaml_type_argument_name inner ^ " Lg_runtime.Runtime_reference.t"
  | TList inner -> ocaml_type_argument_name inner ^ " list"
  | TVector inner -> ocaml_type_argument_name inner ^ " Rrbvec.t"
  | TSet inner -> (
      match set_module_name inner with
      | Ok "Lg_runtime.Runtime_poly_set" ->
          ocaml_name inner ^ " Lg_runtime.Runtime_poly_set.t"
      | Ok "Lg_runtime.Runtime_map_set" -> (
          match inner with
          | TOcaml_app ("Lg_runtime.Runtime_map.t", [ key; value ]) ->
              "(" ^ ocaml_name key ^ ", " ^ ocaml_name value
              ^ ") Lg_runtime.Runtime_map_set.t"
          | TRecord fields -> (
              match homogeneous_record_value_type fields with
              | Some value ->
                  "(" ^ ocaml_name TKeyword ^ ", " ^ ocaml_name value
                  ^ ") Lg_runtime.Runtime_map_set.t"
              | None -> assert false)
          | _ -> assert false)
      | Ok set_module -> set_module ^ ".t"
      | Error _ -> "unsupported_set<" ^ ocaml_name inner ^ ">")
  | TSeq inner -> ocaml_type_argument_name inner ^ " Seq.t"
  | TFn ([], ret) -> "unit -> " ^ ocaml_name ret
  | TFn (args, ret) ->
      let argument_name = function
        | TFn _ as argument -> "(" ^ ocaml_name argument ^ ")"
        | argument -> ocaml_name argument
      in
      (args |> List.map argument_name |> String.concat " -> ")
      ^ " -> " ^ ocaml_name ret
  | TOverloaded_fn arities -> ocaml_name (overloaded_storage_type arities)
  | TRecord fields -> (
      match homogeneous_record_value_type fields with
      | Some value_ty -> ocaml_name (dynamic_map TKeyword value_ty)
      | None -> "record")
  | TNamed_record record -> (
      let type_name = ocaml_record_type_name record.type_name in
      match record.type_arguments with
      | [] -> type_name
      | [ argument ] -> ocaml_type_argument_name argument ^ " " ^ type_name
      | arguments ->
          "("
          ^ String.concat ", " (List.map ocaml_name arguments)
          ^ ") " ^ type_name)

and ocaml_type_argument_name = function
  | TFn _ as ty -> "(" ^ ocaml_name ty ^ ")"
  | ty -> ocaml_name ty

and ocaml_compiler_marker_name = function
  | Module_package signature -> "(module " ^ signature ^ ")"
  | Constant_function inner ->
      ocaml_type_argument_name inner ^ " " ^ constant_function_name
  | Reify_self_method inner -> ocaml_name inner
  | Reify_protocol_payload (_, methods, rest) ->
      ocaml_name (TTuple [ methods; rest ])
  | Next_seq inner | Reversible_next_seq inner -> ocaml_name inner ^ " Seq.t"
  | Maybe_reduced_callback inner -> ocaml_name (reduced inner)
  | Optional_map_adapter (key_ty, value_ty) ->
      "(" ^ ocaml_name key_ty ^ ", " ^ ocaml_name value_ty ^ ") "
      ^ optional_map_adapter_type_name
  | Named_record_app_marker (name, args) -> (
      let rendered_name = ocaml_name (TOcaml name) in
      match args with
      | [] -> rendered_name
      | [ argument ] ->
          ocaml_type_argument_name argument ^ " " ^ rendered_name
      | arguments ->
          "("
          ^ String.concat ", " (List.map ocaml_name arguments)
          ^ ") " ^ rendered_name)
  | Named_record_marker name -> (
      match String.rindex_opt name '/' with
      | Some index ->
          let owner = String.sub name 0 index in
          let local_name =
            String.sub name (index + 1) (String.length name - index - 1)
          in
          Names.ocaml_binding_name owner local_name
      | None -> Names.sanitize_name name)
  | Protocol_marker -> "__lg_protocol_marker"
  | Date_millis -> "__lg_date_millis"

and overloaded_storage_type = function
  | [] -> TUnit
  | arity :: rest ->
      let params =
        match arity.rest_param with
        | None -> arity.fixed_params
        | Some rest_ty -> arity.fixed_params @ [ TSeq rest_ty ]
      in
      TTuple [ TFn (params, arity.return_ty); overloaded_storage_type rest ]

and closed_generated_set_element = function
  | TInt | TFloat | TChar | TString | TRegex | TSymbol | TKeyword | TBool
  | TUnit | TNil | TOcaml "int" | TOcaml "Lg_edn_backend.t" ->
      true
  | TNullable inner | TList inner | TVector inner | TArray inner
  | TOcaml_app ("option", [ inner ]) ->
      closed_generated_set_element inner
  | TTuple items -> List.for_all closed_generated_set_element items
  | _ -> false

and generated_set_module_name ty =
  "Lg_static_set_"
  ^ String.sub (Digest.to_hex (Digest.string (source_name ty))) 0 16

and set_module_name = function
  | TUnknown | TMeta _ | TVar _ -> Ok "Lg_runtime.Runtime_poly_set"
  | TNil -> Ok "Lg_runtime.Runtime_poly_set"
  | TInt -> Ok "Lg_runtime.Core_set.Int_set"
  | TFloat -> Ok "Lg_runtime.Core_set.Float_set"
  | TChar -> Ok "Lg_runtime.Core_set.Char_set"
  | TString | TSymbol | TKeyword -> Ok "Lg_runtime.Core_set.String_set"
  | TBool -> Ok "Lg_runtime.Core_set.Bool_set"
  | TList TInt -> Ok "Lg_runtime.Core_set.Int_list_set"
  | TList TFloat -> Ok "Lg_runtime.Core_set.Float_list_set"
  | TList TChar -> Ok "Lg_runtime.Core_set.Char_list_set"
  | TList (TString | TSymbol | TKeyword) -> Ok "Lg_runtime.Core_set.String_list_set"
  | TList TBool -> Ok "Lg_runtime.Core_set.Bool_list_set"
  | TList (TUnknown | TMeta _ | TVar _) -> Ok "Lg_runtime.Runtime_poly_set"
  | TList inner as ty when closed_generated_set_element inner ->
      Ok (generated_set_module_name ty)
  | TVector TInt -> Ok "Lg_runtime.Core_set.Int_vector_set"
  | TVector TFloat -> Ok "Lg_runtime.Core_set.Float_vector_set"
  | TVector TChar -> Ok "Lg_runtime.Core_set.Char_vector_set"
  | TVector (TString | TSymbol | TKeyword) ->
      Ok "Lg_runtime.Core_set.String_vector_set"
  | TVector TBool -> Ok "Lg_runtime.Core_set.Bool_vector_set"
  | TVector (TUnknown | TMeta _ | TVar _) -> Ok "Lg_runtime.Runtime_poly_set"
  | TVector (TOcaml "Lg_edn_backend.t") -> Ok "Lg_runtime.Runtime_poly_set"
  | TSeq _ -> Ok "Lg_runtime.Runtime_seq_set"
  | TCompiler (Next_seq _ | Reversible_next_seq _) ->
      Ok "Lg_runtime.Runtime_seq_set"
  | TOcaml_app (name, [ _ ]) when is_next_seq_type_name name ->
      Ok "Lg_runtime.Runtime_seq_set"
  | ty when Option.is_some (seqable_constraint_info ty) ->
      Ok "Lg_runtime.Runtime_poly_set"
  | TSet (TUnknown | TMeta _ | TVar _) -> Ok "Lg_runtime.Runtime_poly_set"
  | TVector (TVector TInt) -> Ok "Lg_runtime.Core_set.Int_vector_vector_set"
  | TVector (TRecord _) -> Ok "Lg_runtime.Runtime_poly_set"
  | TVector (TNamed_record { nominal = false; _ }) ->
      Ok "Lg_runtime.Runtime_poly_set"
  | TVector (TVector (TString | TSymbol | TKeyword)) ->
      Ok "Lg_runtime.Runtime_poly_set"
  | TVector (TVector (TRecord _)) -> Ok "Lg_runtime.Runtime_poly_set"
  | TVector inner as ty when closed_generated_set_element inner ->
      Ok (generated_set_module_name ty)
  | TList (TRecord _) -> Ok "Lg_runtime.Runtime_poly_set"
  | TTuple items as ty when List.for_all closed_generated_set_element items ->
      Ok (generated_set_module_name ty)
  | TRecord fields when is_homogeneous_record fields ->
      Ok "Lg_runtime.Runtime_map_set"
  | TRecord _ -> Ok "Lg_runtime.Runtime_poly_set"
  | TOcaml_app ("Lg_runtime.Runtime_map.t", [ _key; _value ]) ->
      Ok "Lg_runtime.Runtime_map_set"
  | TOcaml "int" -> Ok "Lg_runtime.Core_set.Int_set"
  | TCompiler _ -> Ok "Lg_runtime.Runtime_poly_set"
  | TOcaml _ -> Ok "Lg_runtime.Runtime_poly_set"
  | TNamed_record { nominal = false; _ } -> Ok "Lg_runtime.Runtime_poly_set"
  | TNullable (TNamed_record record)
  | TOcaml_app ("option", [ TNamed_record record ]) ->
      Ok (record.set_module_name ^ "_nullable")
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      Result.map
        (fun _ -> "Lg_runtime.Runtime_poly_set")
        (set_module_name inner)
  | TNamed_record record -> Ok record.set_module_name
  | ty -> Error.error ~code:Error_code.Semantic ("sets require a generated comparator for " ^ source_name ty)

let record_fields = function
  | TRecord fields -> Some fields
  | TNamed_record record ->
      let fields =
        if
          record.type_parameters <> []
          && List.length record.type_parameters
          = List.length record.type_arguments
          && not (List.for_all2
                    (fun parameter -> function
                      | TVar name -> String.equal parameter name
                      | _ -> false)
                    record.type_parameters record.type_arguments)
        then
          let substitutions =
            Type_solver.of_list
              (List.map2
              (fun parameter argument ->
                (Type_solver.Declared parameter, argument))
              record.type_parameters record.type_arguments)
          in
          Type_solver.map_preserving_identity
            (fun (field : field) ->
              let ty = Type_solver.apply substitutions field.ty in
              if ty == field.ty then field else { field with ty })
            record.fields
        else record.fields
      in
      Some fields
  | _ -> None

let type_id_of_name type_name =
  match List.rev (String.split_on_char '.' type_name) with
  | [] -> Type_id.create ~owner:[] ~name:type_name
  | name :: owner -> Type_id.create ~owner:(List.rev owner) ~name

let named_record ?(type_parameters = []) ?type_id ?(nominal = false)
    ?(extensible = false) ~type_name ~set_module_name fields =
  let type_id = Option.value type_id ~default:(type_id_of_name type_name) in
  TNamed_record
    {
      type_id;
      nominal;
      extensible;
      type_name;
      type_parameters;
      type_arguments = List.map (fun parameter -> TVar parameter) type_parameters;
      set_module_name;
      fields;
    }

let nominal_tag_name (record : named_record) =
  match String.rindex_opt record.type_name '.' with
  | None -> "Lg_nominal_" ^ record.type_name
  | Some separator ->
      let module_path = String.sub record.type_name 0 separator in
      let local_name =
        String.sub record.type_name (separator + 1)
          (String.length record.type_name - separator - 1)
      in
      module_path ^ ".Lg_nominal_" ^ local_name

let rec qualify_module_type module_path ty =
  let qualify_name name =
    if String.contains name '.' then name else module_path ^ "." ^ name
  in
  match ty with
  | TPoly_variant _ -> Semantic_type.map_children (qualify_module_type module_path) ty
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _ ->
      ty
  | TNullable inner -> TNullable (qualify_module_type module_path inner)
  | TCompiler marker ->
      TCompiler
        (Semantic_type.map_compiler_marker
           (qualify_module_type module_path) marker)
  | TOcaml_app (name, args) ->
      TOcaml_app (name, List.map (qualify_module_type module_path) args)
  | TConstraint constraint_ ->
      TConstraint (map_constraint (qualify_module_type module_path) constraint_)
  | TTuple args -> TTuple (List.map (qualify_module_type module_path) args)
  | TArray inner -> TArray (qualify_module_type module_path inner)
  | TRef inner -> TRef (qualify_module_type module_path inner)
  | TList inner -> TList (qualify_module_type module_path inner)
  | TVector inner -> TVector (qualify_module_type module_path inner)
  | TSet inner -> TSet (qualify_module_type module_path inner)
  | TSeq inner -> TSeq (qualify_module_type module_path inner)
  | TFn (args, ret) ->
      TFn
        ( List.map (qualify_module_type module_path) args,
          qualify_module_type module_path ret )
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             { fixed_params =
                 List.map (qualify_module_type module_path) arity.fixed_params;
               rest_param = Option.map (qualify_module_type module_path) arity.rest_param;
               return_ty = qualify_module_type module_path arity.return_ty })
           arities)
  | TRecord fields ->
      TRecord
        (List.map
           (fun (field : field) ->
             { field with ty = qualify_module_type module_path field.ty })
           fields)
  | TNamed_record record ->
      let type_name = qualify_name record.type_name in
      TNamed_record
        { type_id = record.type_id;
          nominal = record.nominal;
          extensible = record.extensible;
          type_name;
          type_parameters = record.type_parameters;
          type_arguments =
            List.map (qualify_module_type module_path) record.type_arguments;
          set_module_name = qualify_name record.set_module_name;
          fields =
            List.map
              (fun (field : field) ->
                { field with ty = qualify_module_type module_path field.ty })
              record.fields }

let rec remap_module_type ~from_path ~to_path ty =
  let remap_name name =
    if name = from_path then to_path
    else
      let prefix = from_path ^ "." in
      if String.starts_with ~prefix name then
        to_path ^ String.sub name (String.length from_path)
          (String.length name - String.length from_path)
      else name
  in
  let remap_type_id type_id =
    match Type_id.owner type_id with
    | [ owner ] ->
        Type_id.create ~owner:[ remap_name owner ] ~name:(Type_id.name type_id)
    | _ -> type_id
  in
  match ty with
  | TPoly_variant _ -> Semantic_type.map_children (remap_module_type ~from_path ~to_path) ty
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ ->
      ty
  | TOcaml name -> TOcaml (remap_name name)
  | TNullable inner ->
      TNullable (remap_module_type ~from_path ~to_path inner)
  | TCompiler marker ->
      TCompiler
        (Semantic_type.map_compiler_marker
           (remap_module_type ~from_path ~to_path) marker)
  | TOcaml_app (name, args) ->
      TOcaml_app (remap_name name, List.map (remap_module_type ~from_path ~to_path) args)
  | TConstraint constraint_ ->
      TConstraint
        (map_constraint (remap_module_type ~from_path ~to_path) constraint_)
  | TTuple args -> TTuple (List.map (remap_module_type ~from_path ~to_path) args)
  | TArray inner -> TArray (remap_module_type ~from_path ~to_path inner)
  | TRef inner -> TRef (remap_module_type ~from_path ~to_path inner)
  | TList inner -> TList (remap_module_type ~from_path ~to_path inner)
  | TVector inner -> TVector (remap_module_type ~from_path ~to_path inner)
  | TSet inner -> TSet (remap_module_type ~from_path ~to_path inner)
  | TSeq inner -> TSeq (remap_module_type ~from_path ~to_path inner)
  | TFn (args, ret) ->
      TFn
        ( List.map (remap_module_type ~from_path ~to_path) args,
          remap_module_type ~from_path ~to_path ret )
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             { fixed_params =
                 List.map (remap_module_type ~from_path ~to_path) arity.fixed_params;
               rest_param =
                 Option.map (remap_module_type ~from_path ~to_path) arity.rest_param;
               return_ty =
                 remap_module_type ~from_path ~to_path arity.return_ty })
           arities)
  | TRecord fields ->
      TRecord
        (List.map
           (fun (field : field) ->
             { field with ty = remap_module_type ~from_path ~to_path field.ty })
           fields)
  | TNamed_record record ->
      TNamed_record
        { record with
          type_id = remap_type_id record.type_id;
          type_name = remap_name record.type_name;
          set_module_name = remap_name record.set_module_name;
          fields =
            List.map
              (fun (field : field) ->
                { field with
                  ty = remap_module_type ~from_path ~to_path field.ty;
                })
              record.fields;
        }

let refresh_named_record (fresh : named_record) =
  (* One refresh can visit a shared type through many bindings and fields. *)
  (* A direct-mapped cache bounds lookup cost even when distinct type nodes
     have identical structural hashes. Collisions only cause recomputation. *)
  let refreshed = Array.make 64 None in
  let rec refresh ty =
    let slot = Hashtbl.hash ty land 63 in
    match refreshed.(slot) with
    | Some (original, mapped) when original == ty -> mapped
    | Some _ | None ->
        let mapped =
          match ty with
          | TNamed_record record when Type_id.equal record.type_id fresh.type_id ->
              if record == fresh then ty
              else if
                List.length record.type_arguments = List.length fresh.type_arguments
              then
                if record.fields == fresh.fields
                   && record.nominal = fresh.nominal
                   && record.extensible = fresh.extensible
                   && String.equal record.type_name fresh.type_name
                   && record.type_parameters = fresh.type_parameters
                   && String.equal record.set_module_name fresh.set_module_name
                then ty
                else
                  TNamed_record { fresh with type_arguments = record.type_arguments }
              else TNamed_record fresh
          | _ ->
              let changed = ref false in
              let mapped =
                Semantic_type.map_children
                  (fun child ->
                    let mapped = refresh child in
                    if mapped != child then changed := true;
                    mapped)
                  ty
              in
              if !changed then mapped else ty
        in
        refreshed.(slot) <- Some (ty, mapped);
        mapped
  in
  refresh

let find_field keyword fields =
  match List.find_opt (fun field -> field.keyword = keyword) fields with
  | Some _ as field -> field
  | None ->
      let name = Names.keyword_to_ocaml_name keyword in
      List.find_opt (fun field -> not field.runtime_map && field.ocaml_name = name) fields
let make_field ?location ?(quantified = []) ?(mutable_ = false) ?(runtime_map = false) keyword ty =
  {
    keyword;
    ocaml_name = Names.keyword_to_ocaml_name keyword;
    ty;
    quantified;
    mutable_;
    runtime_map;
    location;
  }

let make_map_field ?location keyword ty =
  make_field ?location ~runtime_map:true keyword ty

let make_record_extension_field ~ty () =
  make_field record_extension_keyword ty

let is_record_extension_field field =
  field.keyword = record_extension_keyword

let make_record_identity_field () =
  make_field record_identity_keyword (TOcaml_app ("ref", [ TUnit ]))

let is_record_identity_field field =
  field.keyword = record_identity_keyword

let is_static_record_source_field field =
  is_record_extension_field field
  && Option.is_none (dynamic_map_types field.ty)

let find_record_extension_field fields =
  List.find_opt is_record_extension_field fields

let record_constructor_fields fields =
  List.filter
    (fun field ->
      (not (is_record_extension_field field))
      && not (is_record_identity_field field))
    fields

type type_substitutions = Type_solver.substitutions

let infer_type_substitutions substitutions ~template ~actual =
  Type_solver.infer substitutions ~template ~actual
  |> Result.value ~default:substitutions

let infer_list_substitutions substitutions templates actuals =
  Type_solver.infer_all substitutions ~templates ~actuals
  |> Result.value ~default:substitutions

let substitute_type_variables = Type_solver.apply

let instantiate_type ~templates ~actuals ty =
  if List.length templates <> List.length actuals then ty
  else
    let substitutions =
      infer_list_substitutions Type_solver.empty templates actuals
    in
    substitute_type_variables substitutions ty

let instantiate_type_fields ~templates ~actuals ty =
  if List.length templates <> List.length actuals then ty
  else
    let rec inference_actual template actual =
      match (template, actual) with
      | (TUnknown | TMeta _ | TVar _), actual ->
          let payload = constraint_value_type actual in
          if equal payload actual then actual else payload
      | TFn (template_params, template_return),
        TFn (actual_params, actual_return)
        when List.length template_params = List.length actual_params ->
          TFn
            ( List.map2 inference_actual template_params actual_params,
              inference_actual template_return actual_return )
      | _ -> actual
    in
    let substitutions =
      List.fold_left2
        (fun substitutions template actual ->
          infer_type_substitutions substitutions ~template
            ~actual:(inference_actual template actual))
        Type_solver.empty templates actuals
    in
    let instantiated = substitute_type_variables substitutions ty in
    let rec refine_open_type template actual =
      match (template, actual) with
      | (TUnknown | TMeta _ | TVar _), actual -> actual
      | TNullable template, TNullable actual ->
          TNullable (refine_open_type template actual)
      | TNullable template, TOcaml_app ("option", [ actual ]) ->
          TNullable (refine_open_type template actual)
      | TOcaml_app ("option", [ template ]), TNullable actual
      | TOcaml_app ("option", [ template ]),
        TOcaml_app ("option", [ actual ]) ->
          TOcaml_app ("option", [ refine_open_type template actual ])
      | TArray template, TArray actual ->
          TArray (refine_open_type template actual)
      | TRef template, TRef actual -> TRef (refine_open_type template actual)
      | TList template, TList actual ->
          TList (refine_open_type template actual)
      | TVector template, TVector actual ->
          TVector (refine_open_type template actual)
      | TSet template, TSet actual -> TSet (refine_open_type template actual)
      | TSeq template, TSeq actual -> TSeq (refine_open_type template actual)
      | TOcaml_app (name, templates), TOcaml_app (actual_name, actuals)
        when name = actual_name && List.length templates = List.length actuals ->
          TOcaml_app (name, List.map2 refine_open_type templates actuals)
      | template, _ -> template
    in
    match instantiated with
    | TNamed_record record ->
        let rec refine_fields refined templates actuals = function
          | [] -> List.rev refined
          | field :: fields when is_record_extension_field field ->
              refine_fields (field :: refined) templates actuals fields
          | (field : field) :: fields -> (
              match (templates, actuals) with
              | template :: templates, actual :: actuals ->
                  let template = substitute_type_variables substitutions template in
                  let actual =
                    inference_actual template actual
                    |> substitute_type_variables substitutions
                  in
                  let field =
                    {
                      field with
                      ty = refine_open_type template actual;
                    }
                  in
                  refine_fields (field :: refined) templates actuals fields
              | [], [] -> List.rev_append refined (field :: fields)
              | _ -> List.rev_append refined (field :: fields))
        in
        TNamed_record
          {
            record with
            fields = refine_fields [] templates actuals record.fields;
          }
    | ty -> ty

let instantiate_receiver_method_type receiver_ty method_ty =
  let rec specialize_return value_ty = function
    | TSeq (TUnknown | TMeta _ | TVar _) -> TSeq value_ty
    | TOcaml_app (("Seq.t" | "Seq") as name, [ TUnknown | TMeta _ | TVar _ ]) ->
        TOcaml_app (name, [ value_ty ])
    | TNullable return_ty ->
        TNullable (specialize_return value_ty return_ty)
    | TOcaml_app ("option", [ return_ty ]) ->
        TOcaml_app ("option", [ specialize_return value_ty return_ty ])
    | return_ty -> return_ty
  in
  let template_receiver =
    match method_ty with
    | TFn (template_receiver :: _, _) -> Some template_receiver
    | TOverloaded_fn ({ fixed_params = template_receiver :: _; _ } :: _) ->
        Some template_receiver
    | TFn ([], _) | TOverloaded_fn []
    | TOverloaded_fn ({ fixed_params = []; _ } :: _) | _ ->
        None
  in
  match template_receiver with
  | Some template_receiver ->
      let receiver_value_ty =
        match template_receiver with
        | TNamed_record { type_parameters = [ parameter ]; _ } ->
            let substitutions =
              infer_type_substitutions Type_solver.empty
                ~template:template_receiver
                ~actual:receiver_ty
            in
            (match Type_solver.find_opt (Type_solver.Declared parameter) substitutions with
            | Some TUnknown | None -> None
            | Some ty -> Some ty)
        | template_receiver -> (
            match protocol_constraint_info template_receiver with
            | Some (_, _, TVar parameter) ->
                Some
                  (substitute_type_variables
                     (Type_solver.of_list
                        [ (Type_solver.Declared parameter, receiver_ty) ])
                     (TVar parameter))
            | Some _ | None -> None)
      in
      let method_ty =
        instantiate_type ~templates:[ template_receiver ]
          ~actuals:[ receiver_ty ] method_ty
      in
      (match (receiver_value_ty, method_ty) with
      | Some value_ty, TFn (receiver :: parameters, return_ty) ->
          TFn
            ( receiver
              :: List.map
                   (function TUnknown -> value_ty | ty -> ty)
                   parameters,
              specialize_return value_ty return_ty )
      | Some value_ty, TOverloaded_fn arities ->
          TOverloaded_fn
            (List.map
               (fun arity ->
                 match arity.fixed_params with
                 | receiver :: parameters ->
                     {
                       arity with
                       fixed_params =
                         receiver
                         :: List.map
                              (function TUnknown -> value_ty | ty -> ty)
                              parameters;
                       return_ty = specialize_return value_ty arity.return_ty;
                     }
                 | [] -> arity)
               arities)
      | _ -> method_ty)
  | None -> method_ty
let rec idents_in_conversion names = function
  | Semantic_ir.Ident name -> name :: names
  | Semantic_ir.Typed (_, value)
  | Semantic_ir.GadtScope value
  | Semantic_ir.Located (_, _, value)
  | Semantic_ir.SharedValue (_, value) ->
      idents_in_conversion names value
  | Semantic_ir.PolyTag (_, value) | Semantic_ir.Constructor (_, value) ->
      Option.fold ~none:names ~some:(idents_in_conversion names) value
  | Semantic_ir.Tuple values
  | Semantic_ir.List values
  | Semantic_ir.Array values
  | Semantic_ir.Sequence values ->
      List.fold_left idents_in_conversion names values
  | Semantic_ir.Apply (fn, args) | Semantic_ir.Uncurried_apply (fn, args) ->
      List.fold_left idents_in_conversion (idents_in_conversion names fn) args
  | Semantic_ir.Labelled_apply (fn, args) ->
      List.fold_left
        (fun names (_, value) -> idents_in_conversion names value)
        (idents_in_conversion names fn) args
  | Semantic_ir.If (condition, then_expr, else_expr) ->
      List.fold_left idents_in_conversion names
        [ condition; then_expr; else_expr ]
  | Semantic_ir.Fun (_, body) | Semantic_ir.Labelled_fun (_, body) -> idents_in_conversion names body
  | Semantic_ir.Let (bindings, body)
  | Semantic_ir.LetRecGroup (bindings, body) ->
      List.fold_left
        (fun names (_, value) -> idents_in_conversion names value)
        (idents_in_conversion names body) bindings
  | Semantic_ir.EvaluateOnce (_, value, body) ->
      idents_in_conversion
        (idents_in_conversion (idents_in_conversion names value) body)
        value
  | Semantic_ir.LetRec (_, _, body, args) ->
      List.fold_left idents_in_conversion (idents_in_conversion names body) args
  | Semantic_ir.PackModule _ -> names
  | Semantic_ir.UnpackModule (_, _, body, next)
  | Semantic_ir.LetRecIn (_, _, body, next) ->
      idents_in_conversion (idents_in_conversion names body) next
  | Semantic_ir.Match (target, cases) ->
      List.fold_left
        (fun names (_, value) -> idents_in_conversion names value)
        (idents_in_conversion names target)
        cases
  | Semantic_ir.Match_guarded (target, cases) ->
      List.fold_left
        (fun names (_, _, value) -> idents_in_conversion names value)
        (idents_in_conversion names target)
        cases
  | Semantic_ir.Try (body, cases) ->
      List.fold_left
        (fun names (_, _, handler) -> idents_in_conversion names handler)
        (idents_in_conversion names body) cases
  | Semantic_ir.Infix (_, left, right) | Semantic_ir.Cons (left, right) ->
      idents_in_conversion (idents_in_conversion names left) right
  | Semantic_ir.Prefix (_, value)
  | Semantic_ir.Constraint (value, _)
  | Semantic_ir.Field (value, _) ->
      idents_in_conversion names value
  | Semantic_ir.SetField (target, _, value) ->
      idents_in_conversion (idents_in_conversion names target) value
  | Semantic_ir.PackDynamic { conversion; _ }
  | Semantic_ir.UnpackDynamic { conversion; _ }
  | Semantic_ir.NullableToSeq { conversion; _ } ->
      idents_in_conversion names conversion
  | Semantic_ir.Record (fields, _) ->
      List.fold_left
        (fun names (_, value) -> idents_in_conversion names value)
        names fields
  | Semantic_ir.RecordUpdate (record, fields) ->
      List.fold_left
        (fun names (_, value) -> idents_in_conversion names value)
        (idents_in_conversion names record) fields
  | Semantic_ir.Int _ | Semantic_ir.Int64 _ | Semantic_ir.Float _ | Semantic_ir.String _
  | Semantic_ir.Char _ | Semantic_ir.Bool _ | Semantic_ir.Unit ->
      names

let rec dynamic_pinned_idents names = function
  | Semantic_ir.PackDynamic { conversion; _ } ->
      let names = idents_in_conversion names conversion in
      dynamic_pinned_idents names conversion
  | Semantic_ir.Typed (_, value)
  | Semantic_ir.GadtScope value
  | Semantic_ir.Located (_, _, value)
  | Semantic_ir.SharedValue (_, value) ->
      dynamic_pinned_idents names value
  | Semantic_ir.PolyTag (_, value) | Semantic_ir.Constructor (_, value) ->
      Option.fold ~none:names ~some:(dynamic_pinned_idents names) value
  | Semantic_ir.Tuple values
  | Semantic_ir.List values
  | Semantic_ir.Array values
  | Semantic_ir.Sequence values ->
      List.fold_left dynamic_pinned_idents names values
  | Semantic_ir.Apply (fn, args) | Semantic_ir.Uncurried_apply (fn, args) ->
      List.fold_left dynamic_pinned_idents
        (dynamic_pinned_idents names fn)
        args
  | Semantic_ir.Labelled_apply (fn, args) ->
      List.fold_left
        (fun names (_, value) -> dynamic_pinned_idents names value)
        (dynamic_pinned_idents names fn)
        args
  | Semantic_ir.If (condition, then_expr, else_expr) ->
      List.fold_left dynamic_pinned_idents names
        [ condition; then_expr; else_expr ]
  | Semantic_ir.Fun (_, body) | Semantic_ir.Labelled_fun (_, body) -> dynamic_pinned_idents names body
  | Semantic_ir.Let (bindings, body)
  | Semantic_ir.LetRecGroup (bindings, body) ->
      List.fold_left
        (fun names (_, value) -> dynamic_pinned_idents names value)
        (dynamic_pinned_idents names body)
        bindings
  | Semantic_ir.EvaluateOnce (_, value, body) ->
      dynamic_pinned_idents
        (dynamic_pinned_idents (dynamic_pinned_idents names value) body)
        value
  | Semantic_ir.LetRec (_, _, body, args) ->
      List.fold_left dynamic_pinned_idents
        (dynamic_pinned_idents names body)
        args
  | Semantic_ir.PackModule _ -> names
  | Semantic_ir.UnpackModule (_, _, body, next)
  | Semantic_ir.LetRecIn (_, _, body, next) ->
      dynamic_pinned_idents (dynamic_pinned_idents names body) next
  | Semantic_ir.Match (target, cases) ->
      List.fold_left
        (fun names (_, value) -> dynamic_pinned_idents names value)
        (dynamic_pinned_idents names target)
        cases
  | Semantic_ir.Match_guarded (target, cases) ->
      List.fold_left
        (fun names (_, _, value) -> dynamic_pinned_idents names value)
        (dynamic_pinned_idents names target)
        cases
  | Semantic_ir.Try (body, cases) ->
      List.fold_left
        (fun names (_, _, handler) -> dynamic_pinned_idents names handler)
        (dynamic_pinned_idents names body)
        cases
  | Semantic_ir.Infix (_, left, right) | Semantic_ir.Cons (left, right) ->
      dynamic_pinned_idents (dynamic_pinned_idents names left) right
  | Semantic_ir.Prefix (_, value)
  | Semantic_ir.Constraint (value, _)
  | Semantic_ir.Field (value, _) ->
      dynamic_pinned_idents names value
  | Semantic_ir.SetField (target, _, value) ->
      dynamic_pinned_idents (dynamic_pinned_idents names target) value
  | Semantic_ir.UnpackDynamic { conversion; _ }
  | Semantic_ir.NullableToSeq { conversion; _ } ->
      dynamic_pinned_idents names conversion
  | Semantic_ir.Record (fields, _) ->
      List.fold_left
        (fun names (_, value) -> dynamic_pinned_idents names value)
        names fields
  | Semantic_ir.RecordUpdate (record, fields) ->
      List.fold_left
        (fun names (_, value) -> dynamic_pinned_idents names value)
        (dynamic_pinned_idents names record) fields
  | Semantic_ir.Int _ | Semantic_ir.Int64 _ | Semantic_ir.Float _ | Semantic_ir.String _
  | Semantic_ir.Char _ | Semantic_ir.Bool _ | Semantic_ir.Unit
  | Semantic_ir.Ident _ ->
      names

let rec pattern_name = function
  | Semantic_ir.PVar name -> Some name
  | Semantic_ir.PConstraint (pattern, _) -> pattern_name pattern
  | Semantic_ir.PTyped (pattern, _) -> pattern_name pattern
  | Semantic_ir.PLocated (_, _, pattern) -> pattern_name pattern
  | Semantic_ir.PAlias (pattern, name) -> (
      match pattern_name pattern with Some _ as name -> name | None -> Some name)
  | Semantic_ir.PTuple patterns -> (
      match List.rev patterns with
      | pattern :: _ -> pattern_name pattern
      | [] -> None)
  | Semantic_ir.PAny | Semantic_ir.PUnit | Semantic_ir.PInt _ | Semantic_ir.PInt64 _
  | Semantic_ir.PString _ | Semantic_ir.PBool _ | Semantic_ir.PPolyTag _ | Semantic_ir.PConstructor _
  | Semantic_ir.PList _ | Semantic_ir.PCons _ | Semantic_ir.PRecord _
  | Semantic_ir.POr _ ->
      None

let fn_param_names expression =
  let rec strip expression =
    match expression with
    | Semantic_ir.Typed (_, value) | Semantic_ir.Located (_, _, value) ->
        strip value
    | Semantic_ir.Fun (patterns, _) ->
        List.map pattern_name patterns
    | Semantic_ir.Labelled_fun (patterns, _) ->
        List.map (fun (_, pattern) -> pattern_name pattern) patterns
    | _ -> []
  in
  strip expression

let align_deferred_param_types value_type expression =
  let pinned = dynamic_pinned_idents [] expression in
  match (pinned, value_type) with
  | [], _ | _, TFn ([], _) -> value_type
  | pinned, TFn (parameters, return_ty) ->
      let names = fn_param_names expression in
      TFn
        ( List.mapi
            (fun index ty ->
              match (List.nth_opt names index, ty) with
              | Some (Some name), (TUnknown | TMeta _ | TVar _)
                when List.mem name pinned ->
                  dynamic_constraint TUnknown
              | _ -> ty)
            parameters,
          return_ty )
  | _, value_type -> value_type
