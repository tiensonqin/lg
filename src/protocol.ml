open Ast
open Types

module Env = Compiler_environment

type method_signature = {
  method_id : Method_id.t;
  method_name : string;
  method_ty : ty;
}

let method_id protocol_id method_name =
  Method_id.create
    ~owner:(Protocol_id.owner protocol_id @ [ Protocol_id.name protocol_id ])
    ~name:method_name

let protocol_id scope protocol_name =
  if String.contains protocol_name '/' then Protocol_id.of_string protocol_name
  else
    Protocol_id.create
      ~owner:(if scope = "" then [] else [ scope ])
      ~name:protocol_name

let method_basename name =
  match String.rindex_opt name '/' with
  | None -> name
  | Some index -> String.sub name (index + 1) (String.length name - index - 1)

let canonical_protocol_name protocol_name =
  match method_basename protocol_name with
  | "ISeqable" -> "Seqable"
  | "IReduce" -> "Reducible"
  | "ICounted" -> "Counted"
  | "IEmptyableCollection" -> "Emptyable"
  | _ -> protocol_name

let protocol_marker_type = TOcaml "__lg_protocol_marker"

let protocol_binding protocol_id =
  Types.binding ~protocol_id (Protocol_id.to_string protocol_id)
    protocol_marker_type

let binding_protocol_id (binding : binding) =
  if Types.equal binding.ty protocol_marker_type then binding.protocol_id else None

let marker_binding protocol_id signature =
  Types.binding ~protocol_id (Protocol_id.to_string protocol_id)
    signature.method_ty

let resolve_protocol_id ~scope env protocol_id =
  let registry = Env.protocols env in
  let resolve_core_alias target name =
    let target_id = Protocol_id.create ~owner:[ target ] ~name in
    if Option.is_some (Protocol_registry.find_protocol target_id registry) then
      target_id
    else if
      String.equal target "cljs.core" || String.equal target "clojure.core"
    then
      let clojure_core_id =
        Protocol_id.create ~owner:[ "clojure.core" ] ~name
      in
      if
        Option.is_some
          (Protocol_registry.find_protocol clojure_core_id registry)
      then clojure_core_id
      else
        let root_id = Protocol_id.create ~owner:[] ~name in
        if Option.is_some (Protocol_registry.find_protocol root_id registry) then
          root_id
        else target_id
    else target_id
  in
  if Option.is_some (Protocol_registry.find_protocol protocol_id registry) then
    protocol_id
  else
    match Protocol_id.owner protocol_id with
    | [ module_path ] ->
        (match Env.resolve_namespace_alias ~scope module_path env with
        | Some target ->
            resolve_core_alias target (Protocol_id.name protocol_id)
        | None -> (
            if
              String.equal module_path "cljs.core"
              || String.equal module_path "clojure.core"
            then resolve_core_alias module_path (Protocol_id.name protocol_id)
            else
              match
                Module_registry.resolve_alias ~scope module_path (Env.modules env)
              with
              | None -> protocol_id
            | Some target ->
                Protocol_id.create ~owner:[ Module_id.to_string target ]
                  ~name:(Protocol_id.name protocol_id)))
    | _ -> protocol_id

let find_protocol_id scope env protocol_name =
  let source_name = protocol_name in
  let protocol_name = canonical_protocol_name source_name in
  let registry = Env.protocols env in
  let referred_id =
    Option.bind
      (Env.find_opt (Names.scoped_key scope source_name) env)
      binding_protocol_id
  in
  let scoped_id =
    protocol_id scope protocol_name |> resolve_protocol_id ~scope env
  in
  let root_id = Protocol_id.create ~owner:[] ~name:protocol_name in
  if
    match referred_id with
    | Some id -> Option.is_some (Protocol_registry.find_protocol id registry)
    | None -> false
  then referred_id
  else if Option.is_some (Protocol_registry.find_protocol scoped_id registry) then
    Some scoped_id
  else if Option.is_some (Protocol_registry.find_protocol root_id registry) then
    Some root_id
  else
    let core_id =
      Protocol_id.create ~owner:[ "clojure.core" ] ~name:protocol_name
    in
    if Option.is_some (Protocol_registry.find_protocol core_id registry) then
      Some core_id
    else None

let method_is_ambiguous scope env method_name =
  if String.contains method_name '/' then false
  else
    let owner = if scope = "" then [] else [ scope ] in
    let protocols =
      Protocol_registry.protocols_for_method ~owner ~method_name
        (Env.protocols env)
    in
    let protocols =
      if protocols = [] && owner <> [] then
        Protocol_registry.protocols_for_method ~owner:[] ~method_name
          (Env.protocols env)
      else protocols
    in
    (match protocols with
    | _ :: _ :: _ -> true
    | [] | [ _ ] -> false)

let receiver_id = function
  | TVar name when name = Receiver_id.default_type_variable -> Some "default"
  | TInt -> Some "int"
  | TFloat -> Some "float"
  | TChar -> Some "char"
  | TString -> Some "string"
  | TSymbol -> Some "symbol"
  | TKeyword -> Some "keyword"
  | TBool -> Some "bool"
  | TUnit -> Some "unit"
  | TList _ -> Some "list"
  | TVector _ -> Some "vector"
  | TSet _ -> Some "set"
  | TSeq _ -> Some "seq"
  | TArray _ -> Some "array"
  | TRef _ -> Some "ref"
  | TTuple _ -> Some "tuple"
  | TOcaml name | TOcaml_app (name, _) -> Some name
  | TNamed_record record -> Some record.type_name
  | _ -> None

let registry_receiver_id = Receiver_id.of_type

let protocol_receiver_id protocol_id receiver_ty =
  match (Protocol_id.owner protocol_id, receiver_ty) with
  | _ :: _, TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
      Some Receiver_id.Seq_receiver
  | _ -> registry_receiver_id receiver_ty

let source_type_implicitly_satisfies protocol_id receiver_ty =
  match
    (Protocol_id.owner protocol_id, Protocol_id.name protocol_id, receiver_ty)
  with
  | [], ("IMap" | "IAssociative" | "ICollection"), TRecord _ -> true
  | ( [],
      ("IMap" | "IAssociative" | "ICollection"),
      TNamed_record { nominal = false; _ } ) ->
      true
  | ([] | [ "clojure.core" ]), "IRecord",
    TNamed_record { nominal = false; _ } ->
      true
  | _ -> false

let reify_type_satisfies protocol_id = function
  | TOcaml_app ("Lg_runtime.Runtime_reify.t", [ payload_ty ]) ->
      let rec contains ty =
        match Types.reify_protocol_payload_info ty with
        | Some (candidate, _, rest_ty) ->
            String.equal candidate (Protocol_id.to_string protocol_id)
            || contains rest_ty
        | None -> false
      in
      contains payload_ty
  | _ -> false

let type_satisfies env protocol_id receiver_ty =
  let satisfies registry =
    match
      ( Protocol_registry.find_protocol protocol_id registry,
        protocol_receiver_id protocol_id receiver_ty )
    with
    | Some declaration, Some receiver_id ->
        if Protocol_registry.Method_map.is_empty declaration.methods then
          Protocol_registry.has_marker_implementation protocol_id receiver_id
            registry
        else
          Protocol_registry.Method_map.for_all
            (fun method_id _ ->
              Option.is_some
                (Protocol_registry.find_implementation_or_default protocol_id
                   method_id receiver_id registry))
            declaration.methods
    | None, _ | _, None -> false
  in
  source_type_implicitly_satisfies protocol_id receiver_ty
  || reify_type_satisfies protocol_id receiver_ty
  || satisfies (Env.protocols env)
  ||
  match Env.protocol_evidence env with
  | Some evidence -> satisfies evidence
  | None -> false

let satisfied_protocols env receiver_ty =
  Protocol_registry.declarations (Env.protocols env)
  |> List.filter_map (fun (protocol_id, _) ->
         let compiler_protocol =
           List.mem (Protocol_id.name protocol_id)
             [
               "Seqable";
               "Reducible";
               "Counted";
               "Indexed";
               "Emptyable";
               "IStack";
             ]
         in
         if (not compiler_protocol) && type_satisfies env protocol_id receiver_ty
         then Some protocol_id
         else None)

let constraint_type_for_id env protocol_id =
  let freshen_open_returns = function
    | TFn (parameters, (TUnknown | TMeta _)) ->
        TFn (parameters, Type_solver.fresh ())
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun (arity : fn_arity) ->
               match arity.return_ty with
               | TUnknown | TMeta _ ->
                   { arity with return_ty = Type_solver.fresh () }
               | _ -> arity)
             arities)
    | ty -> ty
  in
  Protocol_registry.find_protocol protocol_id (Env.protocols env)
  |> Option.map (fun (declaration : Protocol_registry.declaration) ->
         let method_types =
           declaration.methods
           |> Protocol_registry.Method_map.bindings
           |> List.map
                (fun (_, (signature : Protocol_registry.method_signature)) ->
                  freshen_open_returns signature.method_ty)
         in
         Types.protocol_constraint protocol_id method_types TUnknown)

let instantiate_receiver_binding receiver_ty (implementation : binding) =
  {
    implementation with
    ty =
      Types.instantiate_receiver_method_type receiver_ty implementation.ty;
  }

let apply_method_signature
    (signature : Protocol_registry.method_signature)
    (implementation : binding) =
  match (signature.method_ty, implementation.ty) with
  | TFn (_, declared_return), TFn (parameters, (TUnknown | TMeta _ | TVar _))
    when not (Types.equal declared_return TUnknown) ->
      { implementation with ty = TFn (parameters, declared_return) }
  | _ -> implementation

let find_implementation_or_evidence env protocol_id method_id receiver_id =
  match
    Protocol_registry.find_implementation_or_default protocol_id method_id
      receiver_id (Env.protocols env)
  with
  | Some _ as implementation -> implementation
  | None -> (
      match Env.protocol_evidence env with
      | Some evidence ->
          Protocol_registry.find_implementation_or_default protocol_id
            method_id receiver_id evidence
      | None -> None)

let witness_implementations env protocol_id receiver_ty =
  match
    ( Protocol_registry.find_protocol protocol_id (Env.protocols env),
      protocol_receiver_id protocol_id receiver_ty )
  with
  | Some (declaration : Protocol_registry.declaration), Some receiver_id ->
      let implementations =
        declaration.methods
        |> Protocol_registry.Method_map.bindings
        |> List.map (fun (method_id, signature) ->
               find_implementation_or_evidence env protocol_id method_id
                 receiver_id
               |> Option.map (fun implementation ->
                      implementation
                      |> instantiate_receiver_binding receiver_ty
                      |> apply_method_signature signature))
      in
      if List.for_all Option.is_some implementations then
        Some
          (List.map
             (fun implementation ->
               instantiate_receiver_binding receiver_ty
                 (Option.get implementation))
             implementations)
      else None
  | None, _ | _, None -> None

let infer_constraint_substitutions env substitutions constraint_ty receiver_ty =
  match Types.protocol_constraint_info constraint_ty with
  | None -> substitutions
  | Some (protocol_id, witness_ty, value_ty) ->
      let substitutions =
        Type_solver.unify substitutions value_ty receiver_ty
        |> Result.value ~default:substitutions
      in
      (match
         ( Types.protocol_witness_method_types witness_ty,
           witness_implementations env protocol_id receiver_ty )
       with
        | Some expected_methods, Some implementations
          when List.length expected_methods = List.length implementations ->
            List.fold_left2
              (fun substitutions expected (implementation : binding) ->
                match (expected, implementation.ty) with
                | ( TFn (_ :: expected_parameters, expected_return),
                    TFn (actual_receiver :: actual_parameters, actual_return) )
                  when List.length expected_parameters
                       = List.length actual_parameters
                       && Result.is_ok
                            (Type_solver.unify Type_solver.empty receiver_ty
                               actual_receiver) ->
                    let substitutions =
                      Type_solver.unify_lists substitutions expected_parameters
                        actual_parameters
                    |> Result.value ~default:substitutions
                  in
                  Type_solver.unify substitutions expected_return actual_return
                  |> Result.value ~default:substitutions
              | _ -> substitutions)
            substitutions expected_methods implementations
      | Some _, Some _ | None, _ | _, None -> substitutions)

let witness_methods env protocol_id receiver_ty =
  match
    ( Protocol_registry.find_protocol protocol_id (Env.protocols env),
      protocol_receiver_id protocol_id receiver_ty )
  with
  | Some (declaration : Protocol_registry.declaration), Some receiver_id ->
      let rec collect methods = function
        | [] -> Some (List.rev methods)
        | (method_id, signature) :: rest -> (
            match
              Protocol_registry.find_implementation protocol_id method_id
                receiver_id (Env.protocols env)
            with
            | None -> None
            | Some implementation ->
                collect
                  ( ( Method_id.name method_id,
                      implementation
                      |> instantiate_receiver_binding receiver_ty
                      |> apply_method_signature signature )
                  :: methods )
                  rest)
      in
      collect []
        (Protocol_registry.Method_map.bindings declaration.methods)
  | None, _ | _, None -> None

let witness_implemented_methods env protocol_id receiver_ty =
  match
    ( Protocol_registry.find_protocol protocol_id (Env.protocols env),
      protocol_receiver_id protocol_id receiver_ty )
  with
  | Some (declaration : Protocol_registry.declaration), Some receiver_id ->
      let methods =
        declaration.methods
        |> Protocol_registry.Method_map.bindings
        |> List.filter_map (fun (method_id, signature) ->
               Protocol_registry.find_implementation protocol_id method_id
                 receiver_id (Env.protocols env)
               |> Option.map (fun implementation ->
                      ( Method_id.name method_id,
                        implementation
                        |> instantiate_receiver_binding receiver_ty
                        |> apply_method_signature signature )))
      in
      if methods = [] then None else Some methods
  | None, _ | _, None -> None

let implemented_protocols env receiver_ty =
  Protocol_registry.declarations (Env.protocols env)
  |> List.filter_map (fun (protocol_id, _) ->
         let compiler_protocol =
           List.mem (Protocol_id.name protocol_id)
             [
               "Seqable";
               "Reducible";
               "Counted";
               "Indexed";
               "Emptyable";
               "IStack";
             ]
         in
         if
           (not compiler_protocol)
           && Option.is_some
                (witness_implemented_methods env protocol_id receiver_ty)
         then Some protocol_id
         else None)

let dynamic_protocols env receiver_ty =
  Protocol_registry.declarations (Env.protocols env)
  |> List.filter_map (fun (protocol_id, _) ->
         if
           Option.is_some
             (witness_implemented_methods env protocol_id receiver_ty)
         then Some protocol_id
         else None)

let rec merge_method_return_types env left right =
  match (left, right) with
  | Types.TUnknown, ty | ty, Types.TUnknown -> Some ty
  | Types.TMeta _, ty | ty, Types.TMeta _ -> (
      match Type_solver.unify ~commit:true Type_solver.empty left right with
      | Ok substitutions -> Some (Type_solver.apply substitutions ty)
      | Error _ -> None)
  | Types.TVar left, Types.TVar right when String.equal left right ->
      Some (Types.TVar left)
  | Types.TVar _, _ | _, Types.TVar _ -> None
  | left, right when Types.equal left right -> Some left
  | left, right when Types.is_dynamic left || Types.is_dynamic right ->
      Some (Types.dynamic_constraint Types.TUnknown)
  | Types.TNullable left, Types.TNullable right ->
      Option.map
        (fun value -> Types.TNullable value)
        (merge_method_return_types env left right)
  | Types.TNullable left, right | right, Types.TNullable left ->
      Option.map
        (fun value -> Types.TNullable value)
        (merge_method_return_types env left right)
  | Types.TSeq left, Types.TSeq right ->
      Option.map
        (fun element -> Types.TSeq element)
        (merge_method_return_types env left right)
  | Types.TList left, Types.TList right ->
      Option.map
        (fun element -> Types.TList element)
        (merge_method_return_types env left right)
  | Types.TVector left, Types.TVector right ->
      Option.map
        (fun element -> Types.TVector element)
        (merge_method_return_types env left right)
  | Types.TArray left, Types.TArray right ->
      Option.map
        (fun element -> Types.TArray element)
        (merge_method_return_types env left right)
  | _ -> (
      match
        ( Collection_capability.element_type_of_ty env left,
          Collection_capability.element_type_of_ty env right )
      with
      | Some left, Some right ->
          Option.map
            (fun element -> Types.TSeq element)
            (merge_method_return_types env left right)
      | None, _ | _, None -> None)

let rec stable_method_return_type = function
  | Types.TNullable return_ty ->
      Types.TNullable (stable_method_return_type return_ty)
  | Types.TConstraint
      (Seqable_constraint { requirement = Required; element = element_ty; _ }) ->
      Types.TSeq element_ty
  | Types.TConstraint
      (Seqable_constraint
        {
          requirement = (Optional | Optional_sequential);
          element = element_ty;
          _;
        }) ->
      Types.TNullable (Types.TSeq element_ty)
  | return_ty -> return_ty

let common_method_return env protocol_id method_name =
  let method_id = method_id protocol_id method_name in
  let registry = Env.protocols env in
  let return_types =
    Protocol_registry.implementations_for_method protocol_id method_id registry
    |> List.filter_map (fun (implementation : binding) ->
           match implementation.ty with
           | TFn (_, return_ty) when not (Types.equal return_ty TUnknown) ->
               Some (stable_method_return_type return_ty)
           | _ -> None)
  in
  match return_types with
  | [] -> None
  | first :: rest ->
      List.fold_left
        (fun merged return_ty ->
          Option.bind merged (fun merged ->
              merge_method_return_types env merged return_ty))
        (Some first) rest

let common_method_return_for_arity env protocol_id method_name
    (target : fn_arity) =
  let method_id = method_id protocol_id method_name in
  let registry = Env.protocols env in
  let same_arity (arity : fn_arity) =
    List.length arity.fixed_params = List.length target.fixed_params
    && Option.is_some arity.rest_param = Option.is_some target.rest_param
  in
  let return_types =
    Protocol_registry.implementations_for_method protocol_id method_id registry
    |> List.filter_map (fun (implementation : binding) ->
           match implementation.ty with
           | TOverloaded_fn arities ->
               arities
               |> List.find_opt same_arity
               |> Option.map (fun arity -> arity.return_ty)
           | TFn (parameters, return_ty)
             when Option.is_none target.rest_param
                  && List.length parameters
                     = List.length target.fixed_params ->
               Some return_ty
           | _ -> None)
    |> List.filter (fun return_ty ->
           not (Types.equal return_ty TUnknown))
    |> List.map stable_method_return_type
  in
  match return_types with
  | [] -> None
  | first :: rest ->
      List.fold_left
        (fun merged return_ty ->
          Option.bind merged (fun merged ->
              merge_method_return_types env merged return_ty))
        (Some first) rest

let has_self_returning_method env protocol_id =
  let returns_self = function
    | TFn (_, TVar "__lg_protocol_self") -> true
    | TOverloaded_fn arities ->
        List.exists
          (fun (arity : fn_arity) ->
            Types.equal arity.return_ty (TVar "__lg_protocol_self"))
          arities
    | _ -> false
  in
  Protocol_registry.find_protocol protocol_id (Env.protocols env)
  |> Option.fold ~none:false
       ~some:(fun (declaration : Protocol_registry.declaration) ->
         declaration.methods
         |> Protocol_registry.Method_map.exists (fun _ signature ->
                returns_self signature.Protocol_registry.method_ty))

let refine_marker_signature env protocol_id target_method_id
    (signature : Protocol_registry.method_signature) =
  let registry = Env.protocols env in
  let refine_arity ?overloaded_arity use_common_return (arity : fn_arity) =
    let fixed_params =
      List.map
        (function TUnknown -> Type_solver.fresh () | ty -> ty)
        arity.fixed_params
    in
    let return_ty =
      match arity.return_ty with
      | TVar "__lg_protocol_self" -> (
          match fixed_params with
          | receiver :: _ -> receiver
          | [] -> Type_solver.fresh ())
      | TUnknown | TMeta _ when use_common_return ->
          (match overloaded_arity with
          | Some target ->
              common_method_return_for_arity env protocol_id
                (Method_id.name target_method_id) target
          | None ->
              common_method_return env protocol_id
                (Method_id.name target_method_id))
          |> Option.value ~default:(Type_solver.fresh ())
      | TUnknown | TMeta _ -> Type_solver.fresh ()
      | ty -> ty
    in
    { arity with fixed_params; return_ty }
  in
  let target_method_ty =
    match signature.method_ty with
    | TFn (param_tys, return_ty) ->
        let arity =
          refine_arity true
            { fixed_params = param_tys; rest_param = None; return_ty }
        in
        TFn (arity.fixed_params, arity.return_ty)
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun arity ->
               refine_arity ~overloaded_arity:arity true arity)
             arities)
    | ty -> ty
  in
  let first_receiver = function
    | TFn (receiver :: _, _) -> Some receiver
    | TOverloaded_fn ({ fixed_params = receiver :: _; _ } :: _) -> Some receiver
    | _ -> None
  in
  let with_receiver receiver = function
    | TFn (_ :: params, return_ty) -> TFn (receiver :: params, return_ty)
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun arity ->
               match arity.fixed_params with
               | _ :: params -> { arity with fixed_params = receiver :: params }
               | [] -> arity)
             arities)
    | ty -> ty
  in
  let receiver_constraint =
    Protocol_registry.find_protocol protocol_id registry
    |> Option.map (fun (declaration : Protocol_registry.declaration) ->
           declaration.methods
           |> Protocol_registry.Method_map.bindings
           |> List.map
                (fun (candidate_method_id, method_) ->
                  if Method_id.equal candidate_method_id target_method_id then
                    target_method_ty
                  else method_.Protocol_registry.method_ty)
           |> fun methods ->
             let receiver_value_ty =
               match first_receiver target_method_ty with
               | Some (TVar _ as receiver) -> receiver
               | _ -> TUnknown
             in
             Types.protocol_constraint protocol_id methods receiver_value_ty)
  in
  let method_ty =
    match receiver_constraint with
    | Some receiver -> with_receiver receiver target_method_ty
    | None -> target_method_ty
  in
  { signature with method_ty }

let lookup_marker scope env method_name =
  let registry = Env.protocols env in
  let marker_for protocol_id method_name =
    let method_id = method_id protocol_id method_name in
    Protocol_registry.find_method protocol_id method_id registry
    |> Option.map (fun (signature : Protocol_registry.method_signature) ->
           let signature =
             refine_marker_signature env protocol_id method_id signature
           in
           marker_binding protocol_id
             { method_id; method_name; method_ty = signature.method_ty })
  in
  match List.rev (String.split_on_char '/' method_name) with
    | method_name :: protocol_name :: reversed_owner ->
        let protocol_name =
          String.concat "/" (List.rev (protocol_name :: reversed_owner))
          |> canonical_protocol_name
        in
        let aliased_protocol_id =
          match String.rindex_opt protocol_name '/' with
          | None -> None
          | Some separator ->
              let namespace = String.sub protocol_name 0 separator in
              let local_name =
                String.sub protocol_name (separator + 1)
                  (String.length protocol_name - separator - 1)
                |> canonical_protocol_name
              in
              Option.map
                (fun target ->
                  Protocol_id.create ~owner:[ target ] ~name:local_name
                  |> resolve_protocol_id ~scope env)
                (Env.resolve_namespace_alias ~scope namespace env)
        in
        let namespace_owner =
          match Env.resolve_namespace_alias ~scope protocol_name env with
          | Some target -> Some target
          | None ->
              let protocols =
                Protocol_registry.protocols_for_method
                  ~owner:[ protocol_name ] ~method_name registry
              in
              if protocols = [] then None else Some protocol_name
        in
        (match aliased_protocol_id with
        | Some protocol_id -> marker_for protocol_id method_name
        | None ->
        (match namespace_owner with
        | Some owner -> (
            match
              Protocol_registry.protocols_for_method ~owner:[ owner ]
                ~method_name registry
            with
            | [ protocol_id ] -> marker_for protocol_id method_name
            | [] | _ :: _ :: _ -> None)
        | None ->
            let scoped_id =
              protocol_id scope protocol_name |> resolve_protocol_id ~scope env
            in
            (match marker_for scoped_id method_name with
            | Some _ as marker -> marker
            | None -> (
                match find_protocol_id scope env protocol_name with
                | Some protocol_id -> marker_for protocol_id method_name
                | None ->
                    marker_for
                      (Protocol_id.create ~owner:[] ~name:protocol_name)
                      method_name))))
    | [ method_name ] ->
        let owner = if scope = "" then [] else [ scope ] in
        let protocols =
          Protocol_registry.protocols_for_method ~owner ~method_name registry
        in
        let protocols =
          if protocols = [] && owner <> [] then
            Protocol_registry.protocols_for_method ~owner:[] ~method_name
              registry
          else protocols
        in
        (match protocols with
        | [ protocol_id ] ->
            marker_for protocol_id method_name
        | [] -> (
            match Env.find_opt (Names.scoped_key scope method_name) env with
            | Some { protocol_id = Some protocol_id; _ } ->
                marker_for protocol_id method_name
            | Some _ | None -> None)
        | _ :: _ :: _ -> None)
    | [] -> None

let raw_constraint_type scope env protocol_or_method_name =
  match find_protocol_id scope env protocol_or_method_name with
  | Some protocol_id -> constraint_type_for_id env protocol_id
  | None -> (
      match lookup_marker scope env protocol_or_method_name with
      | Some { protocol_id = Some protocol_id; _ } ->
          constraint_type_for_id env protocol_id
      | Some _ | None -> None)

let lookup_protocol_marker ?(refine = true) scope env protocol_name method_name =
  let registry = Env.protocols env in
  match find_protocol_id scope env protocol_name with
  | None -> None
  | Some id ->
      let method_id = method_id id method_name in
      (match Protocol_registry.find_method id method_id registry with
      | Some (signature : Protocol_registry.method_signature) ->
          let signature =
            if refine then refine_marker_signature env id method_id signature
            else signature
          in
          Some
            (marker_binding id
               { method_id; method_name; method_ty = signature.method_ty })
      | None -> None)

let lookup_impl env protocol_id method_name receiver_ty =
  match protocol_receiver_id protocol_id receiver_ty with
  | Some receiver_id ->
      let receiver_id =
        match receiver_ty with
        | TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
            Receiver_id.Seq_receiver
        | _ -> receiver_id
      in
      let method_id = method_id protocol_id method_name in
      let registry = Env.protocols env in
      find_implementation_or_evidence env protocol_id method_id receiver_id
      |> Option.map (fun implementation ->
             let implementation =
               instantiate_receiver_binding receiver_ty implementation
             in
             match Protocol_registry.find_method protocol_id method_id registry with
             | None -> implementation
             | Some signature ->
                 apply_method_signature signature implementation)
  | None -> None

let lookup_unique_method_impl env method_name receiver_ty =
  let registry = Env.protocols env in
  let candidates =
    Protocol_registry.declarations registry
    |> List.filter_map (fun (protocol_id, declaration) ->
         declaration.Protocol_registry.methods
         |> Protocol_registry.Method_map.bindings
         |> List.find_map (fun (method_id, _) ->
                let registered_name = Method_id.name method_id in
                if
                  String.equal (method_basename registered_name)
                    (method_basename method_name)
                then lookup_impl env protocol_id registered_name receiver_ty
                else None))
  in
  match candidates with
  | [ implementation ] -> Some implementation
  | [] | _ :: _ :: _ -> None

let lookup_marker_impl env (marker : binding) method_name receiver_ty =
  match marker.protocol_id with
  | None -> None
  | Some protocol_id -> lookup_impl env protocol_id method_name receiver_ty

let common_method_returns env protocol_id =
  match
    Protocol_registry.find_protocol protocol_id (Env.protocols env)
  with
  | None -> []
  | Some declaration ->
      declaration.methods
      |> Protocol_registry.Method_map.bindings
      |> List.map (fun (method_id, _) ->
             common_method_return env protocol_id (Method_id.name method_id))

let common_overloaded_method_return env protocol_id method_id arity =
  common_method_return_for_arity env protocol_id (Method_id.name method_id)
    arity

let common_method_parameters env protocol_id method_id =
  let registry =
    Compiler_environment.protocol_evidence env
    |> Option.value ~default:(Env.protocols env)
  in
  let implementations =
    Protocol_registry.implementations_for_method protocol_id method_id
      registry
  in
  let parameter_lists =
    implementations
    |> List.filter_map (fun (implementation : binding) ->
           match implementation.ty with
           | TFn (_receiver :: parameters, _) -> Some parameters
           | TFn ([], _) | _ -> None)
  in
  match parameter_lists with
  | [] -> []
  | first :: rest
    when List.for_all
           (fun parameters -> List.length parameters = List.length first)
           rest ->
      List.mapi
        (fun index _ ->
          let candidates =
            parameter_lists
            |> List.filter_map (fun parameters ->
                   match List.nth parameters index with
                   | TUnknown | TMeta _ | TVar _ -> None
                   | ty -> Some (Types.constraint_value_type ty))
          in
          match candidates with
          | candidate :: candidates
            when List.for_all (Types.equal candidate) candidates ->
              Some candidate
          | [] | _ :: _ -> None)
        first
  | _ -> []

let refine_constraint_methods env ty =
  let rec method_types = function
    | TUnit -> Some []
    | TTuple [ method_ty; rest ] ->
        Option.map (fun rest -> method_ty :: rest) (method_types rest)
    | _ -> None
  in
  match Types.protocol_constraint_info ty with
  | None -> ty
  | Some (protocol_id, witness_ty, value_ty) -> (
      match method_types witness_ty with
      | None -> ty
      | Some methods ->
          let returns = common_method_returns env protocol_id in
          let declaration_methods =
            Protocol_registry.find_protocol protocol_id (Env.protocols env)
            |> Option.map (fun (declaration : Protocol_registry.declaration) ->
                   Protocol_registry.Method_map.bindings declaration.methods)
            |> Option.value ~default:[]
          in
          let parameters =
            declaration_methods
            |> List.map (fun (method_id, _) ->
                   common_method_parameters env protocol_id method_id)
          in
          let declared_returns_are_open =
            declaration_methods
            |> List.map (fun (_, signature) ->
                   match signature.Protocol_registry.method_ty with
                   | TFn (_, (TUnknown | TMeta _)) -> true
                   | _ -> false)
          in
          if
            List.length methods <> List.length returns
            || List.length methods <> List.length parameters
            || List.length methods <> List.length declared_returns_are_open
          then ty
          else
            let methods =
              List.map2
                (fun method_ty
                     ( (method_id, _),
                       ( (inferred_parameters, inferred_return),
                         declared_return_is_open ) )
                   ->
                  match method_ty with
                  | TFn (receiver :: existing_parameters, existing_return)
                    when List.length existing_parameters
                         = List.length inferred_parameters ->
                      let parameters =
                        List.map2
                          (fun existing inferred ->
                            match (existing, inferred) with
                            | (TUnknown | TMeta _ | TVar _), Some inferred ->
                                inferred
                            | existing, _ -> existing)
                          existing_parameters inferred_parameters
                      in
                      let existing_return =
                        stable_method_return_type existing_return
                      in
                      let return_ty =
                        match
                          ( declared_return_is_open,
                            existing_return,
                            inferred_return )
                        with
                        | true, _, Some inferred -> inferred
                        | _, (TUnknown | TMeta _), Some inferred -> inferred
                        | _, existing, Some inferred ->
                            merge_method_return_types env existing inferred
                            |> Option.value ~default:existing
                        | _, existing, _ -> existing
                      in
                      TFn (receiver :: parameters, return_ty)
                  | TFn (params, existing_return) -> (
                      let existing_return =
                        stable_method_return_type existing_return
                      in
                      match
                        ( declared_return_is_open,
                          existing_return,
                          inferred_return )
                      with
                      | true, _, Some return_ty
                      | _, (TUnknown | TMeta _), Some return_ty ->
                          TFn (params, return_ty)
                      | _, existing, Some inferred ->
                          TFn
                            ( params,
                              merge_method_return_types env existing inferred
                              |> Option.value ~default:existing )
                      | _, return_ty, _ -> TFn (params, return_ty))
                  | TOverloaded_fn arities ->
                      TOverloaded_fn
                        (List.map
                           (fun (arity : fn_arity) ->
                             let existing_return =
                               stable_method_return_type arity.return_ty
                             in
                             let return_ty =
                               match
                                 common_overloaded_method_return env protocol_id
                                   method_id arity
                               with
                               | Some inferred -> (
                                   match existing_return with
                                   | TUnknown | TMeta _ -> inferred
                                   | existing ->
                                       merge_method_return_types env existing
                                         inferred
                                       |> Option.value ~default:existing)
                               | None -> existing_return
                             in
                             { arity with return_ty })
                           arities)
                  | _ -> method_ty)
                methods
                (List.combine declaration_methods
                   (List.combine (List.combine parameters returns)
                      declared_returns_are_open))
            in
            Types.protocol_constraint protocol_id methods value_ty)

let constraint_type scope env protocol_or_method_name =
  raw_constraint_type scope env protocol_or_method_name
  |> Option.map (refine_constraint_methods env)

let constraint_return_substitutions env substitutions ty =
  match Types.protocol_constraint_info ty with
  | None -> substitutions
  | Some (protocol_id, witness_ty, _) -> (
      match Types.protocol_witness_method_types witness_ty with
      | None -> substitutions
      | Some methods ->
          let returns = common_method_returns env protocol_id in
          let declaration_methods =
            Protocol_registry.find_protocol protocol_id (Env.protocols env)
            |> Option.map (fun (declaration : Protocol_registry.declaration) ->
                   Protocol_registry.Method_map.bindings declaration.methods)
            |> Option.value ~default:[]
          in
          if
            List.length methods <> List.length returns
            || List.length methods <> List.length declaration_methods
          then substitutions
          else
            List.fold_left2
              (fun substitutions method_ty ((method_id, _), return_ty) ->
                match (method_ty, return_ty) with
                | TFn (_, existing_return), Some inferred_return ->
                    Type_solver.unify substitutions existing_return
                      inferred_return
                    |> Result.value ~default:substitutions
                | TOverloaded_fn arities, _ ->
                    List.fold_left
                      (fun substitutions (arity : fn_arity) ->
                        match
                          common_overloaded_method_return env protocol_id
                            method_id arity
                        with
                        | Some inferred_return ->
                            Type_solver.unify substitutions arity.return_ty
                              inferred_return
                            |> Result.value ~default:substitutions
                        | None -> substitutions)
                      substitutions arities
                | _, (Some _ | None) -> substitutions)
              substitutions methods
              (List.combine declaration_methods returns))

let refine_deferred_type env = function
  | TFn (parameters, _) as ty ->
      let substitutions =
        List.fold_left
          (constraint_return_substitutions env)
          Type_solver.empty parameters
      in
      let ty = Type_solver.apply substitutions ty in
      (match ty with
      | TFn (parameters, return_ty) ->
          TFn
            ( List.map (refine_constraint_methods env) parameters,
              return_ty )
      | _ -> assert false)
  | ty -> ty

let refine_source_function_type env ty =
  let rec constraint_needs_stabilization parameter_ty =
    match Types.protocol_constraint_info parameter_ty with
    | Some _ -> true
    | None -> (
        match parameter_ty with
        | TNullable value_ty | TOcaml_app ("option", [ value_ty ]) ->
            constraint_needs_stabilization value_ty
        | _ -> false)
  in
  match ty with
  | TFn (parameters, _)
    when List.exists constraint_needs_stabilization parameters ->
      refine_deferred_type env ty
  | _ -> ty

let common_method_return_param_index env protocol_id method_name =
  let method_id = method_id protocol_id method_name in
  let declared_self_return =
    match
      Protocol_registry.find_method protocol_id method_id (Env.protocols env)
    with
    | Some { method_ty = TFn (_, TVar "__lg_protocol_self"); _ } -> true
    | Some { method_ty = TOverloaded_fn arities; _ } ->
        arities <> []
        && List.for_all
             (fun (arity : fn_arity) ->
               Types.equal arity.return_ty (TVar "__lg_protocol_self"))
             arities
    | Some _ | None -> false
  in
  if declared_self_return then Some 0
  else
  let registry =
    Compiler_environment.protocol_evidence env
    |> Option.value ~default:(Env.protocols env)
  in
  let indices =
    Protocol_registry.implementations_for_method protocol_id method_id
      registry
    |> List.map (fun (implementation : binding) ->
           implementation.return_param_index)
  in
  match indices with
  | Some first :: Some second :: rest
    when first = second
         && List.for_all (fun index -> index = Some first) rest ->
      Some first
  | [] | _ -> None

let method_position env (marker : binding) method_name =
  match marker.protocol_id with
  | None -> None
  | Some protocol_id -> (
      match Protocol_registry.find_protocol protocol_id (Env.protocols env) with
      | None -> None
      | Some declaration ->
          declaration.methods
          |> Protocol_registry.Method_map.bindings
          |> List.mapi (fun index (method_id, _) -> (index, Method_id.name method_id))
          |> List.find_map (fun (index, name) ->
                 if name = method_name then Some index else None))

let method_count env (marker : binding) =
  match marker.protocol_id with
  | None -> 0
  | Some protocol_id -> (
      match Protocol_registry.find_protocol protocol_id (Env.protocols env) with
      | None -> 0
      | Some declaration -> Protocol_registry.Method_map.cardinal declaration.methods)

let marker_has_protocol_id (marker : binding) protocol_id =
  Option.fold ~none:false
    ~some:(fun marker_id -> Protocol_id.equal marker_id protocol_id)
    marker.protocol_id

let parse_method_signature = function
  | FList (FSymbol method_name :: forms) ->
      let forms =
        match List.rev forms with
        | FString _ :: rest -> List.rev rest
        | _ -> forms
      in
      let parameter_forms, return_ty =
        match List.rev forms with
        | FKeyword ":self" :: rest ->
            (List.rev rest, Ok (TVar "__lg_protocol_self"))
        | FKeyword return_keyword :: rest ->
            (List.rev rest, Type_annotation.of_keyword return_keyword)
        | _ -> (forms, Ok TUnknown)
      in
      Result.bind return_ty (fun return_ty ->
          let rec parse arities seen = function
            | [] ->
                let arities = List.rev arities in
                let method_ty =
                  match arities with
                  | [ arity ] -> TFn (arity.fixed_params, arity.return_ty)
                  | arities -> TOverloaded_fn arities
                in
                Ok
                  {
                    method_id = Method_id.create ~owner:[] ~name:method_name;
                    method_name;
                    method_ty;
                  }
            | (FVector _ as params) :: rest ->
                Result.bind (Type_annotation.parse_params params) (fun params ->
                    let fixed_params = List.map snd params in
                    if fixed_params = [] then
                      Error.error
                        "protocol methods must have a receiver parameter"
                    else
                      let count = List.length fixed_params in
                      if List.mem count seen then
                        Error.error
                          ("protocol method " ^ method_name
                         ^ " declares duplicate arity " ^ string_of_int count)
                      else
                        parse
                          ({ fixed_params; rest_param = None; return_ty }
                          :: arities)
                          (count :: seen) rest)
            | _ :: _ ->
                Error.error
                  "protocol method arities must be parameter vectors"
          in
          if parameter_forms = [] then
            Error.error "protocol methods must declare at least one arity"
          else parse [] [] parameter_forms)
  | _ ->
      Error.error
        "defprotocol methods must be (method-name [params]...)"

let defprotocol scope protocol_name method_forms =
  let id = protocol_id scope protocol_name in
  let rec loop seen signatures = function
    | [] -> Ok (id, List.rev signatures)
    | method_form :: rest -> (
        match parse_method_signature method_form with
        | Error _ as err -> err
        | Ok signature ->
            if List.mem signature.method_name seen then
              Error.error
                ("protocol " ^ protocol_name ^ " declares duplicate method "
               ^ signature.method_name)
            else
            let signature =
              { signature with method_id = method_id id signature.method_name }
            in
            let registry_signature : Protocol_registry.method_signature =
              {
                method_id = signature.method_id;
                method_ty = signature.method_ty;
              }
            in
            loop (signature.method_name :: seen)
              (registry_signature :: signatures)
              rest)
  in
  loop [] [] method_forms

let annotate_receiver receiver_ty =
  let receiver_annotation = function
    | TNamed_record record -> "^" ^ Type_id.name record.type_id
    | ty -> "^" ^ source_name ty
  in
  function
  | FVector (FSymbol annotation :: FSymbol _name :: _rest as params)
    when String.starts_with ~prefix:"^" annotation -> (
      match Type_annotation.of_param_annotation annotation with
      | Error _ as err -> err
      | Ok ty ->
          if
            Types.same_shape ty receiver_ty
            || Option.equal ( = )
                 (registry_receiver_id ty)
                 (registry_receiver_id receiver_ty)
          then Ok (FVector params)
          else
            Error.error
              ("protocol implementation receiver must be " ^ source_name receiver_ty))
  | FVector (FSymbol name :: rest) -> (
      match registry_receiver_id receiver_ty with
      | Some _ ->
          (match receiver_ty with
          | TNamed_record _ ->
              Ok
                (FVector
                   (FSymbol (receiver_annotation receiver_ty)
                   :: FSymbol name :: rest))
          | _ -> Ok (FVector (FSymbol name :: rest)))
      | None ->
          Error.error
            ("protocol implementations do not support receiver type "
           ^ source_name receiver_ty))
  | FVector _ -> Error.error "protocol methods must have a receiver parameter"
  | _ -> Error.error "protocol method parameters must be a vector"

let impl_ocaml_name scope protocol_name method_name receiver_ty =
  Names.ocaml_binding_name scope
    ("protocol_" ^ protocol_name ^ "_" ^ method_name ^ "_"
   ^ Option.value (receiver_id receiver_ty) ~default:(source_name receiver_ty))
