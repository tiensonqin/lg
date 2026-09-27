module Symbol_map = Persistent_hash_map.Make (struct
  type t = Symbol_id.t

  let equal = Symbol_id.equal
  let hash = Symbol_id.hash
end)
module String_map = Persistent_hash_map.Make (struct
  type t = string

  let equal = String.equal
  let hash = Hashtbl.hash
end)

type exception_data_adapter = Direct of string | Fields of string

type t = {
  target : Target.t;
  symbols : Types.binding Symbol_map.t;
  record_symbols : Types.binding Symbol_map.t;
  record_bindings_by_lookup : Symbol_id.t list String_map.t;
  bindings_by_name : Symbol_id.t list String_map.t;
  bindings_by_emitted_name : Symbol_id.t list String_map.t;
  bindings_by_namespace : Symbol_id.t list String_map.t;
  opened_bindings_by_scope : Symbol_id.t list String_map.t;
  unresolved_declaration_names : int String_map.t;
  unresolved_declaration_binding_names : int String_map.t;
  explicit_declaration_names : unit String_map.t;
  protocols : Protocol_registry.t;
  protocol_evidence : Protocol_registry.t option;
  modules : Module_registry.t;
  types : Type_registry.t;
  signatures : Signature_overlay.t;
  anonymous_records : (string * Semantic_type.named_record) list;
  namespace_aliases : string String_map.t;
  core_exclusions : unit String_map.t;
  macros : Macro_definition.t String_map.t;
  inline_macros : Macro_definition.t String_map.t;
  macro_functions : Macro_definition.t String_map.t;
  macro_values : Ast.form String_map.t;
  private_exports : unit String_map.t;
  expected_type : Types.ty option;
  source_macros_expanded : bool;
  closed_sum_constructors :
    (Types.ty * (string * Types.ty list) list) list;
  predicate_sum_constructors :
    (Types.ty * (string * Types.ty list) list) list;
  optional_sequential_adapters : (Types.ty * Types.ty * string) list;
  nil_value_adapters : (Types.ty * string) list;
  truthiness_adapters : (Types.ty * string) list;
  successful_call_refinements : (string * (int * Types.ty)) list;
  exception_data_adapters : (Types.ty * exception_data_adapter) list;
  empty_map_defaults : (Types.ty * string) list;
}

let empty =
  {
    target = Target.default;
    symbols = Symbol_map.empty;
    record_symbols = Symbol_map.empty;
    record_bindings_by_lookup = String_map.empty;
    bindings_by_name = String_map.empty;
    bindings_by_emitted_name = String_map.empty;
    bindings_by_namespace = String_map.empty;
    opened_bindings_by_scope = String_map.empty;
    unresolved_declaration_names = String_map.empty;
    unresolved_declaration_binding_names = String_map.empty;
    explicit_declaration_names = String_map.empty;
    protocols = Core_protocols.initial_registry;
    protocol_evidence = None;
    modules = Module_registry.empty;
    types = Type_registry.empty;
    signatures = Signature_overlay.empty;
    anonymous_records = [];
    namespace_aliases = String_map.empty;
    core_exclusions = String_map.empty;
    macros = String_map.empty;
    inline_macros = String_map.empty;
    macro_functions = String_map.empty;
    macro_values = String_map.empty;
    private_exports = String_map.empty;
    expected_type = None;
    source_macros_expanded = false;
    closed_sum_constructors = [];
    predicate_sum_constructors = [];
    optional_sequential_adapters = [];
    nil_value_adapters = [];
    truthiness_adapters = [];
    successful_call_refinements = [];
    exception_data_adapters = [];
    empty_map_defaults = [];
  }

let target env = env.target
let with_target target env = { env with target }
let expected_type env = env.expected_type
let with_expected_type expected_type env = { env with expected_type }
let source_macros_expanded env = env.source_macros_expanded

let with_source_macros_expanded source_macros_expanded env =
  { env with source_macros_expanded }

let find_opt name env =
  Symbol_map.find_opt (Symbol_id.of_string name) env.symbols

let mem name env = Symbol_map.mem (Symbol_id.of_string name) env.symbols

let remove_indexed_binding key id index =
  let rec remove = function
    | [] as bindings -> bindings
    | candidate :: rest when Symbol_id.equal candidate id -> rest
    | binding :: rest as bindings ->
        let updated_rest = remove rest in
        if updated_rest == rest then bindings else binding :: updated_rest
  in
  match String_map.find_opt key index with
  | None -> index
  | Some bindings ->
      let updated = remove bindings in
      if updated == bindings then index
      else if updated = [] then String_map.remove key index
      else String_map.add key updated index

let add_indexed_binding key id index =
  String_map.update key
    (function
      | None -> Some [ id ]
      | Some bindings -> Some (id :: bindings))
    index

let update_name_count delta name counts =
  String_map.update name
    (function
      | None when delta > 0 -> Some delta
      | None -> None
      | Some count ->
          let count = count + delta in
          if count = 0 then None else Some count)
    counts

let update_name_counts delta names counts =
  List.fold_left (fun counts name -> update_name_count delta name counts) counts
    names

let binding_unresolved_declaration_names (binding : Types.binding) =
  match binding.ty with
  | Types.TOcaml "__declared_fn" -> [ binding.ocaml_name ]
  | _ when binding.forward_declared -> [ binding.ocaml_name ]
  | _ -> []

let binding_unresolved_declaration_reference_names (binding : Types.binding) =
  match binding.ty with
  | Types.TOcaml "__declared_fn" -> [ binding.ocaml_name ]
  | _ when binding.forward_declared ->
      List.sort_uniq String.compare
        (binding.ocaml_name :: binding.overload_targets)
  | _ -> []

let internal_scope ~prefix name =
  let scope_start = String.length prefix in
  if not (String.starts_with ~prefix name) then None
  else
    match String.rindex_opt name '/' with
    | Some separator when separator >= scope_start ->
        Some (String.sub name scope_start (separator - scope_start))
    | Some _ | None -> None

let record_lookup_index_key name (binding : Types.binding) =
  match (internal_scope ~prefix:"__record/" name, binding.ty) with
  | Some scope, Types.TNamed_record record ->
      Some (scope ^ "\000" ^ record.type_name)
  | Some _, _ | None, _ -> None

let opened_scope name =
  internal_scope ~prefix:"__opened/" name

let namespace_prefixes name =
  let record_prefix = "__record/" in
  let name =
    if String.starts_with ~prefix:record_prefix name then
      String.sub name (String.length record_prefix)
        (String.length name - String.length record_prefix)
    else name
  in
  let rec dotted_prefixes namespace prefixes =
    match String.rindex_opt namespace '.' with
    | None -> prefixes
    | Some separator ->
        let namespace = String.sub namespace 0 separator in
        dotted_prefixes namespace (namespace :: prefixes)
  in
  let rec collect offset prefixes =
    match String.index_from_opt name offset '/' with
    | None -> List.sort_uniq String.compare prefixes
    | Some separator ->
        let prefix = String.sub name 0 separator in
        collect (separator + 1) (dotted_prefixes prefix (prefix :: prefixes))
  in
  collect 0 []

let update_namespace_index update id name index =
  List.fold_left (fun index namespace -> update namespace id index) index
    (namespace_prefixes name)

let remove name env =
  let id = Symbol_id.of_string name in
  let previous = Symbol_map.find_opt id env.symbols in
  let bindings_by_emitted_name =
    match previous with
    | None -> env.bindings_by_emitted_name
    | Some binding ->
        remove_indexed_binding binding.Types.ocaml_name id
          env.bindings_by_emitted_name
  in
  let record_bindings_by_lookup =
    match Option.bind previous (record_lookup_index_key name) with
    | None -> env.record_bindings_by_lookup
    | Some key ->
        remove_indexed_binding key id env.record_bindings_by_lookup
  in
  let opened_bindings_by_scope =
    match opened_scope name with
    | None -> env.opened_bindings_by_scope
    | Some scope ->
        remove_indexed_binding scope id env.opened_bindings_by_scope
  in
  let bindings_by_namespace =
    match previous with
    | None -> env.bindings_by_namespace
    | Some _ ->
        update_namespace_index remove_indexed_binding id name
          env.bindings_by_namespace
  in
  let unresolved_declaration_names =
    match previous with
    | None -> env.unresolved_declaration_names
    | Some binding ->
        update_name_counts (-1)
          (binding_unresolved_declaration_reference_names binding)
          env.unresolved_declaration_names
  in
  let unresolved_declaration_binding_names =
    match previous with
    | None -> env.unresolved_declaration_binding_names
    | Some binding ->
        update_name_counts (-1)
          (binding_unresolved_declaration_names binding)
          env.unresolved_declaration_binding_names
  in
  {
    env with
    symbols = Symbol_map.remove id env.symbols;
    record_symbols = Symbol_map.remove id env.record_symbols;
    record_bindings_by_lookup;
    bindings_by_name =
      remove_indexed_binding (Symbol_id.name id) id env.bindings_by_name;
    bindings_by_emitted_name;
    bindings_by_namespace;
    opened_bindings_by_scope;
    unresolved_declaration_names;
    unresolved_declaration_binding_names;
  }

let add name binding env =
  let id = Symbol_id.of_string name in
  let previous = Symbol_map.find_opt id env.symbols in
  let bindings_by_name =
    match previous with
    | None ->
        add_indexed_binding (Symbol_id.name id) id env.bindings_by_name
    | Some _ -> env.bindings_by_name
  in
  let bindings_by_emitted_name =
    match previous with
    | Some previous
      when String.equal previous.Types.ocaml_name binding.Types.ocaml_name ->
        env.bindings_by_emitted_name
    | None -> env.bindings_by_emitted_name
    | Some previous ->
        remove_indexed_binding previous.Types.ocaml_name id
          env.bindings_by_emitted_name
  in
  let bindings_by_emitted_name =
    match previous with
    | Some previous
      when String.equal previous.Types.ocaml_name binding.Types.ocaml_name ->
        bindings_by_emitted_name
    | None | Some _ ->
        add_indexed_binding binding.Types.ocaml_name id bindings_by_emitted_name
  in
  let previous_record_key = Option.bind previous (record_lookup_index_key name) in
  let next_record_key = record_lookup_index_key name binding in
  let record_bindings_by_lookup =
    match (previous_record_key, next_record_key) with
    | Some previous_key, Some next_key when String.equal previous_key next_key ->
        env.record_bindings_by_lookup
    | None, _ -> env.record_bindings_by_lookup
    | Some key, _ ->
        remove_indexed_binding key id env.record_bindings_by_lookup
  in
  let record_bindings_by_lookup =
    match (previous_record_key, next_record_key) with
    | Some previous_key, Some next_key when String.equal previous_key next_key ->
        record_bindings_by_lookup
    | _, None -> record_bindings_by_lookup
    | _, Some key ->
        add_indexed_binding key id record_bindings_by_lookup
  in
  let opened_bindings_by_scope =
    match (previous, opened_scope name) with
    | Some _, Some _ -> env.opened_bindings_by_scope
    | None, Some scope ->
        add_indexed_binding scope id env.opened_bindings_by_scope
    | _, None -> env.opened_bindings_by_scope
  in
  let bindings_by_namespace =
    match previous with
    | Some _ -> env.bindings_by_namespace
    | None ->
        update_namespace_index add_indexed_binding id name
          env.bindings_by_namespace
  in
  let unresolved_declaration_names =
    match previous with
    | None -> env.unresolved_declaration_names
    | Some previous ->
        update_name_counts (-1)
          (binding_unresolved_declaration_reference_names previous)
          env.unresolved_declaration_names
  in
  let unresolved_declaration_names =
    update_name_counts 1 (binding_unresolved_declaration_reference_names binding)
      unresolved_declaration_names
  in
  let unresolved_declaration_binding_names =
    match previous with
    | None -> env.unresolved_declaration_binding_names
    | Some previous ->
        update_name_counts (-1)
          (binding_unresolved_declaration_names previous)
          env.unresolved_declaration_binding_names
  in
  let unresolved_declaration_binding_names =
    update_name_counts 1
      (binding_unresolved_declaration_names binding)
      unresolved_declaration_binding_names
  in
  {
    env with
    symbols = Symbol_map.add id binding env.symbols;
    record_symbols =
      (if String.starts_with ~prefix:"__record/" name then
         Symbol_map.add id binding env.record_symbols
       else Symbol_map.remove id env.record_symbols);
    record_bindings_by_lookup;
    bindings_by_name;
    bindings_by_emitted_name;
    bindings_by_namespace;
    opened_bindings_by_scope;
    unresolved_declaration_names;
    unresolved_declaration_binding_names;
  }

let add_bindings bindings env =
  List.fold_left
    (fun env (name, binding) ->
      match find_opt name env with
      | Some previous when previous == binding -> env
      | Some _ | None -> add name binding env)
    env bindings

let of_bindings bindings = add_bindings bindings empty

let to_bindings env =
  Symbol_map.bindings env.symbols
  |> List.map (fun (id, binding) -> (Symbol_id.to_string id, binding))

let fold f env initial =
  Symbol_map.fold
    (fun id binding state -> f (Symbol_id.to_string id) binding state)
    env.symbols initial

let filter_map f env =
  fold
    (fun name binding result ->
      match f name binding with None -> result | Some value -> value :: result)
    env []
  |> List.rev

let find_map f env =
  Symbol_map.find_map
    (fun id binding -> f (Symbol_id.to_string id) binding)
    env.symbols

let add_closed_sum_constructors result_ty constructors env =
  {
    env with
    closed_sum_constructors =
      (result_ty, constructors) :: env.closed_sum_constructors;
  }

let closed_sum_head = function
  | Types.TOcaml name -> Some name
  | Types.TOcaml_app (name, _) -> Some name
  | _ -> None

let variant_constructors result_ty env =
  env.closed_sum_constructors
  |> List.filter_map (fun (candidate, constructors) ->
         if Types.equal result_ty candidate then Some constructors else None)
  |> List.flatten |> List.sort_uniq compare

let is_closed_sum ty env =
  variant_constructors ty env <> []
  ||
  match closed_sum_head ty with
  | None -> false
  | Some name ->
      List.exists
        (fun (candidate, _) ->
          match closed_sum_head candidate with
          | Some candidate_name -> String.equal candidate_name name
          | None -> false)
        env.closed_sum_constructors

let closed_sum_candidates_for_payloads payload_types env =
  let rec compatible visited expected actual =
    if Types.equal expected actual then true
    else
      let key = (Types.ocaml_name expected, Types.ocaml_name actual) in
      if List.mem key visited then false
      else
        let visited = key :: visited in
        match (expected, actual) with
        | Types.TVector expected, Types.TVector actual
        | Types.TList expected, Types.TList actual
        | Types.TSeq expected, Types.TSeq actual
        | Types.TArray expected, Types.TArray actual ->
            compatible visited expected actual
        | _ ->
            env.closed_sum_constructors
            |> List.find_map (fun (candidate, constructors) ->
                   if Types.equal candidate expected then Some constructors
                   else None)
            |> Option.fold ~none:false ~some:(fun constructors ->
                   List.exists
                     (fun (_, payloads) ->
                       match payloads with
                       | [ payload ] -> compatible visited payload actual
                       | [] | _ :: _ :: _ -> false)
                     constructors)
  in
  let contains_payload constructors payload_ty =
    List.exists
      (fun (_, constructor_payloads) ->
        match constructor_payloads with
        | [ candidate ] -> compatible [] candidate payload_ty
        | [] | _ :: _ :: _ -> false)
      constructors
  in
  let candidates =
    env.closed_sum_constructors
    |> List.filter_map (fun (candidate, constructors) ->
           if List.for_all (contains_payload constructors) payload_types then
             Some (candidate, List.length constructors)
           else None)
  in
  match candidates with
  | [] -> []
  | (_, first_size) :: rest ->
      let minimum_size =
        List.fold_left
          (fun minimum (_, size) -> min minimum size)
          first_size rest
      in
      candidates
      |> List.filter_map (fun (candidate, size) ->
             if size = minimum_size then Some candidate else None)
      |> List.sort_uniq compare

let add_predicate_sum_constructors result_ty constructors env =
  {
    env with
    predicate_sum_constructors =
      (result_ty, constructors) :: env.predicate_sum_constructors;
  }

let predicate_variant_constructors result_ty env =
  env.predicate_sum_constructors
  |> List.filter_map (fun (candidate, constructors) ->
         if Types.equal result_ty candidate then Some constructors else None)
  |> List.flatten |> List.sort_uniq compare

let add_optional_sequential_adapter storage_ty element_ty adapter env =
  {
    env with
    optional_sequential_adapters =
      (storage_ty, element_ty, adapter) :: env.optional_sequential_adapters;
  }

let find_optional_sequential_adapter storage_ty env =
  env.optional_sequential_adapters
  |> List.find_map (fun (candidate, element_ty, adapter) ->
         if Types.equal storage_ty candidate then
           match element_ty with
           | Types.TOcaml_app ("__lg_optional_map_adapter", _) -> None
           | _ -> Some (element_ty, adapter)
         else None)

let add_optional_map_adapter storage_ty key_ty value_ty adapter env =
  {
    env with
    optional_sequential_adapters =
      ( storage_ty,
        Types.TOcaml_app
          ("__lg_optional_map_adapter", [ key_ty; value_ty ]),
        adapter )
      :: env.optional_sequential_adapters;
  }

let find_optional_map_adapter storage_ty env =
  env.optional_sequential_adapters
  |> List.find_map (fun (candidate, payload_ty, adapter) ->
         if Types.equal storage_ty candidate then
           match payload_ty with
           | Types.TOcaml_app
               ("__lg_optional_map_adapter", [ key_ty; value_ty ]) ->
               Some (key_ty, value_ty, adapter)
           | _ -> None
         else None)

let add_nil_value_adapter value_ty adapter env =
  {
    env with
    nil_value_adapters = (value_ty, adapter) :: env.nil_value_adapters;
  }

let find_nil_value_adapter value_ty env =
  env.nil_value_adapters
  |> List.find_map (fun (candidate, adapter) ->
         if Types.equal value_ty candidate then Some adapter else None)

let add_truthiness_adapter value_ty adapter env =
  {
    env with
    truthiness_adapters = (value_ty, adapter) :: env.truthiness_adapters;
  }

let find_truthiness_adapter value_ty env =
  env.truthiness_adapters
  |> List.find_map (fun (candidate, adapter) ->
         if Types.equal value_ty candidate then Some adapter else None)

let add_successful_call_refinement function_name parameter_index refined_ty env =
  {
    env with
    successful_call_refinements =
      (function_name, (parameter_index, refined_ty))
      :: List.remove_assoc function_name env.successful_call_refinements;
  }

let find_successful_call_refinement function_name env =
  List.assoc_opt function_name env.successful_call_refinements

let remove_successful_call_refinement function_name env =
  {
    env with
    successful_call_refinements =
      List.remove_assoc function_name env.successful_call_refinements;
  }

let add_exception_data_adapter value_ty adapter env =
  {
    env with
    exception_data_adapters =
      (value_ty, adapter) :: env.exception_data_adapters;
  }

let find_exception_data_adapter value_ty env =
  env.exception_data_adapters
  |> List.find_map (fun (candidate, adapter) ->
         if Types.equal value_ty candidate then Some adapter else None)

let add_empty_map_default target_ty factory env =
  {
    env with
    empty_map_defaults = (target_ty, factory) :: env.empty_map_defaults;
  }

let find_empty_map_default target_ty env =
  env.empty_map_defaults
  |> List.find_map (fun (candidate, factory) ->
         if Types.equal target_ty candidate then Some factory else None)

let filter_record_bindings f env =
  Symbol_map.fold
    (fun id binding result ->
      match f (Symbol_id.to_string id) binding with
      | None -> result
      | Some value -> value :: result)
    env.record_symbols []
  |> List.rev

let find_record_binding f env =
  Symbol_map.find_map
    (fun id binding -> f (Symbol_id.to_string id) binding)
    env.record_symbols

let binding_entries_named name env =
  String_map.find_opt name env.bindings_by_name
  |> Option.value ~default:[]
  |> List.filter_map (fun id ->
         Symbol_map.find_opt id env.symbols
         |> Option.map (fun binding -> (Symbol_id.to_string id, binding)))

let bindings_named name env =
  binding_entries_named name env |> List.map snd

let namespace_binding_entries namespace env =
  String_map.find_opt namespace env.bindings_by_namespace
  |> Option.value ~default:[]
  |> List.filter_map (fun id ->
         Symbol_map.find_opt id env.symbols
         |> Option.map (fun binding -> (Symbol_id.to_string id, binding)))

let bindings_emitted_as name env =
  String_map.find_opt name env.bindings_by_emitted_name
  |> Option.value ~default:[]
  |> List.filter_map (fun id ->
         Symbol_map.find_opt id env.symbols
         |> Option.map (fun binding -> (Symbol_id.to_string id, binding)))

let record_bindings_named ~scope ~type_name env =
  String_map.find_opt (scope ^ "\000" ^ type_name)
    env.record_bindings_by_lookup
  |> Option.value ~default:[]
  |> List.filter_map (fun id -> Symbol_map.find_opt id env.symbols)

let opened_bindings scope env =
  String_map.find_opt scope env.opened_bindings_by_scope
  |> Option.value ~default:[]
  |> List.filter_map (fun id -> Symbol_map.find_opt id env.symbols)

let unresolved_declaration name env =
  String_map.mem name env.unresolved_declaration_names

let unresolved_declaration_binding name env =
  String_map.mem name env.unresolved_declaration_binding_names

let add_explicit_declaration name env =
  {
    env with
    explicit_declaration_names =
      String_map.add name () env.explicit_declaration_names;
  }

let explicitly_declared name env =
  String_map.mem name env.explicit_declaration_names

let protocols env = env.protocols
let with_protocols protocols env = { env with protocols }
let protocol_evidence env = env.protocol_evidence
let with_protocol_evidence protocol_evidence env =
  { env with protocol_evidence }
let modules env = env.modules
let with_modules modules env = { env with modules }
let types env = env.types
let with_types types env = { env with types }
let signatures env = env.signatures
let with_signatures signatures env = { env with signatures }

let add_namespace_alias ~scope ~alias ~target env =
  let key = Names.scoped_key scope alias in
  { env with namespace_aliases = String_map.add key target env.namespace_aliases }

let resolve_namespace_alias ~scope alias env =
  match String_map.find_opt (Names.scoped_key scope alias) env.namespace_aliases with
  | Some _ as target -> target
  | None -> String_map.find_opt alias env.namespace_aliases

let namespace_alias_targets ~scope env =
  let prefix = scope ^ "/" in
  String_map.fold
    (fun key target targets ->
      if String.starts_with ~prefix key || not (String.contains key '/') then
        target :: targets
      else targets)
    env.namespace_aliases []

let add_core_exclusions ~scope names env =
  let exclusions =
    List.fold_left
      (fun exclusions name ->
        String_map.add (Names.scoped_key scope name) () exclusions)
      env.core_exclusions names
  in
  { env with core_exclusions = exclusions }

let core_excluded ~scope name env =
  String_map.mem (Names.scoped_key scope name) env.core_exclusions

let add_macro ~scope ~name definition env =
  let key = Names.scoped_key scope name in
  { env with macros = String_map.add key definition env.macros }

let add_macro_alias ~alias definition env =
  { env with macros = String_map.add alias definition env.macros }

let remove_macro_alias ~alias definition env =
  match String_map.find_opt alias env.macros with
  | Some current when current = definition ->
      { env with macros = String_map.remove alias env.macros }
  | Some _ | None -> env

let find_source_callable ~scope name definitions env =
  let qualified_alias =
    match String.index_opt name '/' with
    | Some index when index > 0 ->
        let alias = String.sub name 0 index in
        Option.map
          (fun namespace -> namespace ^ String.sub name index (String.length name - index))
          (resolve_namespace_alias ~scope alias env)
    | _ -> None
  in
  match qualified_alias with
  | Some canonical -> String_map.find_opt canonical definitions
  | None -> (
      match String_map.find_opt (Names.scoped_key scope name) definitions with
      | Some _ as definition -> definition
      | None -> String_map.find_opt name definitions)

let find_macro ~scope name env =
  find_source_callable ~scope name env.macros env

let namespace_macros namespace env =
  let prefix = namespace ^ "/" in
  String_map.fold
    (fun key definition macros ->
      if not (String.starts_with ~prefix key) then macros
      else
        let name =
          String.sub key (String.length prefix)
            (String.length key - String.length prefix)
        in
        (name, definition) :: macros)
    env.macros []

let add_inline_macro ~scope ~name definition env =
  let key = Names.scoped_key scope name in
  {
    env with
    inline_macros = String_map.add key definition env.inline_macros;
  }

let add_inline_macro_alias ~alias definition env =
  {
    env with
    inline_macros = String_map.add alias definition env.inline_macros;
  }

let remove_inline_macro_alias ~alias definition env =
  match String_map.find_opt alias env.inline_macros with
  | Some current when current = definition ->
      { env with inline_macros = String_map.remove alias env.inline_macros }
  | Some _ | None -> env

let find_inline_macro ~scope name env =
  find_source_callable ~scope name env.inline_macros env

let namespace_inline_macros namespace env =
  let prefix = namespace ^ "/" in
  String_map.fold
    (fun key definition macros ->
      if not (String.starts_with ~prefix key) then macros
      else
        let name =
          String.sub key (String.length prefix)
            (String.length key - String.length prefix)
        in
        (name, definition) :: macros)
    env.inline_macros []

let inline_macros env = env.inline_macros
let with_inline_macros inline_macros env = { env with inline_macros }
let clear_inline_macros env = { env with inline_macros = String_map.empty }

let without_source_callable ~scope name env =
  if Names.is_qualified name then env
  else
    let keys = List.sort_uniq String.compare [ name; Names.scoped_key scope name ] in
    {
      env with
      macros =
        List.fold_left (fun macros key -> String_map.remove key macros) env.macros
          keys;
      inline_macros =
        List.fold_left
          (fun inline_macros key -> String_map.remove key inline_macros)
          env.inline_macros keys;
    }

let source_callable_shadowed ~scope name (definition : Macro_definition.t) env =
  core_excluded ~scope name env
  && (definition.namespace = "clojure.core"
     || definition.namespace = "cljs.core")

let add_macro_function ~scope ~name definition env =
  let key = Names.scoped_key scope name in
  {
    env with
    macro_functions = String_map.add key definition env.macro_functions;
  }

let find_macro_function ~scope name env =
  match String_map.find_opt (Names.scoped_key scope name) env.macro_functions with
  | Some _ as definition -> definition
  | None -> String_map.find_opt name env.macro_functions

let add_macro_value ~scope ~name value env =
  let key = Names.scoped_key scope name in
  { env with macro_values = String_map.add key value env.macro_values }

let find_macro_value ~scope name env =
  match String_map.find_opt (Names.scoped_key scope name) env.macro_values with
  | Some _ as value -> value
  | None -> String_map.find_opt name env.macro_values

let rec anonymous_type_equal left right =
  match (left, right) with
  | Types.TRecord left, Types.TRecord right -> anonymous_fields_equal left right
  | Types.TRecord left, Types.TNamed_record { nominal = false; fields = right; _ }
  | Types.TNamed_record { nominal = false; fields = left; _ }, Types.TRecord right ->
      anonymous_fields_equal left right
  | Types.TNullable left, Types.TNullable right
  | Types.TArray left, Types.TArray right
  | Types.TRef left, Types.TRef right
  | Types.TList left, Types.TList right
  | Types.TVector left, Types.TVector right
  | Types.TSet left, Types.TSet right
  | Types.TSeq left, Types.TSeq right ->
      anonymous_type_equal left right
  | Types.TOcaml_app (left_name, left_args),
    Types.TOcaml_app (right_name, right_args)
    when left_name = right_name ->
      List.length left_args = List.length right_args
      && List.for_all2 anonymous_type_equal left_args right_args
  | Types.TConstraint left, Types.TConstraint right ->
      Types.constraint_compatible
        (fun ~expected ~actual -> anonymous_type_equal expected actual)
        left right
  | Types.TTuple left, Types.TTuple right ->
      List.length left = List.length right
      && List.for_all2 anonymous_type_equal left right
  | _ -> Types.equal left right

and anonymous_fields_equal left right =
  List.length left = List.length right
  &&
  List.for_all
    (fun (left_field : Types.field) ->
      match
        List.find_opt
          (fun (right_field : Types.field) ->
            right_field.keyword = left_field.keyword)
          right
      with
      | Some right_field -> anonymous_type_equal left_field.ty right_field.ty
      | None -> false)
    left

let rec anonymous_type_layout_compatible left right =
  match (left, right) with
  | (Types.TUnknown | Types.TMeta _ | Types.TVar _), _
  | _, (Types.TUnknown | Types.TMeta _ | Types.TVar _) ->
      true
  | Types.TRecord left, Types.TRecord right ->
      anonymous_fields_layout_compatible left right
  | Types.TRecord _, _ | _, Types.TRecord _ -> false
  | Types.TNullable left, Types.TNullable right
  | Types.TArray left, Types.TArray right
  | Types.TRef left, Types.TRef right
  | Types.TList left, Types.TList right
  | Types.TVector left, Types.TVector right
  | Types.TSet left, Types.TSet right
  | Types.TSeq left, Types.TSeq right ->
      anonymous_type_layout_compatible left right
  | Types.TOcaml_app (left_name, left_args),
    Types.TOcaml_app (right_name, right_args)
    when left_name = right_name ->
      List.length left_args = List.length right_args
      && List.for_all2 anonymous_type_layout_compatible left_args right_args
  | Types.TConstraint left, Types.TConstraint right ->
      Types.constraint_compatible
        (fun ~expected ~actual ->
          anonymous_type_layout_compatible expected actual)
        left right
  | Types.TTuple left, Types.TTuple right ->
      List.length left = List.length right
      && List.for_all2 anonymous_type_layout_compatible left right
  | _ -> Types.ocaml_name left = Types.ocaml_name right

and anonymous_fields_layout_compatible left right =
  List.length left = List.length right
  &&
  List.for_all
    (fun (left_field : Types.field) ->
      match
        List.find_opt
          (fun (right_field : Types.field) ->
            right_field.keyword = left_field.keyword)
          right
      with
      | Some right_field ->
          anonymous_type_layout_compatible left_field.ty right_field.ty
      | None -> false)
    left

(* Canonical field shape for dedup: unresolved positions (metas, declared vars,
   unknowns/nils) are alpha-renamed to positional placeholders so two
   same-shaped records allocated from different inference contexts compare
   equal. Sharing is preserved: one meta/var maps to one placeholder. *)
let canonical_anonymous_fields fields =
  let names : (string, string) Hashtbl.t = Hashtbl.create 8 in
  let next = ref 0 in
  let leaf key =
    match Hashtbl.find_opt names key with
    | Some name -> Types.TVar name
    | None ->
        incr next;
        let name = "c" ^ string_of_int !next in
        Hashtbl.add names key name;
        Types.TVar name
  in
  let rec canon = function
    | Types.TMeta meta -> leaf ("m" ^ string_of_int meta.id)
    | Types.TVar name -> leaf ("v" ^ name)
    | Types.TUnknown | Types.TNil ->
        incr next;
        Types.TVar ("cu" ^ string_of_int !next)
    | ty -> Semantic_type.map_children canon ty
  in
  List.map (fun (field : Types.field) -> { field with ty = canon field.ty }) fields

(* Prefer the earliest-allocated match: anonymous record decls are emitted at
   allocation time, so the oldest record with a given shape is the one whose
   declaration precedes the most use sites. The list is newest-first, so pick
   the smallest "t<N>" index among candidates. *)
let record_type_index (record : Semantic_type.named_record) =
  let name = record.type_name in
  let length = String.length name in
  if length > 1 && name.[0] = 't' then
    match int_of_string_opt (String.sub name 1 (length - 1)) with
    | Some index -> index
    | None -> max_int
  else max_int

let oldest_candidate candidates =
  List.fold_left
    (fun best record ->
      match best with
      | Some best when record_type_index record >= record_type_index best ->
          Some best
      | _ -> Some record)
    None candidates

let find_oldest_anonymous_record ~owner fields env =
  let matches predicate =
    env.anonymous_records
    |> List.filter_map (fun (record_owner, (record : Semantic_type.named_record)) ->
           if record_owner = owner && predicate record.fields then Some record
           else None)
    |> oldest_candidate
  in
  match matches (anonymous_fields_equal fields) with
  | Some _ as found -> found
  | None -> (
      (* Prefer the record whose site instantiation equals the query fields:
         e.g. a row `{title; uuid}` queried with `uuid = 'm` belongs to the
         record allocated for that site, not an older same-shape record. *)
      let instantiated =
        env.anonymous_records
        |> List.filter_map
             (fun (record_owner, (record : Semantic_type.named_record)) ->
               if record_owner <> owner then None
               else
                 let record_fields =
                   if
                     record.type_parameters <> []
                     && List.length record.type_parameters
                        = List.length record.type_arguments
                   then
                     let substitutions =
                       List.combine record.type_parameters
                         record.type_arguments
                       |> List.map (fun (parameter, argument) ->
                              (Type_solver.Declared parameter, argument))
                       |> Type_solver.of_list
                     in
                     List.map
                       (fun (field : Types.field) ->
                         {
                           field with
                           ty = Type_solver.apply substitutions field.ty;
                         })
                       record.fields
                   else record.fields
                 in
                 if anonymous_fields_equal fields record_fields then
                   Some record
                 else None)
        |> oldest_candidate
      in
      match instantiated with
      | Some _ as found -> found
      | None ->
          let fields = canonical_anonymous_fields fields in
          matches (fun record_fields ->
              anonymous_fields_equal fields
                (canonical_anonymous_fields record_fields)))

let find_oldest_anonymous_record_by_layout ~owner fields env =
  env.anonymous_records
  |> List.filter_map (fun (record_owner, (record : Semantic_type.named_record)) ->
         if
           record_owner = owner
           && anonymous_fields_layout_compatible fields record.fields
         then Some record
         else None)
  |> oldest_candidate

let find_anonymous_record ~owner fields env =
  env.anonymous_records
  |> List.find_map (fun (record_owner, (record : Semantic_type.named_record)) ->
         if
           record_owner = owner
           && anonymous_fields_equal fields record.fields
         then Some record
         else None)
  |> fun found ->
  match found with
  | Some _ -> found
  | None ->
      (* Stored records keep parameter names; a fresh lookup may carry raw
         metavariables. Compare canonical shapes before giving up. *)
      let fields = canonical_anonymous_fields fields in
      env.anonymous_records
      |> List.find_map (fun (record_owner, (record : Semantic_type.named_record)) ->
             if
               record_owner = owner
               && anonymous_fields_equal fields
                    (canonical_anonymous_fields record.fields)
             then Some record
             else None)

let find_anonymous_record_by_layout ~owner fields env =
  env.anonymous_records
  |> List.find_map (fun (record_owner, (record : Semantic_type.named_record)) ->
         if
           record_owner = owner
           && anonymous_fields_layout_compatible fields record.fields
         then Some record
         else None)

let find_unique_anonymous_record_by_layout fields env =
  let candidates =
    env.anonymous_records
    |> List.filter_map (fun (_, (record : Semantic_type.named_record)) ->
           if anonymous_fields_layout_compatible fields record.fields then
             Some record
           else None)
  in
  match candidates with
  | [ record ] -> Some record
  | [] | _ :: _ :: _ -> None

let find_anonymous_record_any_owner fields env =
  let fields = canonical_anonymous_fields fields in
  env.anonymous_records
  |> List.find_map (fun (_, (record : Semantic_type.named_record)) ->
         if
           anonymous_fields_equal fields
             (canonical_anonymous_fields record.fields)
         then Some record
         else None)

let add_anonymous_record ~owner record env =
  { env with anonymous_records = (owner, record) :: env.anonymous_records }

let hide_export name env =
  { env with private_exports = String_map.add name () env.private_exports }

let export_is_private env name = String_map.mem name env.private_exports

let inherit_private_exports source env =
  { env with private_exports = source.private_exports }

let remap_private_exports ~from_module ~to_module env =
  let prefix = from_module ^ "." in
  String_map.fold (fun name () env ->
    if String.starts_with ~prefix name then
      hide_export (to_module ^ String.sub name (String.length from_module)
        (String.length name - String.length from_module)) env
    else env) env.private_exports env
