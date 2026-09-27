open Types

module Env = Compiler_environment

let record_type_key scope type_name = "__record/" ^ scope ^ "/" ^ type_name

let canonical_core_name name =
  let cljs_prefix = "cljs.core/" in
  if String.starts_with ~prefix:cljs_prefix name then
    "clojure.core/"
    ^ String.sub name (String.length cljs_prefix)
        (String.length name - String.length cljs_prefix)
  else name

let canonical_core_binding_name scope env name =
  let name = canonical_core_name name in
  match String.split_on_char '/' name with
  | [ alias; member ] -> (
      match Env.resolve_namespace_alias ~scope alias env with
      | Some ("clojure.core" | "cljs.core") -> "clojure.core/" ^ member
      | Some _ | None -> name)
  | _ -> name

let canonical_host_binding_name scope env name =
  match String.split_on_char '/' name with
  | [alias; member] -> (
      match Env.resolve_namespace_alias ~scope alias env with
      | Some target when String.starts_with ~prefix:"ocaml." target -> target ^ "/" ^ member
      | _ -> name)
  | _ -> name

let lookup_type_declaration scope env type_name =
  let registry = Env.types env in
  let lookup owner local_name =
    Type_registry.emitted_name ~scope:owner local_name
    |> fun emitted_name ->
    Type_registry.find_by_emitted_name emitted_name registry
  in
  match String.rindex_opt type_name '/' with
  | Some index ->
      let alias = String.sub type_name 0 index in
      let local_name =
        String.sub type_name (index + 1) (String.length type_name - index - 1)
      in
      let resolved_owner =
        Env.resolve_namespace_alias ~scope alias env
        |> Option.value ~default:alias
      in
      (match lookup resolved_owner local_name with
      | Some _ as declaration -> declaration
      | None -> lookup alias local_name)
  | None ->
      if String.contains type_name '.' then
        Type_registry.find_by_emitted_name type_name registry
      else lookup scope type_name

let split_qualified_type_name type_name =
  match String.rindex_opt type_name '.' with
  | None -> None
  | Some index ->
      let module_path = String.sub type_name 0 index in
      let local_name =
        String.sub type_name (index + 1) (String.length type_name - index - 1)
      in
      Some (module_path, local_name)

let qualify_record_type module_path record =
  let type_name = Names.module_path_to_ocaml module_path ^ "." ^ record.type_name in
  {
    record with
    type_name;
    set_module_name =
      Names.module_path_to_ocaml module_path ^ "." ^ record.set_module_name;
  }

let lookup_record_type scope env type_name =
  let lookup owner local_name =
    match Env.find_opt (record_type_key owner local_name) env with
    | Some _ as binding -> binding
    | None -> Env.find_opt (record_type_key owner (Names.sanitize_name local_name)) env
  in
  let local_lookup owner local_name =
    match lookup owner local_name with
    | Some ({ ty = TNamed_record record; _ } : binding) -> Ok record
    | Some _ -> Error.error ("invalid record type metadata for " ^ type_name)
    | None ->
        let records =
          Env.record_bindings_named ~scope:owner ~type_name:local_name env
          |> List.filter_map (fun (binding : binding) ->
                 match binding.ty with
                 | TNamed_record record -> Some record
                 | _ -> None)
        in
        (match records with
        | [ record ] -> Ok record
        | [] | _ :: _ :: _ -> Error.error ("unknown record type " ^ type_name))
  in
  match String.rindex_opt type_name '/' with
  | Some index ->
      let alias = String.sub type_name 0 index in
      let local_name =
        String.sub type_name (index + 1) (String.length type_name - index - 1)
      in
      (match local_lookup alias local_name with
      | Ok _ as record -> record
      | Error _ ->
          let resolved_owner =
            Env.resolve_namespace_alias ~scope alias env
            |> Option.value ~default:alias
          in
          (match local_lookup (Names.sanitize_name resolved_owner) local_name with
          | Ok _ as record -> record
          | Error _ ->
              local_lookup
                (Names.module_path_to_ocaml resolved_owner)
                local_name))
  | None ->
  match split_qualified_type_name type_name with
  | Some (module_path, local_name) -> (
      match local_lookup (Names.module_path_to_ocaml module_path) local_name with
      | Ok record
        when Names.module_path_to_ocaml module_path = Names.module_path_to_ocaml scope ->
          Ok record
      | Ok record when String.contains record.type_name '.' -> Ok record
      | Ok record -> Ok (qualify_record_type module_path record)
      | Error _ as err -> err)
  | None -> local_lookup scope type_name

let lookup_binding scope env name =
  let name = canonical_core_binding_name scope env name in
  let name = canonical_host_binding_name scope env name in
  match Env.find_opt (Names.scoped_key scope name) env with
  | Some (binding : binding) -> Ok binding
  | None -> (
      (* Fully qualified calls into core namespaces resolve without an
         explicit require, mirroring Clojure's auto-loading. *)
      match Core_namespaces.lookup_qualified_member name with
      | Some (binding : binding) -> Ok binding
      | None -> Error.error ("unknown function " ^ name))

let binding_owner key =
  match String.rindex_opt key '/' with
  | None -> ""
  | Some index -> String.sub key 0 index

let check_emitted_name_collision env ~source_key ~ocaml_name =
  let owner = binding_owner source_key in
  match
    Env.bindings_emitted_as ocaml_name env
    |> List.find_map (fun (key, (binding : binding)) ->
        if
          (not (String.starts_with ~prefix:"__" key))
          && key <> source_key && binding_owner key = owner
        then Some (key, binding)
        else None)
  with
  | None -> Ok ()
  | Some (existing_key, _) ->
      let source_name = Protocol.method_basename source_key in
      let existing_name = Protocol.method_basename existing_key in
      Error.error
        ("OCaml name collision: " ^ existing_name ^ " and " ^ source_name
       ^ " both emit " ^ ocaml_name)

let lookup_host_reference scope env name =
  let name = canonical_host_binding_name scope env name in
  match Env.find_opt (Names.scoped_key scope name) env with
  | Some _ as binding -> binding
  | None -> Env.find_opt name env

let starts_with_uppercase name =
  String.length name > 0
  && Char.uppercase_ascii name.[0] = name.[0]

let opened_ocaml_call_target scope env function_name =
  Env.opened_bindings scope env
  |> List.find_map (fun (binding : binding) ->
         match binding.host_reference with
         | Some (Ocaml_module module_path) ->
             let target = module_path ^ "." ^ Names.ocaml_member_name function_name in
             (match Ocaml_signature.value_signature target with
             | Ok _ -> Some target
             | Error _ -> None)
         | _ -> None)

let ocaml_alias_module_path scope env alias =
  match Env.resolve_namespace_alias ~scope alias env with
  | Some module_name when String.starts_with ~prefix:"ocaml." module_name ->
      let prefix_length = String.length "ocaml." in
      Some
        (String.sub module_name prefix_length
           (String.length module_name - prefix_length))
  | Some _ | None -> None

let ocaml_module_member module_path member_name =
  let exact = module_path ^ "." ^ member_name in
  let sanitized = module_path ^ "." ^ Names.ocaml_member_name member_name in
  if String.exists (fun ch -> ch >= 'A' && ch <= 'Z') member_name then exact
  else sanitized

let ocaml_call_target scope env function_name =
  match lookup_host_reference scope env function_name with
  | Some { host_reference = Some (Ocaml_value ocaml_name); _ } -> Some ocaml_name
  | _ -> (
      match String.split_on_char '/' function_name with
      | [ alias; member_name ] -> (
          match ocaml_alias_module_path scope env alias with
          | Some module_path ->
              Some (ocaml_module_member module_path member_name)
          | None -> (
              match lookup_host_reference scope env alias with
          | Some { host_reference = Some (Ocaml_module module_path); _ } ->
              Some (ocaml_module_member module_path member_name)
          | None -> (
              match Host_interop.implicit_module alias with
              | Some module_path ->
                  Some (ocaml_module_member module_path member_name)
              | None when String.length alias > 0 && starts_with_uppercase alias ->
                  Some (ocaml_module_member alias member_name)
              | None -> None)
          | _ when String.length alias > 0 && starts_with_uppercase alias ->
              Some (ocaml_module_member alias member_name)
          | _ -> None))
      | _ ->
          let first_segment =
            match String.split_on_char '.' function_name with
            | first :: _ -> first
            | [] -> ""
          in
          if String.contains function_name '.' && first_segment <> ""
             && Char.uppercase_ascii first_segment.[0] = first_segment.[0]
          then Some function_name
          else opened_ocaml_call_target scope env function_name)

let resolve_ocaml_call_target scope env function_name =
  match ocaml_call_target scope env function_name with
  | Some target -> target
  | None -> function_name

let resolve_ocaml_constructor_target scope env constructor_name =
  match String.split_on_char '/' constructor_name with
  | [ alias; member_name ] -> (
      match ocaml_alias_module_path scope env alias with
      | Some module_path -> module_path ^ "." ^ member_name
      | None -> (
          match lookup_host_reference scope env alias with
      | Some { host_reference = Some (Ocaml_module module_path); _ } ->
          module_path ^ "." ^ member_name
      | _ when starts_with_uppercase alias -> alias ^ "." ^ member_name
      | _ -> constructor_name))
  | _ -> constructor_name
