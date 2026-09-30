open Types
open Lowered
module Env = Compiler_environment
module Signature_set = Set.Make (Signature_id)

let parameter_value_binding parameter_name value_path (binding : binding) =
  match String.rindex_opt value_path '/' with
  | None ->
      ( Module_environment.binding_key parameter_name value_path,
        {
          binding with
          ocaml_name =
            Names.module_segment_to_ocaml parameter_name
            ^ "." ^ binding.ocaml_name;
        } )
  | Some separator ->
      let nested_path = String.sub value_path 0 separator in
      let value_name =
        String.sub value_path (separator + 1)
          (String.length value_path - separator - 1)
      in
      let parameter_path = parameter_name ^ "." ^ nested_path in
      ( Module_environment.binding_key parameter_path value_name,
        {
          binding with
          ocaml_name =
            Names.module_path_to_ocaml parameter_path ^ "." ^ binding.ocaml_name;
        } )

let typed_signature_bindings ?(module_path = "") modules signature_id =
  let qualify prefix (path, binding) = (prefix ^ "/" ^ path, binding) in
  let nested_path module_path name = if module_path = "" then name else module_path ^ "." ^ name in
  let rec expand visiting module_path signature_id =
    match Module_registry.find_signature_named ~owner:(Signature_id.owner signature_id)
      (Signature_id.name signature_id) modules with
    | None -> Ok []
    | Some (resolved_id, _) ->
        if Signature_set.mem resolved_id visiting then
          Error.error ~code:Error_code.Semantic ("cyclic module signature include " ^ Signature_id.to_string resolved_id)
        else Result.bind (Module_registry.expanded_signature resolved_id modules)
          (collect_items (Signature_set.add resolved_id visiting) module_path (Signature_id.owner resolved_id))
  and collect_items visiting module_path owner items =
    let aliases = List.filter_map (function
      | Signature_type {type_name; type_parameters; manifest; _} ->
          let full_name = nested_path module_path type_name in
          let abstract = match type_parameters with
            | [] -> TOcaml full_name
            | parameters -> TOcaml_app (full_name, List.map (fun name -> TVar name) parameters) in
          Some (type_name, (type_parameters, Option.value manifest ~default:abstract))
      | _ -> None) items in
    let items = Signature_types.substitute aliases items in
    let rec collect bindings = function
      | [] -> Ok (List.rev bindings |> List.concat)
      | Signature_value {source_name; value_name; value_type; _} :: rest ->
          collect ([source_name, Types.binding value_name value_type] :: bindings) rest
      | Signature_type _ :: rest -> collect bindings rest
      | Signature_module {source_name; module_name; module_signature; _} :: rest ->
          Result.bind (expand visiting (nested_path module_path module_name)
            (Signature_id.create ~owner ~name:module_signature))
            (fun nested -> collect (List.map (qualify source_name) nested :: bindings) rest)
      | Signature_inline_module {source_name; module_name; items; _} :: rest ->
          Result.bind (collect_items visiting (nested_path module_path module_name) owner items)
            (fun nested -> collect (List.map (qualify source_name) nested :: bindings) rest)
      | Signature_include {module_signature; _} :: rest ->
          Result.bind (expand visiting module_path (Signature_id.create ~owner ~name:module_signature))
            (fun included -> collect (included :: bindings) rest) in
    collect [] items
  in
  expand Signature_set.empty module_path signature_id

let signature_parameter_bindings ~scope env parameter_name signature_name =
  let signature_id =
    Signature_id.create
      ~owner:(if scope = "" then [] else [ scope ])
      ~name:signature_name
  in
  typed_signature_bindings
    ~module_path:(Names.module_path_to_ocaml parameter_name)
    (Env.modules env) signature_id
  |> Result.map
       (List.map (fun (value_path, binding) ->
            parameter_value_binding parameter_name value_path binding))

let apply_stored_functor_result module_name functor_name public_bindings =
  let prefix = functor_name ^ "/" in
  let prefix_len = String.length prefix in
  let nested_prefix = functor_name ^ "." in
  let nested_prefix_len = String.length nested_prefix in
  let record_prefix = "__record/" ^ functor_name ^ "/" in
  let record_prefix_len = String.length record_prefix in
  public_bindings
  |> List.filter_map (fun (key, (binding : binding)) ->
      let remap_binding =
        let from_module = Names.module_path_to_ocaml functor_name in
        let to_module = Names.module_path_to_ocaml module_name in
        let ocaml_name =
          if binding.ocaml_name = from_module then to_module
          else if
            String.starts_with ~prefix:(from_module ^ ".") binding.ocaml_name
          then
            to_module
            ^ String.sub binding.ocaml_name
                (String.length from_module)
                (String.length binding.ocaml_name - String.length from_module)
          else binding.ocaml_name
        in
        let protocol_id =
          Option.map
            (fun protocol_id ->
              match Protocol_id.owner protocol_id with
              | [ owner ] when owner = functor_name ->
                  Protocol_id.create ~owner:[ module_name ]
                    ~name:(Protocol_id.name protocol_id)
              | [ owner ]
                when String.starts_with ~prefix:(functor_name ^ ".") owner ->
                  Protocol_id.create
                    ~owner:
                      [
                        module_name
                        ^ String.sub owner
                            (String.length functor_name)
                            (String.length owner - String.length functor_name);
                      ]
                    ~name:(Protocol_id.name protocol_id)
              | _ -> protocol_id)
            binding.protocol_id
        in
        {
          binding with
          ocaml_name;
          ty =
            Types.remap_module_type
              ~from_path:(Names.module_path_to_ocaml functor_name)
              ~to_path:(Names.module_path_to_ocaml module_name)
              binding.ty;
          protocol_id;
        }
      in
      if String.length key > prefix_len && String.sub key 0 prefix_len = prefix
      then
        let value_name =
          String.sub key prefix_len (String.length key - prefix_len)
        in
        Some
          (Module_environment.binding_key module_name value_name, remap_binding)
      else if
        String.length key > nested_prefix_len
        && String.sub key 0 nested_prefix_len = nested_prefix
      then
        let suffix =
          String.sub key nested_prefix_len
            (String.length key - nested_prefix_len)
        in
        let remapped_key = module_name ^ "." ^ suffix in
        Some (remapped_key, remap_binding)
      else if
        String.length key > record_prefix_len
        && String.sub key 0 record_prefix_len = record_prefix
      then
        let type_name =
          String.sub key record_prefix_len
            (String.length key - record_prefix_len)
        in
        Some (Resolver.record_type_key module_name type_name, remap_binding)
      else None)

let apply_parameter_types env functor_name arguments ty =
  match Module_registry.find_functor_parameters (Functor_id.of_string functor_name) (Env.modules env) with
  | Some parameters when List.length parameters = List.length arguments ->
      List.fold_left2 (fun ty parameter argument ->
        Types.remap_module_type ~from_path:(Names.module_path_to_ocaml parameter)
          ~to_path:(Names.module_path_to_ocaml argument) ty) ty parameters arguments
  | _ -> ty

let apply_functor_result_bindings env module_name functor_name arguments =
  let functor_id = Functor_id.of_string functor_name in
  match Module_registry.find_functor_result functor_id (Env.modules env) with
  | Some bindings ->
      apply_stored_functor_result module_name functor_name bindings
      |> List.map (fun (key, (binding : Types.binding)) ->
          let map = apply_parameter_types env functor_name arguments in
          (key, {binding with ty = map binding.ty;
            scheme = Option.map (fun (scheme : Types.scheme) -> {scheme with body = map scheme.body}) binding.scheme}))
  | None -> []

let apply_functor_protocols env module_name functor_name =
  let functor_id = Functor_id.of_string functor_name in
  match Module_registry.find_functor_protocols functor_id (Env.modules env) with
  | None -> Env.protocols env
  | Some protocols ->
      Protocol_registry.export_owner ~from_owner:[ functor_name ]
        ~to_owner:[ module_name ]
        ~from_module:(Names.module_path_to_ocaml functor_name)
        ~to_module:(Names.module_path_to_ocaml module_name)
        protocols (Env.protocols env)

let apply_functor_types env module_name functor_name arguments =
  let functor_id = Functor_id.of_string functor_name in
  match Module_registry.find_functor_types functor_id (Env.modules env) with
  | None -> Ok (Env.types env)
  | Some types ->
      Type_registry.export_scope ~from_scope:functor_name ~to_scope:module_name
        ~map_manifest:(apply_parameter_types env functor_name arguments)
        types (Env.types env)
