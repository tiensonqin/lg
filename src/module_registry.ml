module Signature_map = Map.Make (Signature_id)
module Signature_set = Set.Make (Signature_id)
module Functor_map = Map.Make (Functor_id)
module Module_map = Map.Make (Module_id)
module Module_set = Set.Make (Module_id)
module Emitted_module_map = Map.Make (String)
module Emitted_signature_map = Map.Make (String)

type module_kind = Concrete | Alias | Functor | Applied

type module_declaration = {
  module_id : Module_id.t;
  kind : module_kind;
}

type t = {
  signatures : Lowered.signature_item list Signature_map.t;
  emitted_signatures : Signature_id.t Emitted_signature_map.t;
  functor_results : (string * Types.binding) list Functor_map.t;
  functor_parameters : string list Functor_map.t;
  functor_protocols : Protocol_registry.t Functor_map.t;
  functor_types : Type_registry.t Functor_map.t;
  functor_modules : module_declaration list Functor_map.t;
  functor_aliases : (Module_id.t * Module_id.t) list Functor_map.t;
  aliases : Module_id.t Module_map.t;
  module_declarations : module_declaration Emitted_module_map.t;
}

let empty =
  {
    signatures = Signature_map.empty;
    emitted_signatures = Emitted_signature_map.empty;
    functor_results = Functor_map.empty;
    functor_parameters = Functor_map.empty;
    functor_protocols = Functor_map.empty;
    functor_types = Functor_map.empty;
    functor_modules = Functor_map.empty;
    functor_aliases = Functor_map.empty;
    aliases = Module_map.empty;
    module_declarations = Emitted_module_map.empty;
  }

let declare_signature signature_id items registry =
  if Signature_map.mem signature_id registry.signatures then
    Error.error ~code:Error_code.Duplicate
      ("duplicate module signature " ^ Signature_id.to_string signature_id)
  else
    let emitted_name =
      String.concat "."
        (Signature_id.owner signature_id @ [ Signature_id.name signature_id ])
      |> Names.module_path_to_ocaml
    in
    match Emitted_signature_map.find_opt emitted_name registry.emitted_signatures with
    | Some existing ->
        Error.error ~code:Error_code.Interop
          ("OCaml module type name collision: " ^ Signature_id.to_string existing
         ^ " and " ^ Signature_id.to_string signature_id ^ " both emit "
         ^ emitted_name)
    | None ->
        Ok
          {
            registry with
            signatures = Signature_map.add signature_id items registry.signatures;
            emitted_signatures =
              Emitted_signature_map.add emitted_name signature_id
                registry.emitted_signatures;
          }

let find_signature signature_id registry =
  Signature_map.find_opt signature_id registry.signatures

let find_signature_named ~owner name registry =
  Signature_map.to_seq registry.signatures
  |> Seq.find_map (fun (signature_id, items) ->
         if
           Signature_id.owner signature_id = owner
           && (Signature_id.name signature_id = name
              || Names.module_path_to_ocaml (Signature_id.name signature_id) = name)
         then Some (signature_id, items)
         else None)

let expanded_signature signature_id registry =
  let rec expand visiting signature_id =
    match find_signature_named ~owner:(Signature_id.owner signature_id)
            (Signature_id.name signature_id) registry with
    | None -> Ok []
    | Some (resolved_id, items) ->
        if Signature_set.mem resolved_id visiting then
          Error.error ~code:Error_code.Semantic ("cyclic module signature include " ^ Signature_id.to_string resolved_id)
        else
          let visiting = Signature_set.add resolved_id visiting in
          let rec collect acc = function
            | [] -> Ok (Signature_types.resolve_manifests (List.rev acc))
            | Lowered.Signature_include {module_signature; type_constraints; _} :: rest ->
                let included = Signature_id.create ~owner:(Signature_id.owner resolved_id)
                    ~name:module_signature in
                Result.bind (expand visiting included) (fun items ->
                  Result.bind (Signature_types.apply ~resolve_module:(fun name -> expand visiting (Signature_id.create ~owner:(Signature_id.owner resolved_id) ~name)) type_constraints items) (fun items ->
                    collect (List.rev_append items acc) rest))
            | item :: rest -> collect (item :: acc) rest
          in
          collect [] items
  in
  expand Signature_set.empty signature_id

let abstract_signature_types signature_id registry =
  match expanded_signature signature_id registry with
  | Error _ -> []
  | Ok items -> List.filter_map (function
      | Lowered.Signature_type {type_name; manifest = None; _} -> Some type_name
      | _ -> None) items

let store_functor_result functor_id bindings registry =
  {
    registry with
    functor_results = Functor_map.add functor_id bindings registry.functor_results;
  }

let find_functor_result functor_id registry =
  Functor_map.find_opt functor_id registry.functor_results

let store_functor_protocols functor_id protocols registry =
  {
    registry with
    functor_protocols = Functor_map.add functor_id protocols registry.functor_protocols;
  }

let find_functor_protocols functor_id registry =
  Functor_map.find_opt functor_id registry.functor_protocols

let store_functor_types functor_id types registry =
  { registry with
    functor_types = Functor_map.add functor_id types registry.functor_types;
  }

let find_functor_types functor_id registry =
  Functor_map.find_opt functor_id registry.functor_types

let module_path module_id =
  String.concat "." (Module_id.owner module_id @ [ Module_id.name module_id ])

let store_functor_modules functor_id source registry =
  let prefix = Functor_id.to_string functor_id ^ "." in
  let modules =
    Emitted_module_map.fold
      (fun _ declaration modules ->
        if
          declaration.kind <> Alias
          && String.starts_with ~prefix (module_path declaration.module_id)
        then declaration :: modules
        else modules)
      source.module_declarations []
  in
  { registry with
    functor_modules = Functor_map.add functor_id modules registry.functor_modules;
  }

let store_functor_aliases functor_id source registry =
  let functor_path = Functor_id.to_string functor_id in
  let aliases =
    Module_map.fold
      (fun alias target aliases ->
        match Module_id.owner alias with
        | [ owner ]
          when owner = functor_path
               || String.starts_with ~prefix:(functor_path ^ ".") owner ->
            (alias, target) :: aliases
        | _ -> aliases)
      source.aliases []
  in
  { registry with
    functor_aliases = Functor_map.add functor_id aliases registry.functor_aliases;
  }

let emitted_module_name module_id =
  String.concat "." (Module_id.owner module_id @ [ Module_id.name module_id ])
  |> Names.module_path_to_ocaml

let declare_module module_id kind registry =
  let emitted_name = emitted_module_name module_id in
  match Emitted_module_map.find_opt emitted_name registry.module_declarations with
  | Some existing when Module_id.equal existing.module_id module_id ->
      Error.error ~code:Error_code.Duplicate ("duplicate module " ^ Module_id.to_string module_id)
  | Some existing ->
      Error.error ~code:Error_code.Interop
        ("OCaml module name collision: " ^ Module_id.to_string existing.module_id
       ^ " and " ^ Module_id.to_string module_id ^ " both emit " ^ emitted_name)
  | None ->
      Ok
        {
          registry with
          module_declarations =
            Emitted_module_map.add emitted_name { module_id; kind }
              registry.module_declarations;
        }

let apply_functor_modules ~module_name ~functor_name registry =
  let functor_id = Functor_id.of_string functor_name in
  let remap_path path =
    module_name
    ^ String.sub path (String.length functor_name)
        (String.length path - String.length functor_name)
  in
  let module_id_of_path path =
    match String.rindex_opt path '.' with
    | None -> Module_id.create ~owner:[] ~name:path
    | Some separator ->
        let owner = String.sub path 0 separator in
        let name =
          String.sub path (separator + 1)
            (String.length path - separator - 1)
        in
        Module_id.create ~owner:[ owner ] ~name
  in
  let rec apply registry = function
    | [] -> Ok registry
    | declaration :: rest ->
        let module_id =
          declaration.module_id |> module_path |> remap_path |> module_id_of_path
        in
        (match declare_module module_id declaration.kind registry with
        | Error _ as err -> err
        | Ok registry -> apply registry rest)
  in
  match Functor_map.find_opt functor_id registry.functor_modules with
  | None -> Ok registry
  | Some modules -> apply registry modules

let mem_module module_id registry =
  Emitted_module_map.mem (emitted_module_name module_id)
    registry.module_declarations

let module_bindings registry = Emitted_module_map.bindings registry.module_declarations

let signature_bindings registry =
  Emitted_signature_map.bindings registry.emitted_signatures

let add_alias alias target registry =
  { registry with aliases = Module_map.add alias target registry.aliases }

let declare_alias alias target registry =
  declare_module alias Alias registry
  |> Result.map (add_alias alias target)

let apply_functor_aliases ~module_name ~functor_name registry =
  let functor_id = Functor_id.of_string functor_name in
  let remap_path path =
    if path = functor_name then module_name
    else if String.starts_with ~prefix:(functor_name ^ ".") path then
      module_name
      ^ String.sub path (String.length functor_name)
          (String.length path - String.length functor_name)
    else path
  in
  let remap_target target =
    Module_id.create ~owner:[] ~name:(remap_path (Module_id.to_string target))
  in
  let rec apply registry = function
    | [] -> Ok registry
    | (alias, target) :: rest ->
        let alias_path =
          match Module_id.owner alias with
          | [ owner ] -> remap_path (owner ^ "." ^ Module_id.name alias)
          | _ -> remap_path (Module_id.to_string alias)
        in
        let alias = Module_id.create ~owner:[] ~name:alias_path in
        (match declare_alias alias (remap_target target) registry with
        | Error _ as err -> err
        | Ok registry -> apply registry rest)
  in
  match Functor_map.find_opt functor_id registry.functor_aliases with
  | None -> Ok registry
  | Some aliases -> apply registry aliases

let find_alias alias registry = Module_map.find_opt alias registry.aliases

let resolve_alias ~scope module_path registry =
  let top = Module_id.create ~owner:[] ~name:module_path in
  let scoped =
    if scope = "" then top
    else Module_id.create ~owner:[ scope ] ~name:module_path
  in
  let initial =
    if Module_map.mem scoped registry.aliases then Some scoped
    else if Module_map.mem top registry.aliases then Some top
    else None
  in
  let rec resolve visited module_id =
    if Module_set.mem module_id visited then None
    else
      match Module_map.find_opt module_id registry.aliases with
      | None -> Some module_id
      | Some target ->
          let target =
            if scope <> "" && Module_id.owner target = [] then
              let local =
                Module_id.create ~owner:[ scope ] ~name:(Module_id.name target)
              in
              if Module_map.mem local registry.aliases then local else target
            else target
          in
          resolve (Module_set.add module_id visited) target
  in
  Option.bind initial (resolve Module_set.empty)

let store_functor_parameters functor_id parameters registry =
  {registry with functor_parameters = Functor_map.add functor_id parameters registry.functor_parameters}

let find_functor_parameters functor_id registry =
  Functor_map.find_opt functor_id registry.functor_parameters
