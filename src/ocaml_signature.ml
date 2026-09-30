open Types
module String_set = Set.Make (String)

let rec find_project_root dir =
  if Sys.file_exists (Filename.concat dir "dune-project") then Some dir
  else
    let parent = Filename.dirname dir in
    if parent = dir then None else find_project_root parent

let existing_dirs dirs = List.filter Sys.file_exists dirs

let env_include_dirs () =
  match Sys.getenv_opt "LG_OCAML_INCLUDE_PATH" with
  | None -> []
  | Some value ->
      value |> String.split_on_char ':' |> List.filter (fun dir -> dir <> "")

let project_build_root () =
  let cwd = Sys.getcwd () in
  match find_project_root cwd with
  | Some root -> Filename.concat root "_build/default"
  | None -> cwd

let contains_compiled_interface directory =
  Sys.file_exists directory && Sys.is_directory directory
  && Sys.readdir directory
     |> Array.exists (String.ends_with ~suffix:".cmi")

let project_compiled_interface_dirs () =
  let root = project_build_root () in
  let rec scan directories directory =
    if not (Sys.file_exists directory && Sys.is_directory directory) then directories
    else
      let basename = Filename.basename directory in
      if
        List.mem basename [ ".git"; ".ppx"; "_doc"; "melange" ]
        || String.ends_with ~suffix:".eobjs" basename
      then directories
      else
        let entries =
          try Sys.readdir directory |> Array.to_list with Sys_error _ -> []
        in
        let directories =
          if
            List.mem basename [ "byte"; "public_cmi" ]
            && contains_compiled_interface directory
          then directory :: directories
          else directories
        in
        entries
        |> List.fold_left
             (fun directories entry ->
               let child = Filename.concat directory entry in
               if Sys.file_exists child && Sys.is_directory child then
                 scan directories child
               else directories)
             directories
  in
  scan [] root |> List.sort_uniq String.compare

let project_include_dirs () =
  let root = project_build_root () in
  existing_dirs
    [
      Filename.concat root "src";
      Filename.concat root "src/.lg.objs/byte";
      Filename.concat root "runtime";
      Filename.concat root "runtime/.lg_runtime.objs/byte";
      Filename.concat root "runtime_edn_backend";
      Filename.concat root
        "runtime_edn_backend/.lg_edn_backend.objs/byte";
      Filename.concat root "vendor/rrbvec";
      Filename.concat root "vendor/rrbvec/.rrbvec.objs/byte";
    ]
  @ project_compiled_interface_dirs ()

let base_include_dirs = lazy (env_include_dirs () @ project_include_dirs ())
let include_dirs () = Lazy.force base_include_dirs
let native_package_include_dirs = ref []
let melange_package_include_dirs = ref []
let melange_target = ref false
let package_include_dirs () =
  if !melange_target then melange_package_include_dirs else native_package_include_dirs
let initialized_include_dirs = ref None
let active_include_dirs_cache = ref None
let compiled_interfaces_cache = Hashtbl.create 32

let set_melange_target enabled =
  if !melange_target <> enabled then (
    melange_target := enabled;
    active_include_dirs_cache := None)

let is_melange_target () = !melange_target

let compiled_interfaces directory =
  match Hashtbl.find_opt compiled_interfaces_cache directory with
  | Some interfaces -> interfaces
  | None ->
      let interfaces =
        if Sys.file_exists directory && Sys.is_directory directory then
          Sys.readdir directory |> Array.to_list
          |> List.filter (String.ends_with ~suffix:".cmi")
          |> String_set.of_list
        else String_set.empty
      in
      Hashtbl.replace compiled_interfaces_cache directory interfaces;
      interfaces

let unique_interface_directories directories =
  List.fold_left
    (fun (directories, interfaces) directory ->
      let directory_interfaces = compiled_interfaces directory in
      if String_set.disjoint interfaces directory_interfaces then
        ( directories @ [ directory ],
          String_set.union interfaces directory_interfaces )
      else (directories, interfaces))
    ([], String_set.empty) directories
  |> fst

let active_include_dirs () =
  match !active_include_dirs_cache with
  | Some directories -> directories
  | None ->
      let project_dirs =
        if !melange_target then
          include_dirs ()
          |> List.filter_map (fun directory ->
                 if Filename.basename directory = "byte" then
                   let melange = Filename.concat (Filename.dirname directory) "melange" in
                   if Sys.file_exists melange then Some melange else None
                 else Some directory)
        else include_dirs ()
      in
      let directories =
        unique_interface_directories
          (project_dirs @ !(package_include_dirs ()))
      in
      active_include_dirs_cache := Some directories;
      directories

let unique_directories directories =
  List.fold_left
    (fun unique directory ->
      if List.mem directory unique then unique else unique @ [ directory ])
    [] directories

let ensure_initialized () =
  let dirs = active_include_dirs () in
  if !initialized_include_dirs <> Some dirs then (
    ignore (Lg_compiler_support.Ocaml_value.init ~melange:!melange_target dirs);
    initialized_include_dirs := Some dirs)

let add_include_dirs dirs =
  let package_include_dirs = package_include_dirs () in
  let updated = unique_directories (dirs @ !package_include_dirs) in
  if updated <> !package_include_dirs then (
    package_include_dirs := updated;
    active_include_dirs_cache := None);
  (* Register the directories in the global load path immediately so
     restored environments can resolve their modules, but only rebuild an
     environment that already exists — eagerly building one here can run
     before package include directories are registered, and under melange
     the stdlib interface lives in those package dirs. *)
  Lg_compiler_support.Ocaml_value.refresh_include_dirs
    ~melange:!melange_target
    (active_include_dirs ());
  if
    Option.is_some !initialized_include_dirs
    || Lg_compiler_support.Ocaml_value.environment_initialized ()
  then ensure_initialized ()

let init () = ensure_initialized ()

let same_type_path left right =
  if String.equal left right then true
  else (
    ensure_initialized ();
    let canonical name =
      Lg_compiler_support.Ocaml_value.canonical_type_path
        ~include_dirs:(active_include_dirs ()) name
    in
    String.equal (canonical left) (canonical right))

type parameter_label = Positional | Labelled of string | Optional of string
type parameter = {
  label : parameter_label;
  ty : Types.ty;
  callback_labels : Asttypes.arg_label list option;
}
type value_signature = { parameters : parameter list; return_type : Types.ty }

type constructor_signature = {
  payload_types : Types.ty list;
  result_type : Types.ty;
}

module Lookup_key = struct
  type t = string list * string

  let equal = ( = )
  let hash = Hashtbl.hash
end

module Lookup_cache = Hashtbl.Make (Lookup_key)

let value_signature_cache =
  Domain.DLS.new_key (fun () -> Lookup_cache.create 64)

let constructor_signature_cache =
  Domain.DLS.new_key (fun () -> Lookup_cache.create 32)

let type_manifest_cache =
  Domain.DLS.new_key (fun () -> Lookup_cache.create 32)

let record_type_cache =
  Domain.DLS.new_key (fun () -> Lookup_cache.create 32)

let type_manifest_resolution_stack = Domain.DLS.new_key (fun () -> ref [])
let recursive_variant_resolution_stack = Domain.DLS.new_key (fun () -> ref [])

let string_contains_substring source substring =
  let source_length = String.length source in
  let substring_length = String.length substring in
  let rec loop index =
    if index + substring_length > source_length then false
    else if String.sub source index substring_length = substring then true
    else loop (index + 1)
  in
  substring_length = 0 || loop 0

let exposes_internal_compilation_unit = function
  | TOcaml name | TOcaml_app (name, _) -> string_contains_substring name "__"
  | _ -> false

let rec of_compiler_type =
  let open Lg_compiler_support.Ocaml_value in
  function
  | Variant (tags, closed, required) ->
      let bound = if not closed then Lower_row
        else if List.length tags = List.length required then Exact_row
        else if required = [] then Upper_row else Bounded_row required in
      TPoly_variant {tags = List.map (fun (tag, payload) -> (tag, Option.map of_compiler_type payload)) tags; bound}
  | Variable id -> TVar ("ocaml_" ^ string_of_int id)
  | Arrow (Unlabelled, argument, result) ->
      let arguments, result = function_parts result in
      TFn (of_compiler_type argument :: arguments, result)
  | Arrow ((Labelled _ | Optional _), _, _) -> TOcaml "labelled_function"
  | Tuple elements -> TTuple (List.map of_compiler_type elements)
  | Constructor (name, arguments) -> (
      let name =
        match String.split_on_char '.' name with
        | "Stdlib" :: rest -> String.concat "." rest
        | _ -> name
      in
      let name = Names.canonical_runtime_path name in
      let arguments = List.map of_compiler_type arguments in
      match (name, arguments) with
      | "int", [] -> TInt
      | "int64", [] -> TOcaml "int64"
      | "Unix.file_perm", [] -> TOcaml "int"
      | "float", [] -> TFloat
      | "char", [] -> TChar
      | "string", [] -> TString
      | "Lg_runtime.Runtime_keyword.t", [] -> TKeyword
      | "bool", [] -> TBool
      | "unit", [] -> TUnit
      | "Lg_runtime.Runtime_dynamic.t", [] ->
          Types.dynamic_constraint TUnknown
      | "list", [ inner ] -> TList inner
      | "array", [ inner ] -> TArray inner
      | "Rrbvec.t", [ inner ] -> TVector inner
      | "ref", [ inner ] -> TRef inner
      | "Lg_runtime.Runtime_reference.t", [ inner ] -> TRef inner
      | name, [] -> (
          match transparent_manifest_alias name with
          | Some ty -> ty
          | None -> TOcaml name)
      | name, arguments -> TOcaml_app (name, arguments))
  | Opaque -> TOcaml "value"

and function_parts compiler_type =
  match of_compiler_type compiler_type with
  | TFn (arguments, result) -> (arguments, result)
  | result -> ([], result)

and transparent_manifest_alias name =
  let stack = Domain.DLS.get type_manifest_resolution_stack in
  let canonical_name =
    Lg_compiler_support.Ocaml_value.canonical_type_path
      ~include_dirs:(include_dirs ()) name
  in
  let variant_stack = Domain.DLS.get recursive_variant_resolution_stack in
  if List.mem canonical_name !variant_stack then Some (TOcaml canonical_name)
  else if List.mem name !stack then None
  else
    let include_dirs = include_dirs () in
    let cache = Domain.DLS.get type_manifest_cache in
    let key = (include_dirs, name) in
    match Lookup_cache.find_opt cache key with
    | Some (Ok ty)
      when (not (Types.equal ty (TOcaml name)))
           && not (exposes_internal_compilation_unit ty) ->
        Some ty
    | Some _ -> None
    | None -> (
        stack := name :: !stack;
        let manifest =
          Fun.protect
            ~finally:(fun () ->
              stack := List.filter (fun current -> current <> name) !stack)
            (fun () ->
              match
                Lg_compiler_support.Ocaml_value.lookup_type_manifest
                  ~include_dirs name
              with
              | Error message -> Error.error ~code:Error_code.Interop message
              | Ok (Lg_compiler_support.Ocaml_value.Variant _ as compiler_type) ->
                  variant_stack := canonical_name :: !variant_stack;
                  Fun.protect
                    ~finally:(fun () ->
                      variant_stack := List.filter (( <> ) canonical_name) !variant_stack)
                    (fun () -> Ok (of_compiler_type compiler_type))
              | Ok compiler_type -> Ok (of_compiler_type compiler_type))
        in
        Lookup_cache.add cache key manifest;
        match manifest with
        | Ok ty
          when (not (Types.equal ty (TOcaml name)))
               && not (exposes_internal_compilation_unit ty) ->
            Some ty
        | Ok _ | Error _ -> None)

let callback_parameter_type compiler_type =
  let open Lg_compiler_support.Ocaml_value in
  let rec arrows labels parameters = function
    | Arrow (label, argument, result) ->
        let label = match label with
          | Unlabelled -> Asttypes.Nolabel
          | Labelled name -> Asttypes.Labelled name
          | Optional name -> Asttypes.Optional name in
        arrows (label :: labels) (of_compiler_type argument :: parameters) result
    | result ->
        let labels = List.rev labels in
        if List.exists (( <> ) Asttypes.Nolabel) labels then
          Some (TFn (List.rev parameters, of_compiler_type result), labels)
        else None in
  match compiler_type with
  | Constructor ("option", [ inner ]) -> (
      match arrows [] [] inner with
      | Some (ty, labels) -> TNullable ty, Some labels
      | None -> of_compiler_type compiler_type, None)
  | _ -> (
      match arrows [] [] compiler_type with
      | Some (ty, labels) -> ty, Some labels
      | None -> of_compiler_type compiler_type, None)

let rec signature_of_compiler_type =
  let open Lg_compiler_support.Ocaml_value in
  function
  | Arrow (label, argument, result) ->
      let signature = signature_of_compiler_type result in
      let label =
        match label with
        | Unlabelled -> Positional
        | Labelled name -> Labelled name
        | Optional name -> Optional name
      in
      let ty, callback_labels = callback_parameter_type argument in
      {
        signature with
        parameters =
          { label; ty; callback_labels } :: signature.parameters;
      }
  | compiler_type ->
      { parameters = []; return_type = of_compiler_type compiler_type }

let value_signature name =
  let include_dirs = include_dirs () in
  let cache = Domain.DLS.get value_signature_cache in
  let key = (include_dirs, name) in
  match Lookup_cache.find_opt cache key with
  | Some signature -> signature
  | None ->
      let signature =
        match Lg_compiler_support.Ocaml_value.lookup ~include_dirs name with
        | Error message -> Error.error ~code:Error_code.Interop message
        | Ok compiler_type -> Ok (signature_of_compiler_type compiler_type)
      in
      Lookup_cache.add cache key signature;
      signature

let constructor_signature name =
  let include_dirs = include_dirs () in
  let cache = Domain.DLS.get constructor_signature_cache in
  let key = (include_dirs, name) in
  match Lookup_cache.find_opt cache key with
  | Some signature -> signature
  | None ->
      let signature =
        match
          Lg_compiler_support.Ocaml_value.lookup_constructor ~include_dirs name
        with
        | Error message -> Error.error ~code:Error_code.Interop message
        | Ok constructor ->
            Ok
              {
                payload_types =
                  List.map of_compiler_type constructor.arguments;
                result_type = of_compiler_type constructor.result;
              }
      in
      Lookup_cache.add cache key signature;
      signature

let type_manifest name =
  let include_dirs = include_dirs () in
  let cache = Domain.DLS.get type_manifest_cache in
  let key = (include_dirs, name) in
  match Lookup_cache.find_opt cache key with
  | Some manifest -> manifest
  | None ->
      let manifest =
        match
          Lg_compiler_support.Ocaml_value.lookup_type_manifest ~include_dirs name
        with
        | Error message -> Error.error ~code:Error_code.Interop message
        | Ok compiler_type -> Ok (of_compiler_type compiler_type)
      in
      Lookup_cache.add cache key manifest;
      manifest

let keyword_of_label_name label_name =
  ":"
  ^ String.map
      (function
        | '_' -> '-'
        | character -> character)
      label_name

let set_module_name name = "Set_" ^ Names.sanitize_name name

let record_type name =
  let include_dirs = include_dirs () in
  let cache = Domain.DLS.get record_type_cache in
  let key = (include_dirs, name) in
  match Lookup_cache.find_opt cache key with
  | Some record -> record
  | None ->
      let record =
        match Lg_compiler_support.Ocaml_value.lookup_record ~include_dirs name with
        | Error message -> Error.error ~code:Error_code.Interop message
        | Ok record ->
            let fields =
              List.map
                (fun (field : Lg_compiler_support.Ocaml_value.record_field) ->
                  Types.make_field ~mutable_:field.mutable_
                    (keyword_of_label_name field.label_name)
                    (of_compiler_type field.label_type))
                record.fields
            in
            Ok
              (Types.named_record ~nominal:false ~type_name:name
                 ~set_module_name:(set_module_name name) fields)
      in
      Lookup_cache.add cache key record;
      record

let field_type type_name field_name =
  match record_type type_name with
  | Ok (TNamed_record record) -> (
      match List.find_opt (fun (field : Types.field) -> field.ocaml_name = field_name) record.fields with
      | Some field -> Ok field.ty
      | None -> Error.error ~code:Error_code.Unresolved ("unknown field " ^ field_name ^ " in " ^ type_name))
  | Ok _ -> Error.error ~code:Error_code.Interop ("OCaml type " ^ type_name ^ " is not a record")
  | Error _ as error -> error

let parameter_label_name = function
  | Positional -> None
  | Labelled name | Optional name -> Some name

let supplied_argument_type parameter =
  match (parameter.label, parameter.ty) with
  | Optional _, (TNullable ty | TOcaml_app ("option", [ ty ])) -> ty
  | _ -> parameter.ty

let parse_argument_forms forms =
  let rec parse acc = function
    | [] -> Ok (List.rev acc)
    | Ast.FKeyword label :: [] ->
        Error.error ~code:Error_code.Interop ("OCaml argument label " ^ label ^ " requires a value")
    | Ast.FKeyword label :: value :: rest ->
        let label = String.sub label 1 (String.length label - 1) in
        parse ((Some label, value) :: acc) rest
    | value :: rest -> parse ((None, value) :: acc) rest
  in
  parse [] forms

let applied_parameters signature arguments =
  let named_labels = List.filter_map fst arguments in
  let remaining =
    List.filter
      (fun parameter ->
        match parameter_label_name parameter.label with
        | Some label -> not (List.mem label named_labels)
        | None -> true)
      signature.parameters
  in
  let find_named label =
    signature.parameters
    |> List.find_opt (fun parameter ->
           parameter_label_name parameter.label = Some label)
  in
  let rec consume_positional prefix = function
    | [] -> None
    | { label = Optional _; _ } :: parameters ->
        consume_positional prefix parameters
    | ({ label = Labelled _; _ } as parameter) :: parameters ->
        consume_positional (parameter :: prefix) parameters
    | ({ label = Positional; _ } as parameter) :: parameters ->
        Some (parameter, List.rev_append prefix parameters)
  in
  let rec collect collected remaining = function
    | [] -> Some (List.rev collected)
    | (Some label, _) :: rest ->
        Option.bind (find_named label) (fun ty ->
            collect (ty :: collected) remaining rest)
    | (None, _) :: rest ->
        Option.bind (consume_positional [] remaining) (fun (ty, remaining) ->
            collect (ty :: collected) remaining rest)
  in
  collect [] remaining arguments

let expected_argument_types signature arguments =
  applied_parameters signature arguments
  |> Option.map (List.map supplied_argument_type)

let result_after_application signature arguments =
  let argument_labels = List.map fst arguments in
  let named_labels = List.filter_map Fun.id argument_labels in
  let rec reject_duplicate seen = function
    | [] -> Ok ()
    | label :: rest ->
        if List.mem label seen then
          Error.error ~code:Error_code.Duplicate ("duplicate OCaml argument label :" ^ label)
        else reject_duplicate (label :: seen) rest
  in
  let known_label label =
    List.exists
      (fun parameter -> parameter_label_name parameter.label = Some label)
      signature.parameters
  in
  match reject_duplicate [] named_labels with
  | Error _ as err -> err
  | Ok () -> (
      match
        List.find_opt (fun label -> not (known_label label)) named_labels
      with
      | Some label -> Error.error ~code:Error_code.Unresolved ("unknown OCaml argument label :" ^ label)
      | None -> (
          let consumed_named =
            arguments
            |> List.filter_map (function
              | None, _ -> None
              | Some label, actual_ty ->
                  signature.parameters
                  |> List.find_opt (fun parameter ->
                      parameter_label_name parameter.label = Some label)
                  |> Option.map (fun parameter ->
                         (supplied_argument_type parameter, actual_ty)))
          in
          let remaining =
            List.filter
              (fun parameter ->
                match parameter_label_name parameter.label with
                | Some label -> not (List.mem label named_labels)
                | None -> true)
              signature.parameters
          in
          let rec consume_positionals consumed remaining = function
            | [] -> Ok (consumed, remaining)
            | (Some _, _) :: rest -> consume_positionals consumed remaining rest
            | (None, actual_ty) :: rest ->
                let rec consume prefix = function
                  | [] -> Error.error ~code:Error_code.Interop "too many positional OCaml arguments"
                  | { label = Optional _; _ } :: parameters ->
                      consume prefix parameters
                  | ({ label = Labelled _; _ } as parameter) :: parameters ->
                      consume (parameter :: prefix) parameters
                  | { label = Positional; ty; _ } :: parameters ->
                      consume_positionals
                        ((ty, actual_ty) :: consumed)
                        (List.rev_append prefix parameters)
                        rest
                in
                consume [] remaining
          in
          match consume_positionals consumed_named remaining arguments with
          | Error _ as err -> err
          | Ok (consumed, parameters) ->
              let result_ty =
                match parameters with
                | [] -> signature.return_type
                | parameters
                  when List.for_all
                         (fun parameter -> parameter.label = Positional)
                         parameters ->
                    TFn
                      ( List.map (fun parameter -> parameter.ty) parameters,
                        signature.return_type )
                | _ -> TOcaml "labelled_function"
              in
              let templates, actuals = List.split consumed in
              Ok (Types.instantiate_type ~templates ~actuals result_ty)))
