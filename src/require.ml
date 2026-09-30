open Ast
open Types

module Env = Compiler_environment

type require_spec =
  | Package of string
  | Load of { module_name : string }
  | Alias of {
      module_name : string;
      alias : string;
    }
  | Refer of {
      module_name : string;
      names : string list;
    }

let ocaml_value name ty = Types.binding ~host_reference:(Ocaml_value name) name ty

let ocaml_host_functions = function
  | "ocaml.Stdlib" ->
      [
        ("string-of-int", ocaml_value "string_of_int" (TFn ([ TInt ], TString)));
        ("int-of-string", ocaml_value "int_of_string" (TFn ([ TString ], TInt)));
      ]
  | "ocaml.String" ->
      [
        ( "uppercase-ascii",
          ocaml_value "String.uppercase_ascii" (TFn ([ TString ], TString)) );
        ("length", ocaml_value "Lg_runtime.Runtime_string.length"
          (TFn ([ TString ], TInt)));
      ]
  | _ -> []

let ocaml_module_path module_name =
  let prefix = "ocaml." in
  if String.starts_with ~prefix module_name then
    String.sub module_name (String.length prefix)
      (String.length module_name - String.length prefix)
  else module_name

let core_bindings = function
  | module_name -> Core_namespaces.bindings module_name

let core_namespace = function
  | module_name -> Core_namespaces.is_core_namespace module_name

let namespace_bindings env module_name =
  let value_prefix = module_name ^ "/" in
  let record_prefix = "__record/" ^ module_name ^ "/" in
  Env.namespace_binding_entries module_name env
  |> List.filter_map
    (fun (key, binding) ->
      if String.starts_with ~prefix:value_prefix key then
        let name =
          String.sub key (String.length value_prefix)
            (String.length key - String.length value_prefix)
        in
        Some (`Value name, binding)
      else if String.starts_with ~prefix:record_prefix key then
        let name =
          String.sub key (String.length record_prefix)
            (String.length key - String.length record_prefix)
        in
        Some (`Record name, binding)
      else None)

let add_core_alias_bindings env module_name alias =
  let source_module_name =
    if String.equal module_name "cljs.core" then "clojure.core"
    else module_name
  in
  let source_bindings = namespace_bindings env source_module_name in
  let source_value_names =
    source_bindings
    |> List.filter_map (function
         | `Value name, _ -> Some name
         | `Record _, _ -> None)
  in
  let primitive_bindings =
    core_bindings module_name
    |> List.filter (fun (name, _) ->
           not (List.exists (String.equal name) source_value_names))
    |> List.map (fun (name, binding) -> (`Value name, binding))
  in
  let env =
    source_bindings @ primitive_bindings
    |> List.map (function
         | `Value name, binding -> (alias ^ "/" ^ name, binding)
         | `Record name, binding ->
             ("__record/" ^ alias ^ "/" ^ name, binding))
    |> fun bindings -> Env.add_bindings bindings env
  in
  let env =
    Env.namespace_macros source_module_name env
    |> List.fold_left
         (fun env (name, definition) ->
           Env.add_macro_alias ~alias:(alias ^ "/" ^ name) definition env)
         env
  in
  Env.namespace_inline_macros source_module_name env
  |> List.fold_left
       (fun env (name, definition) ->
         Env.add_inline_macro_alias ~alias:(alias ^ "/" ^ name) definition env)
       env

let add_source_core_bindings env scope =
  let env =
    namespace_bindings env "clojure.core"
    |> List.fold_left
         (fun env -> function
           | `Value name, binding ->
               Env.add (Names.scoped_key scope name) binding env
           | `Record _, _ -> env)
         env
  in
  let env =
    Env.namespace_macros "clojure.core" env
    |> List.fold_left
         (fun env (name, definition) ->
           env
           |> Env.add_macro_alias ~alias:(Names.scoped_key scope name) definition
           |> Env.add_macro_alias ~alias:(Names.scoped_key "cljs.core" name)
                definition)
         env
  in
  Env.namespace_inline_macros "clojure.core" env
  |> List.fold_left
       (fun env (name, definition) ->
         env
         |> Env.add_inline_macro_alias ~alias:(Names.scoped_key scope name)
              definition
         |> Env.add_inline_macro_alias
              ~alias:(Names.scoped_key "cljs.core" name)
              definition)
       env

let remove_source_core_macro_alias env scope name =
  let scoped_key = Names.scoped_key scope name in
  let env =
    match Env.find_macro ~scope:"clojure.core" name env with
    | Some definition -> Env.remove_macro_alias ~alias:scoped_key definition env
    | None -> env
  in
  match Env.find_inline_macro ~scope:"clojure.core" name env with
  | Some definition ->
      Env.remove_inline_macro_alias ~alias:scoped_key definition env
  | None -> env

let remove_source_core_binding env scope name =
  let scoped_key = Names.scoped_key scope name in
  let core_key = Names.scoped_key "clojure.core" name in
  let env =
    match (Env.find_opt scoped_key env, Env.find_opt core_key env) with
    | Some scoped, Some core when scoped.ocaml_name = core.ocaml_name ->
        Env.remove scoped_key env
    | _ -> env
  in
  remove_source_core_macro_alias env scope name

let ensure_namespace env module_name =
  if
    namespace_bindings env module_name = []
    && Env.namespace_macros module_name env = []
  then
    Error.error ~code:Error_code.Unresolved ("cannot require unknown namespace " ^ module_name)
  else Ok env

let add_lg_alias_bindings env module_name alias =
  let source_bindings = namespace_bindings env module_name in
  let source_value_names =
    source_bindings
    |> List.filter_map (function
         | `Value name, _ -> Some name
         | `Record _, _ -> None)
  in
  let primitive_bindings =
    core_bindings module_name
    |> List.filter (fun (name, _) ->
           not (List.exists (String.equal name) source_value_names))
    |> List.map (fun (name, binding) -> (`Value name, binding))
  in
  let bindings = source_bindings @ primitive_bindings in
  let macros = Env.namespace_macros module_name env in
  let inline_macros = Env.namespace_inline_macros module_name env in
  if source_bindings = [] && macros = [] && inline_macros = [] then
    Error.error ~code:Error_code.Unresolved ("cannot require unknown namespace " ^ module_name)
  else
      let env =
        bindings
        |> List.map (function
             | `Value name, binding -> (alias ^ "/" ^ name, binding)
             | `Record name, binding ->
                 ("__record/" ^ alias ^ "/" ^ name, binding))
        |> fun bindings -> Env.add_bindings bindings env
      in
      macros
      |> List.fold_left
           (fun env (name, definition) ->
             Env.add_macro_alias ~alias:(alias ^ "/" ^ name) definition env)
           env
      |> fun env ->
      inline_macros
      |> List.fold_left
           (fun env (name, definition) ->
             Env.add_inline_macro_alias ~alias:(alias ^ "/" ^ name)
               definition env)
           env
      |> fun env -> Ok env

let add_lg_refer_bindings env scope module_name names =
  let source_module_name =
    if String.equal module_name "cljs.core" then "clojure.core"
    else module_name
  in
  let rec loop env = function
    | [] -> Ok env
    | name :: rest ->
        let value =
          match Env.find_opt (source_module_name ^ "/" ^ name) env with
          | Some _ as value -> value
          | None -> List.assoc_opt name (core_bindings module_name)
        in
        let record =
          Env.find_opt (Resolver.record_type_key source_module_name name) env
        in
        let macro = Env.find_macro ~scope:source_module_name name env in
        let inline_macro =
          Env.find_inline_macro ~scope:source_module_name name env
        in
        if
          Option.is_none value && Option.is_none record
          && Option.is_none macro && Option.is_none inline_macro
        then
          Error.error ~code:Error_code.Unresolved
            ("cannot refer unknown symbol " ^ module_name ^ "/" ^ name)
        else
          let alias = Names.scoped_key scope name in
          let env =
            match value with None -> env | Some binding -> Env.add alias binding env
          in
          let env =
            match record with
            | None -> env
            | Some binding ->
                Env.add (Resolver.record_type_key scope name) binding env
          in
          let env =
            match macro with
            | None -> env
            | Some definition -> Env.add_macro_alias ~alias definition env
          in
          let env =
            match inline_macro with
            | None -> env
            | Some definition ->
                Env.add_inline_macro_alias ~alias definition env
          in
          loop env rest
  in
  loop env names

let add_ocaml_alias_bindings env module_name alias =
  let module_path = ocaml_module_path module_name in
  let bindings alias =
    ( alias,
      Types.binding ~host_reference:(Ocaml_module module_path) module_path
        (TOcaml "__module") )
    :: (ocaml_host_functions module_name
       |> List.map (fun (name, binding) -> (alias ^ "/" ^ name, binding)))
  in
  let env = Env.add_bindings (bindings module_name) env in
  if alias = module_name then env else Env.add_bindings (bindings alias) env

let add_ocaml_refer_bindings env scope module_name names =
  let host_functions = ocaml_host_functions module_name in
  let module_path = ocaml_module_path module_name in
  let source_function_type (signature : Ocaml_signature.value_signature) =
    let rec source_type = function
      | TFn ([ TUnit ], return_ty) -> TFn ([], source_type return_ty)
      | TFn (parameters, return_ty) ->
          TFn (List.map source_type parameters, source_type return_ty)
      | ty -> ty
    in
    let parameters =
      List.map
        (fun (parameter : Ocaml_signature.parameter) ->
          source_type parameter.ty)
        signature.parameters
    in
    let parameters = match parameters with [ TUnit ] -> [] | _ -> parameters in
    let return_type = source_type signature.return_type in
    match signature.parameters with
    | [] -> return_type
    | _ -> TFn (parameters, return_type)
  in
  let external_value name =
    let exact = module_path ^ "." ^ name in
    let sanitized = module_path ^ "." ^ Names.ocaml_member_name name in
    let candidates = if exact = sanitized then [ exact ] else [ exact; sanitized ] in
    let rec find = function
      | [] ->
          Types.binding ~host_reference:(Ocaml_value sanitized) sanitized
            (TOcaml "__value")
      | candidate :: rest -> (
          match Ocaml_signature.value_signature candidate with
          | Ok signature ->
              Types.binding ~host_reference:(Ocaml_value candidate) candidate
                (source_function_type signature)
          | Error _ -> find rest)
    in
    find candidates
  in
  let rec loop acc = function
    | [] -> Ok acc
    | name :: rest -> (
        match List.assoc_opt name host_functions with
        | Some binding ->
            let target_key = Names.scoped_key scope name in
            loop (Env.add target_key binding acc) rest
        | None ->
            let target_key = Names.scoped_key scope name in
            loop (Env.add target_key (external_value name) acc) rest)
  in
  loop env names

let parse_entries entries =
  let package_prefix = "ocaml.package/" in
  let is_dynamic_runtime_module name =
    List.exists
      (fun module_name ->
        name = module_name
        || String.starts_with ~prefix:(module_name ^ "/") name)
      [
        "ocaml.Lg_runtime.Runtime_dynamic";
        "ocaml.Lg_runtime.Lg_dyn";
      ]
  in
  let parse_refer_names = function
    | FVector names ->
        let rec loop acc = function
          | [] -> Ok (List.rev acc)
          | FSymbol name :: rest -> loop (name :: acc) rest
          | _ -> Error.error ~code:Error_code.Arity "require :refer expects a vector of symbols"
        in
        loop [] names
    | _ -> Error.error ~code:Error_code.Arity "require :refer expects a vector of symbols"
  in
  let parse_require_entry = function
    | FSymbol module_name when is_dynamic_runtime_module module_name ->
        Error.error ~code:Error_code.Namespace
          "the universal dynamic runtime is not available to LG source; \
           define a closed sum type"
    | FSymbol module_name -> Ok [ Load { module_name } ]
    | FVector (FSymbol module_name :: _)
      when is_dynamic_runtime_module module_name ->
        Error.error ~code:Error_code.Namespace
          "the universal dynamic runtime is not available to LG source; \
           define a closed sum type"
    | FVector [ FSymbol module_name ]
      when String.starts_with ~prefix:package_prefix module_name ->
        let package =
          String.sub module_name (String.length package_prefix)
            (String.length module_name - String.length package_prefix)
        in
        if Ocaml_package.valid_name package then Ok [ Package package ]
        else Error.error ~code:Error_code.Interop ("invalid OCaml package name " ^ package)
    | FVector [ FSymbol module_name ] -> Ok [ Load { module_name } ]
    | FVector (FSymbol combined_name :: options)
      when String.starts_with ~prefix:"ocaml." combined_name
           && String.contains combined_name '/' ->
        let separator = String.index combined_name '/' in
        let package =
          String.sub combined_name 6 (separator - 6)
        in
        let module_name =
          "ocaml."
          ^ String.sub combined_name (separator + 1)
              (String.length combined_name - separator - 1)
        in
        if not (Ocaml_package.valid_name package) then
          Error.error ~code:Error_code.Interop ("invalid OCaml package name " ^ package)
        else
          let rec parse_options acc = function
            | [] ->
                if acc = [] then
                  Error.error ~code:Error_code.Macro "require entry requires :as or :refer"
                else Ok (Package package :: List.rev acc)
            | FKeyword ":as" :: FSymbol alias :: rest ->
                parse_options (Alias { module_name; alias } :: acc) rest
            | FKeyword (":refer" | ":refer-macros") :: names :: rest -> (
                match parse_refer_names names with
                | Error _ as err -> err
                | Ok names ->
                    parse_options (Refer { module_name; names } :: acc) rest)
            | _ ->
                Error.error ~code:Error_code.Namespace
                  "require entries must use :as alias or :refer [symbols]"
          in
          parse_options [] options
    | FVector (FSymbol module_name :: options) ->
        let rec parse_options acc = function
          | [] -> if acc = [] then Error.error ~code:Error_code.Macro "require entry requires :as or :refer" else Ok acc
          | FKeyword ":as" :: FSymbol alias :: rest ->
              parse_options (Alias { module_name; alias } :: acc) rest
          | FKeyword (":refer" | ":refer-macros") :: names :: rest -> (
              match parse_refer_names names with
              | Error _ as err -> err
              | Ok names -> parse_options (Refer { module_name; names } :: acc) rest)
          | _ -> Error.error ~code:Error_code.Namespace "require entries must use :as alias or :refer [symbols]"
        in
        parse_options [] options |> Result.map List.rev
    | _ -> Error.error ~code:Error_code.Namespace "require entries must start with a module symbol"
  in
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | entry :: rest -> (
        match parse_require_entry entry with
        | Error _ as err -> err
        | Ok specs -> loop (List.rev_append specs acc) rest)
  in
  loop [] entries

let package_names specs =
  specs
  |> List.filter_map (function
       | Package package -> Some package
       | Load _ | Alias _ | Refer _ -> None)
