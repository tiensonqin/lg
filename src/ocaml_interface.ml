open Ast
open Parsetree

exception Invalid of Location.t * string

let invalid location message = raise (Invalid (location, message))

let app name arguments =
  if arguments = [] then name
  else name ^ "<" ^ String.concat ";" arguments ^ ">"

let parameter_forms = function [] -> [] | parameters -> [ FVector parameters ]
let symbol name = FSymbol name
let keyword name = FKeyword (":" ^ name)
let form name arguments = FList (symbol name :: arguments)

let parse ~filename source =
  let lexbuf = Lexing.from_string source in
  Location.init lexbuf filename;
  try Ok (Parse.interface lexbuf)
  with exn ->
    let location = Location.curr lexbuf in
    Error.error ~code:Error_code.Unsupported ~location ~phase:`Parsing
      ("Invalid OCaml interface: "
      ^ Format.asprintf "%a" Location.report_exception exn)

let source_stem filename =
  [ ".mli"; ".lgi"; ".clj"; ".cljc"; ".cljs" ]
  |> List.find_map (fun suffix ->
      if Filename.check_suffix filename suffix then
        Some (Filename.chop_suffix filename suffix)
      else None)
  |> Option.value ~default:filename

let is_interface filename =
  Filename.check_suffix filename ".mli" || Filename.check_suffix filename ".lgi"

let translate ~filename ~scope ~env forms signature =
  try
    let validate_attributes attributes =
      List.iter
        (fun attribute ->
          if
            not (List.mem attribute.attr_name.txt [ "ocaml.doc"; "ocaml.text" ])
          then
            invalid attribute.attr_loc
              ("Unsupported attribute in LG OCaml interface: "
             ^ attribute.attr_name.txt))
        attributes
    in
    let iterator =
      {
        Ast_iterator.default_iterator with
        attributes = (fun _ attributes -> validate_attributes attributes);
      }
    in
    iterator.signature iterator signature;
    let definitions =
      forms
      |> List.filter_map (function
        | FList (FSymbol kind :: FSymbol name :: rest)
          when List.mem kind
                 [
                   "def";
                   "defn";
                   "defn-";
                   "defrecord";
                   "type-record";
                   "type-alias";
                   "type-variant";
                 ] ->
            Some (kind, name, rest)
        | _ -> None)
    in
    let is_type kind =
      List.mem kind [ "defrecord"; "type-record"; "type-alias"; "type-variant" ]
    in
    let resolve ~required ~types location name =
      let matches =
        List.filter
          (fun (kind, source_name, _) ->
            is_type kind = types && Names.sanitize_name source_name = name)
          definitions
      in
      match matches with
      | [ (_, source_name, _) ] -> source_name
      | [] when not required -> name
      | [] ->
          invalid location
            ("OCaml interface declaration has no LG implementation: " ^ name)
      | _ ->
          invalid location
            ("Ambiguous LG implementation for OCaml interface name: " ^ name)
    in
    let type_names =
      signature
      |> List.concat_map (fun item ->
          match item.psig_desc with
          | Psig_type (_, declarations) ->
              List.map
                (fun declaration ->
                  let name = declaration.ptype_name.txt in
                  (name, resolve ~required:false ~types:true declaration.ptype_loc name))
                declarations
          | _ -> [])
    in
    let module_name =
      "Lg_interface_" ^ Names.sanitize_name scope ^ "_"
      ^ Digest.to_hex (Digest.string (source_stem filename))
    in
    let owned_types =
      type_names
      |> List.filter_map (fun (name, source_name) ->
          if
            List.exists
              (fun (kind, candidate, _) ->
                is_type kind && candidate = source_name)
              definitions
          then None
          else Some name)
    in
    let imported_type location name =
      if String.contains name '.' then name
      else
        let candidates =
          Type_registry.bindings (Compiler_environment.types env)
          |> List.filter_map (fun (emitted, declaration) ->
              let owner = Type_id.owner declaration.Type_registry.type_id |> String.concat "." in
              if Names.sanitize_name (Type_id.name declaration.type_id) = name
                 && Module_registry.mem_module (Module_id.of_string owner)
                      (Compiler_environment.modules env)
              then Some emitted else None)
          |> List.sort_uniq String.compare
        in
        match candidates with
        | [] -> name
        | [emitted] -> emitted
        | _ -> invalid location ("Ambiguous imported type in LG OCaml interface: " ^ name)
    in
    let rec type_name ?(qualified = false) ty =
      let unsupported () =
        invalid ty.ptyp_loc "Unsupported type in LG OCaml interface"
      in
      match ty.ptyp_desc with
      | Ptyp_var name -> name
      | Ptyp_constr (path, arguments) ->
          let name = String.concat "." (Longident.flatten path.txt) in
          if
            Type_annotation.is_dynamic_runtime_type name
            || List.mem name [ "__lg_dynamic"; "dynamic" ]
          then
            invalid ty.ptyp_loc
              "Dynamic types are not allowed in LG OCaml interfaces";
          let name =
            match List.assoc_opt name type_names with
            | Some local ->
                if qualified && List.mem name owned_types then
                  module_name ^ "." ^ Names.sanitize_name local
                else local
            | None -> (
                match name with
                | "Rrbvec.t" -> "vector"
                | "Seq.t" -> "seq"
                | "Lg_runtime.Runtime_keyword.t" -> "keyword"
                | "Lg_runtime.Runtime_symbol.t" -> "symbol"
                | ("int" | "int32" | "int64" | "nativeint" | "float" | "char"
                  | "string" | "bytes" | "bool" | "unit" | "list" | "array"
                  | "ref" | "option" | "result") -> name
                | _ -> imported_type ty.ptyp_loc name)
          in
          app name (List.map (type_name ~qualified) arguments)
      | Ptyp_arrow (Nolabel, argument, result) ->
          let rec arrows arguments ty =
            match ty.ptyp_desc with
            | Ptyp_arrow (Nolabel, argument, result) ->
                arrows (type_name ~qualified argument :: arguments) result
            | Ptyp_arrow _ ->
                invalid ty.ptyp_loc
                  "Labelled function types are not supported in LG OCaml \
                   interfaces"
            | _ -> app "fn" (List.rev arguments @ [ type_name ~qualified ty ])
          in
          arrows [ type_name ~qualified argument ] result
      | Ptyp_arrow _ ->
          invalid ty.ptyp_loc
            "Labelled function types are not supported in LG OCaml interfaces"
      | Ptyp_tuple elements ->
          app "tuple"
            (List.map
               (fun (label, element) ->
                 if Option.is_some label then unsupported ();
                 type_name ~qualified element)
               elements)
      | Ptyp_variant (fields, closed, required) ->
          let tags =
            List.map
              (fun field ->
                match field.prf_desc with
                | Rtag (tag, true, []) -> tag.txt
                | Rtag (tag, false, [ payload ]) ->
                    tag.txt ^ ":" ^ type_name ~qualified payload
                | _ ->
                    invalid field.prf_loc
                      "Unsupported polymorphic variant row in LG OCaml \
                       interface")
              fields
          in
          let name =
            match (closed, required) with
            | Open, None -> "variant-open"
            | Closed, None -> "variant"
            | Closed, Some [] -> "variant-upper"
            | _ -> unsupported ()
          in
          app name tags
      | _ -> unsupported ()
    in
    let parameters ty =
      let names = ref [] in
      let iterator =
        {
          Ast_iterator.default_iterator with
          typ =
            (fun self ty ->
              (match ty.ptyp_desc with
              | Ptyp_var name when not (List.mem name !names) ->
                  names := !names @ [ name ]
              | _ -> ());
              Ast_iterator.default_iterator.typ self ty);
        }
      in
      iterator.typ iterator ty;
      parameter_forms (List.map symbol !names)
    in
    let arities rest =
      let parameters = function
        | FVector args ->
            let rec loop count = function
              | [] -> (count, false)
              | FSymbol "&" :: _ -> (count, true)
              | FSymbol hint :: tail when String.starts_with ~prefix:"^" hint ->
                  loop count tail
              | _ :: tail -> loop (count + 1) tail
            in
            Some (loop 0 args)
        | _ -> None
      in
      match List.find_map parameters rest with
      | Some arity -> [ arity ]
      | None ->
          List.filter_map
            (function FList (args :: _) -> parameters args | _ -> None)
            rest
    in
    let value_type name ty =
      let definition =
        List.find_opt
          (fun (kind, candidate, _) -> (not (is_type kind)) && candidate = name)
          definitions
      in
      let arities =
        match definition with
        | Some ("def", _, [ FList (FSymbol "fn" :: rest) ]) -> arities rest
        | Some (("defn" | "defn-"), _, rest) -> arities rest
        | _ -> []
      in
      let function_type (count, variadic) ty =
        let rec split arguments ty =
          match ty.ptyp_desc with
          | Ptyp_arrow (Nolabel, argument, result)
            when List.length arguments
                 < count + if variadic || count = 0 then 1 else 0 ->
              split (arguments @ [ argument ]) result
          | _ -> (arguments, ty)
        in
        let arguments, result = split [] ty in
        let arguments =
          match (count, variadic, arguments) with
          | ( 0,
              false,
              [
                {
                  ptyp_desc =
                    Ptyp_constr ({ txt = Longident.Lident "unit"; _ }, []);
                  _;
                };
              ] ) ->
              []
          | _ -> arguments
        in
        if List.length arguments <> count + if variadic then 1 else 0 then
          invalid ty.ptyp_loc
            ("OCaml interface function arity does not match LG definition: "
           ^ name);
        let arguments =
          List.mapi
            (fun index argument ->
              if variadic && index = count then
                match argument.ptyp_desc with
                | Ptyp_constr (path, [ element ])
                  when Longident.flatten path.txt = [ "Seq"; "t" ] ->
                    type_name ~qualified:true element
                | _ ->
                    invalid argument.ptyp_loc
                      "A variadic LG parameter must use an OCaml Seq.t type"
              else type_name ~qualified:true argument)
            arguments
        in
        app
          (if variadic then "variadic-fn" else "fn")
          (arguments @ [ type_name ~qualified:true result ])
      in
      match arities with
      | [] -> type_name ~qualified:true ty
      | [ ((_, false) as arity) ] -> function_type arity ty
      | arities ->
          let rec unpack arities ty =
            match (arities, ty.ptyp_desc) with
            | [], Ptyp_constr ({ txt = Longident.Lident "unit"; _ }, []) -> []
            | arity :: rest, Ptyp_tuple [ (None, head); (None, tail) ] ->
                function_type arity head :: unpack rest tail
            | _ ->
                invalid ty.ptyp_loc
                  "An overloaded LG function requires its OCaml nested pair \
                   signature ending in unit"
          in
          app "overload" (unpack arities ty)
    in
    let seen = Hashtbl.create 16 in
    let unique domain name location =
      let key = domain ^ name in
      if Hashtbl.mem seen key then
        invalid location ("Duplicate OCaml interface declaration: " ^ name);
      Hashtbl.add seen key ()
    in
    let located location form = (form, location) in
    let translate_type declaration =
      let location = declaration.ptype_loc in
      let name = declaration.ptype_name.txt in
      unique "type:" name location;
      if
        declaration.ptype_private = Private
        || declaration.ptype_constraints <> []
      then
        invalid location
          "Private or constrained type declarations are not supported in LG \
           OCaml interfaces";
      let source_name = List.assoc name type_names in
      let params =
        List.map
          (fun (parameter, (variance, injectivity)) ->
            if
              variance <> Asttypes.NoVariance
              || injectivity <> Asttypes.NoInjectivity
            then
              invalid parameter.ptyp_loc
                "Explicit variance and injectivity are not supported in LG \
                 OCaml interfaces";
            match parameter.ptyp_desc with
            | Ptyp_var name -> symbol name
            | _ ->
                invalid parameter.ptyp_loc
                  "LG interface type parameters must be named")
          declaration.ptype_params
      in
      let prefix = symbol source_name :: parameter_forms params in
      let existing =
        List.find_opt
          (fun (kind, candidate, _) -> is_type kind && candidate = source_name)
          definitions
      in
      match (declaration.ptype_kind, declaration.ptype_manifest) with
      | Ptype_abstract, None ->
          ignore (resolve ~required:true ~types:true location name);
          let existing_parameters =
            match existing with
            | Some
                ( ("type-alias" | "type-record" | "type-variant"),
                  _,
                  FVector parameters :: _ ) ->
                List.length parameters
            | _ -> 0
          in
          if existing_parameters <> List.length params then
            invalid location
              ("OCaml interface type parameter arity does not match LG \
                definition: " ^ name);
          []
      | Ptype_record fields, None -> (
          let fields =
            List.map
              (fun field ->
                if field.pld_mutable = Mutable then
                  invalid field.pld_loc
                    "Mutable fields are not supported in LG OCaml interface \
                     records";
                (field.pld_name.txt, type_name field.pld_type))
              fields
          in
          match existing with
          | Some ("defrecord", _, FVector source_fields :: _) ->
              let source_fields =
                List.filter_map
                  (function
                    | FSymbol hint when String.starts_with ~prefix:"^" hint ->
                        None
                    | FSymbol name -> Some name
                    | _ -> None)
                  source_fields
              in
              if
                List.map Names.sanitize_name source_fields
                <> List.map fst fields
              then
                invalid location
                  ("OCaml interface record fields do not match LG definition: "
                 ^ name);
              [
                located location
                  (form "signature"
                     (prefix
                     @ [
                         FMap
                           (List.map2
                              (fun name (_, ty) -> (keyword name, keyword ty))
                              source_fields fields);
                       ]));
              ]
          | Some _ ->
              invalid location
                ("Define the manifest type only once, in the OCaml interface: "
               ^ name)
          | None ->
              [
                located location
                  (form "type-record"
                     (prefix
                     @ List.map
                         (fun (name, ty) -> FList [ symbol name; keyword ty ])
                         fields));
              ])
      | kind, manifest ->
          if Option.is_some existing then
            invalid location
              ("Define the manifest type only once, in the OCaml interface: "
             ^ name);
          let translated =
            match (kind, manifest) with
            | Ptype_abstract, Some manifest ->
                form "type-alias" (prefix @ [ keyword (type_name manifest) ])
            | Ptype_variant constructors, None ->
                let constructors =
                  List.map
                    (fun constructor ->
                      if
                        constructor.pcd_vars <> []
                        || Option.is_some constructor.pcd_res
                      then
                        invalid constructor.pcd_loc
                          "GADT constructors are not yet supported in LG OCaml \
                           interfaces";
                      match constructor.pcd_args with
                      | Pcstr_tuple arguments ->
                          FList
                            (symbol constructor.pcd_name.txt
                            :: List.map
                                 (fun ty -> keyword (type_name ty))
                                 arguments)
                      | Pcstr_record _ ->
                          invalid constructor.pcd_loc
                            "Inline record constructors are not supported in \
                             LG OCaml interfaces")
                    constructors
                in
                form "type-variant" (prefix @ constructors)
            | _ ->
                invalid location
                  "Unsupported type declaration in LG OCaml interface"
          in
          [ located location translated ]
    in
    let translated =
      List.concat_map
        (fun item ->
          match item.psig_desc with
          | Psig_value value ->
              unique "val:" value.pval_name.txt value.pval_loc;
              if value.pval_prim <> [] then
                invalid value.pval_loc
                  "External primitives are not LG implementation contracts";
              let name =
                resolve ~required:true ~types:false value.pval_loc
                  value.pval_name.txt
              in
              [
                located value.pval_loc
                  (form "signature"
                     ((symbol name :: parameters value.pval_type)
                     @ [ keyword (value_type name value.pval_type) ]));
              ]
          | Psig_type (Recursive, declarations) ->
              List.concat_map translate_type declarations
          | Psig_type (Nonrecursive, _) ->
              invalid item.psig_loc
                "Nonrecursive type declarations are not supported in LG OCaml \
                 interfaces"
          | Psig_attribute attribute
            when attribute.attr_name.txt = "ocaml.doc"
                 || attribute.attr_name.txt = "ocaml.text" ->
              []
          | _ ->
              invalid item.psig_loc
                "Unsupported declaration in LG OCaml interface; use val and \
                 type declarations")
        signature
    in
    let namespace = form "namespace-scope" [ symbol scope ] in
    let location =
      match signature with item :: _ -> item.psig_loc | [] -> Location.none
    in
    let types, contracts =
      List.partition
        (fun (declaration, _) ->
          match declaration with
          | FList (FSymbol ("type-alias" | "type-record" | "type-variant") :: _)
            ->
              true
          | _ -> false)
        translated
    in
    let declarations =
      if types = [] then []
      else
        [
          located location
            (form "module" (symbol module_name :: List.map fst types));
        ]
    in
    let declarations = ((namespace, location) :: declarations) @ contracts in
    let locations =
      List.fold_left
        (fun entries (form, location) ->
          Source_context.fold_forms
            (fun entries form -> (form, location) :: entries)
            entries form)
        declarations translated
    in
    Ok (declarations, locations, if types = [] then None else Some module_name)
  with Invalid (location, message) -> Error.error ~code:Error_code.Interop ~location message
