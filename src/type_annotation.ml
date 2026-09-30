open Ast
open Types

let reject_dynamic_type () =
  Error.error ~code:Error_code.Semantic
    "dynamic is not a source type; define a closed sum type containing the \
     supported values"

let is_dynamic_runtime_type = function
  | "Lg_runtime.Runtime_dynamic.t"
  | "Lg_runtime.Lg_dyn.t"
  | "Runtime_dynamic.t"
  | "Lg_dyn.t" ->
      true
  | _ -> false

let split_top_level_type_args source =
  let rec loop depth start index acc =
    if index >= String.length source then
      let part = String.sub source start (index - start) |> String.trim in
      List.rev (part :: acc)
    else
      match source.[index] with
      | '<' -> loop (depth + 1) start (index + 1) acc
      | '>' when depth > 0 -> loop (depth - 1) start (index + 1) acc
      | (',' | ';') when depth = 0 ->
          let part = String.sub source start (index - start) |> String.trim in
          loop depth (index + 1) (index + 1) (part :: acc)
      | _ -> loop depth start (index + 1) acc
  in
  loop 0 0 0 []

let matching_type_application source =
  match String.index_opt source '<' with
  | None -> None
  | Some open_index ->
      if not (String.ends_with ~suffix:">" source) then None
      else
        let rec loop depth index =
          if index >= String.length source then depth = 0
          else
            match source.[index] with
            | '<' -> loop (depth + 1) (index + 1)
            | '>' ->
                let depth = depth - 1 in
                depth >= 0
                && (if depth = 0 then index = String.length source - 1
                    else loop depth (index + 1))
            | _ -> loop depth (index + 1)
        in
        if loop 0 open_index then Some open_index else None

let validate_ocaml_type_application name args =
  match (name, args) with
  | "tuple", _ :: _ :: _ -> Ok ()
  | "tuple", _ -> Error.error ~code:Error_code.Arity "tuple expects at least two type arguments"
  | "option", [ _ ] -> Ok ()
  | "option", _ -> Error.error ~code:Error_code.Arity "option expects one type argument"
  | "weak", [ _ ] -> Ok ()
  | "weak", _ -> Error.error ~code:Error_code.Arity "weak expects one type argument"
  | "result", [ _; _ ] -> Ok ()
  | "result", _ -> Error.error ~code:Error_code.Arity "result expects two type arguments"
  | "map", [ _; _ ] -> Ok ()
  | "map", _ -> Error.error ~code:Error_code.Arity "map expects two type arguments"
  | "fn", _ :: _ -> Ok ()
  | "fn", [] -> Error.error ~code:Error_code.Arity "fn expects a return type"
  | "variadic-fn", _ :: _ :: _ -> Ok ()
  | "variadic-fn", _ ->
      Error.error ~code:Error_code.Arity "variadic-fn expects a rest type and return type"
  | "overload", _ :: _ -> Ok ()
  | "overload", _ -> Error.error ~code:Error_code.Protocol "overload expects at least two function types"
  | "reify", [ _; _ ] -> Ok ()
  | "reify", _ -> Error.error ~code:Error_code.Protocol "reify expects a protocol and method type"
  | _, [] -> Error.error ~code:Error_code.Interop "OCaml type application expects at least one argument"
  | _ -> Ok ()

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

let transparent_ocaml_alias = function
  | TOcaml name as ty
    when String.contains name '.' && not (String.starts_with ~prefix:"__" name)
    -> (
      match Ocaml_signature.type_manifest name with
      | Ok manifest
        when (not (Types.equal manifest ty))
             && not (exposes_internal_compilation_unit manifest) ->
          manifest
      | Ok _ | Error _ -> ty)
  | ty -> ty

let rec parse_ocaml_type source =
  let source = String.trim source in
  if source = "" then Error.error ~code:Error_code.Interop "empty OCaml type"
  else
    match matching_type_application source with
    | None ->
        if String.contains source '<' || String.contains source '>' then
          Error.error ~code:Error_code.Interop "malformed OCaml type application"
        else if source = "ordering" then Ok (TOcaml "int")
        else if source = "int" then Ok TInt
        else if source = "int64" then Ok (TOcaml "int64")
        else if source = "float" then Ok TFloat
        else if source = "char" then Ok TChar
        else if source = "string" then Ok TString
        else if source = "regex" then Ok TRegex
        else if source = "bytes" then Ok TString
        else if source = "bool" then Ok TBool
        else if source = "unit" then Ok TUnit
        else if source = "nil" then Ok TNil
        else if source = "symbol" then Ok TSymbol
        else if source = "keyword" then Ok TKeyword
        else if source = "dynamic" || is_dynamic_runtime_type source then
          reject_dynamic_type ()
        else
          (match String.rindex_opt source '/' with
          | Some separator when separator > 0 ->
              let module_path = String.sub source 0 separator in
              if Char.uppercase_ascii module_path.[0] = module_path.[0] then
                let type_name =
                  String.sub source (separator + 1)
                    (String.length source - separator - 1)
                  |> Names.sanitize_name
                in
                Ok (transparent_ocaml_alias (TOcaml (module_path ^ "." ^ type_name)))
              else Ok (Types.named_record_marker source)
          | _ ->
              if String.contains source '.' then
                Ok (transparent_ocaml_alias (TOcaml source))
              else if
                String.length source > 0
                && Char.uppercase_ascii source.[0] = source.[0]
              then Ok (Types.named_record_marker source)
              else
                Ok
                  (transparent_ocaml_alias
                     (TOcaml (Names.sanitize_name source))))
    | Some open_index ->
        let name = String.sub source 0 open_index |> String.trim in
        let inner =
          String.sub source (open_index + 1)
            (String.length source - open_index - 2)
        in
        if name = "" then Error.error ~code:Error_code.Interop "missing OCaml type constructor"
        else if List.mem name ["variant"; "variant-open"; "variant-upper"] then
          let bound = match name with "variant" -> Exact_row | "variant-open" -> Lower_row | _ -> Upper_row in
          let rec parse_tags tags = function
            | [] -> Ok (TPoly_variant {tags = List.sort compare tags; bound})
            | source :: rest ->
                let tag, payload = match String.index_opt source ':' with
                  | None -> (source, Ok None)
                  | Some index ->
                      (String.sub source 0 index,
                       Result.map Option.some (parse_ocaml_type (String.sub source (index + 1) (String.length source - index - 1)))) in
                if not (Variant_row.valid_tag tag) then
                  Error.error ~code:Error_code.Invalid_form "invalid polymorphic variant tag"
                else if List.mem_assoc tag tags then Error.error ~code:Error_code.Duplicate "duplicate polymorphic variant tag"
                else Result.bind payload (fun payload -> parse_tags ((tag, payload) :: tags) rest) in
          parse_tags [] (split_top_level_type_args inner)
        else
          let arg_sources = split_top_level_type_args inner in
          if List.exists (( = ) "") arg_sources then
            Error.error ~code:Error_code.Interop "empty OCaml type argument"
          else
            let rec parse_args acc = function
              | [] -> Ok (List.rev acc)
              | arg :: rest -> (
                  match parse_ocaml_type arg with
                  | Error _ as err -> err
                  | Ok ty -> parse_args (ty :: acc) rest)
            in
            match parse_args [] arg_sources with
            | Error _ as err -> err
            | Ok args -> (
                match validate_ocaml_type_application name args with
                | Error _ as err -> err
                | Ok () ->
                    if name = "module" then
                      match arg_sources with
                      | [ signature ] -> Ok (Types.module_package_type (Names.module_path_to_ocaml signature))
                      | _ -> Error.error ~code:Error_code.Interop "module expects one module signature"
                    else if name = "option" then
                      match args with
                      | [ inner ] -> Ok (TNullable inner)
                      | _ -> assert false
                    else if name = "tuple" then Ok (TTuple args)
                    else if name = "callback" then
                      match args with
                      | [ inner ] -> Ok (TOcaml_app ("Lg_ffi.Callback.t", [inner]))
                      | _ -> Error.error ~code:Error_code.Interop "callback expects one function type argument"
                    else if name = "owned-pointer" then
                      match args with
                      | [ inner ] -> Ok (TOcaml_app ("Lg_ffi.Owned_pointer.t", [inner]))
                      | _ -> Error.error ~code:Error_code.Arity "owned-pointer expects one type argument"
                    else if name = "pointer" then
                      match args with
                      | [ inner ] -> Ok (TOcaml_app ("Ctypes.ptr", [inner]))
                      | _ -> Error.error ~code:Error_code.Arity "pointer expects one type argument"
                    else if name = "array" then
                      match args with
                      | [ inner ] -> Ok (TArray inner)
                      | _ -> Error.error ~code:Error_code.Arity "array expects one type argument"
                    else if name = "vector" then
                      match args with
                      | [ inner ] -> Ok (TVector inner)
                      | _ -> Error.error ~code:Error_code.Arity "vector expects one type argument"
                    else if name = "list" then
                      match args with
                      | [ inner ] -> Ok (TList inner)
                      | _ -> Error.error ~code:Error_code.Arity "list expects one type argument"
                    else if name = "set" then
                      match args with
                      | [ inner ] -> Ok (TSet inner)
                      | _ -> Error.error ~code:Error_code.Arity "set expects one type argument"
                    else if name = "seq" then
                      match args with
                      | [ inner ] -> Ok (TSeq inner)
                      | _ -> Error.error ~code:Error_code.Arity "seq expects one type argument"
                    else if
                      name = Types.maybe_reduced_callback_type_name
                    then
                      match args with
                      | [ inner ] -> Ok (Types.reduced inner)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "reducing-function result expects one type argument"
                    else if name = "reducing-callback-result" then
                      match args with
                      | [ inner ] ->
                          Ok (Types.maybe_reduced_callback_result inner)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "reducing-callback-result expects one type argument"
                    else if name = "seqable" then
                      match args with
                      | [ inner ] -> Ok (Types.seqable_constraint inner)
                      | [ inner; storage ] ->
                          Ok
                            (Types.seqable_constraint_with_value inner storage)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "seqable expects one or two type arguments"
                    else if name = "sorted" then
                      match args with
                      | [ entry; key; storage ] ->
                          Ok (Types.sorted_constraint entry key storage)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "sorted expects entry, key, and storage type arguments"
                    else if name = "map-entry" then
                      match args with
                      | [ key; value; storage ] ->
                          Ok (Types.map_entry_constraint key value storage)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "map-entry expects key, value, and storage type arguments"
                    else if name = "optional-seqable" then
                      match args with
                      | [ inner ] ->
                          Ok
                            (Types.optional_seqable_constraint inner TUnknown)
                      | [ inner; storage ] ->
                          Ok
                            (Types.optional_seqable_constraint inner storage)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "optional-seqable expects one or two type arguments"
                    else if name = "truthy" then
                      match args with
                      | [ inner ] -> Ok (Types.truthy_constraint inner)
                      | _ -> Error.error ~code:Error_code.Arity "truthy expects one type argument"
                    else if name = "printable" then
                      match args with
                      | [ inner ] -> Ok (Types.printable_constraint inner)
                      | _ -> Error.error ~code:Error_code.Arity "printable expects one type argument"
                    else if name = "hashable" then
                      match args with
                      | [ inner ] -> Ok (Types.hashable_constraint inner)
                      | _ -> Error.error ~code:Error_code.Arity "hashable expects one type argument"
                    else if name = "comparable" then
                      match args with
                      | [ inner ] -> Ok (Types.comparable_constraint inner)
                      | _ -> Error.error ~code:Error_code.Arity "comparable expects one type argument"
                    else if name = "array-index" then
                      match args with
                      | [ inner ] -> Ok (Types.array_index_constraint inner)
                      | _ -> Error.error ~code:Error_code.Arity "array-index expects one type argument"
                    else if name = "map" then
                      match args with
                      | [ key; value ] -> Ok (Types.dynamic_map key value)
                      | _ -> Error.error ~code:Error_code.Arity "map expects two type arguments"
                    else if name = "ref" then
                      match args with
                      | [ inner ] -> Ok (TRef inner)
                      | _ -> Error.error ~code:Error_code.Arity "ref expects one type argument"
                    else if name = "weak" then
                      match args with
                      | [ inner ] -> Ok (Types.weak_type inner)
                      | _ -> Error.error ~code:Error_code.Arity "weak expects one type argument"
                    else if name = "fn" then
                      match List.rev args with
                      | return_ty :: reversed_params ->
                          Ok (TFn (List.rev reversed_params, return_ty))
                      | [] -> assert false
                    else if name = "variadic-fn" then
                      match List.rev args with
                      | return_ty :: rest_param :: reversed_fixed_params ->
                          Ok
                            (TOverloaded_fn
                               [
                                 {
                                   fixed_params = List.rev reversed_fixed_params;
                                   rest_param = Some rest_param;
                                   return_ty;
                                 };
                               ])
                      | _ -> assert false
                    else if name = "overload" then
                      let rec arities acc = function
                        | [] -> Ok (TOverloaded_fn (List.rev acc))
                        | TFn (fixed_params, return_ty) :: rest ->
                            arities
                              ({ fixed_params; rest_param = None; return_ty }
                              :: acc)
                              rest
                        | TOverloaded_fn nested :: rest ->
                            arities (List.rev_append nested acc) rest
                        | _ :: _ ->
                            Error.error ~code:Error_code.Protocol
                              "overload arguments must all be function types"
                      in
                      arities [] args
                    else if name = "reify" then
                      match (arg_sources, args) with
                      | [ protocol_name; _ ], [ _; methods_ty ] ->
                          let protocol_name = String.trim protocol_name in
                          if
                            protocol_name = ""
                            || String.contains protocol_name '<'
                            || String.contains protocol_name '>'
                          then
                            Error.error ~code:Error_code.Protocol
                              "reify protocol must be a qualified protocol name"
                          else
                            let protocol_id =
                              Protocol_id.of_string protocol_name
                            in
                            Ok
                              (TOcaml_app
                                 ( "Lg_runtime.Runtime_reify.t",
                                   [
                                     Types.reify_protocol_payload protocol_id
                                       methods_ty TUnit;
                                   ] ))
                      | _ -> assert false
                    else if name = Types.next_seq_type_name then
                      match args with
                      | [ inner ] -> Ok (Types.next_seq inner)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "next-seq expects one type argument"
                    else if name = Types.reversible_next_seq_type_name then
                      match args with
                      | [ inner ] -> Ok (Types.reversible_next_seq inner)
                      | _ ->
                          Error.error ~code:Error_code.Arity
                            "reversible-next-seq expects one type argument"
                    else if String.contains name '/' then
                      Ok (Types.named_record_app_marker name args)
                    else
                      Ok
                        (TOcaml_app
                           ( (if String.contains name '.' then name
                              else Names.sanitize_name name),
                             args )))

let of_keyword = function
  | ":int" -> Ok TInt
  | ":ordering" -> Ok (TOcaml "int")
  | ":ordering-fn" ->
      Ok (TFn ([ TUnknown; TUnknown ], TOcaml "int"))
  | ":float" -> Ok TFloat
  | ":char" -> Ok TChar
  | ":string" -> Ok TString
  | ":symbol" -> Ok TSymbol
  | ":keyword" -> Ok TKeyword
  | ":bool" -> Ok TBool
  | ":unit" -> Ok TUnit
  | ":buffer" -> Ok (TOcaml "Buffer.t")
  | ":list" -> Ok (TList TUnknown)
  | ":vector" -> Ok (TVector TUnknown)
  | ":seq" -> Ok (TSeq TUnknown)
  | ":array" -> Ok (TArray TUnknown)
  | ":set" -> Ok (TSet TUnknown)
  | ":map" -> Ok (Types.dynamic_map TUnknown TUnknown)
  | ":dynamic" -> reject_dynamic_type ()
  | ":transient-vector" ->
      Error.error ~code:Error_code.Semantic
        "transient-vector requires concrete element types; untyped transient \
         collections are not supported"
  | ":transient-map" ->
      Error.error ~code:Error_code.Semantic
        "transient-map requires concrete key and value types; untyped transient \
         collections are not supported"
  | ":nil" -> Error.error ~code:Error_code.Interop "nil is not a valid type annotation"
  | keyword when String.starts_with ~prefix:":ocaml/" keyword ->
      Error.error ~code:Error_code.Unsupported "the :ocaml/ type prefix is not supported"
  | keyword when String.starts_with ~prefix:":param/" keyword ->
      Error.error ~code:Error_code.Unsupported "the :param/ type prefix is not supported"
  | keyword when String.starts_with ~prefix:":" keyword ->
      String.sub keyword 1 (String.length keyword - 1) |> parse_ocaml_type
  | keyword -> Error.error ~code:Error_code.Unresolved ("unknown vector element type " ^ keyword)

let rec resolve_type_parameters parameters = function
  | TPoly_variant row ->
      let rec resolve acc = function
        | [] -> Ok (TPoly_variant {row with tags = List.rev acc})
        | (tag, None) :: rest -> resolve ((tag, None) :: acc) rest
        | (tag, Some ty) :: rest -> Result.bind (resolve_type_parameters parameters ty)
            (fun ty -> resolve ((tag, Some ty) :: acc) rest) in
      resolve [] row.tags
  | TOcaml name when List.mem name parameters ->
      Ok (TVar (Names.sanitize_name name))
  | TOcaml name
    when parameters <> [] && String.length name = 1
         && Char.lowercase_ascii name.[0] = name.[0] ->
      Error.error ~code:Error_code.Unresolved ("unknown type parameter " ^ name)
  | TOcaml_app (name, args) ->
      let rec resolve_args acc = function
        | [] -> Ok (TOcaml_app (name, List.rev acc))
        | arg :: rest -> (
            match resolve_type_parameters parameters arg with
            | Error _ as err -> err
            | Ok arg -> resolve_args (arg :: acc) rest)
      in
      resolve_args [] args
  | TCompiler marker ->
      let rec resolve_children acc = function
        | [] -> Ok (List.rev acc)
        | value :: rest -> (
            match resolve_type_parameters parameters value with
            | Error _ as err -> err
            | Ok value -> resolve_children (value :: acc) rest)
      in
      Result.map
        (fun children ->
          TCompiler
            (Semantic_type.replace_compiler_marker_children marker children))
        (resolve_children [] (Semantic_type.compiler_marker_children marker))
  | TConstraint constraint_ ->
      let resolve value = resolve_type_parameters parameters value in
      let resolve_one build value =
        Result.map (fun value -> TConstraint (build value)) (resolve value)
      in
      let resolve_two build left right =
        Result.bind (resolve left) (fun left ->
            Result.map
              (fun right -> TConstraint (build left right))
              (resolve right))
      in
      (match constraint_ with
      | Seqable_constraint ({ element; storage; _ } as seqable) ->
          resolve_two
            (fun element storage ->
              Seqable_constraint { seqable with element; storage })
            element storage
      | Contains_constraint { key; storage } ->
          resolve_two
            (fun key storage -> Contains_constraint { key; storage })
            key storage
      | Truthy_constraint value ->
          resolve_one (fun value -> Truthy_constraint value) value
      | Nil_predicate_constraint value ->
          resolve_one (fun value -> Nil_predicate_constraint value) value
      | Printable_constraint value ->
          resolve_one (fun value -> Printable_constraint value) value
      | Exception_data_constraint value ->
          resolve_one (fun value -> Exception_data_constraint value) value
      | Hashable_constraint value ->
          resolve_one (fun value -> Hashable_constraint value) value
      | Comparable_constraint value ->
          resolve_one (fun value -> Comparable_constraint value) value
      | Array_index_constraint value ->
          resolve_one (fun value -> Array_index_constraint value) value
      | Symbol_predicate_constraint value ->
          resolve_one (fun value -> Symbol_predicate_constraint value) value
      | Open_boundary_constraint value ->
          resolve_one (fun value -> Open_boundary_constraint value) value
      | Protocol_constraint ({ witness; value; _ } as protocol) ->
          resolve_two
            (fun witness value ->
              Protocol_constraint { protocol with witness; value })
            witness value)
  | TArray inner ->
      resolve_type_parameters parameters inner |> Result.map (fun inner -> TArray inner)
  | TRef inner ->
      resolve_type_parameters parameters inner |> Result.map (fun inner -> TRef inner)
  | TNullable inner ->
      resolve_type_parameters parameters inner
      |> Result.map (fun inner -> TNullable inner)
  | TList inner ->
      resolve_type_parameters parameters inner
      |> Result.map (fun inner -> TList inner)
  | TVector inner ->
      resolve_type_parameters parameters inner
      |> Result.map (fun inner -> TVector inner)
  | TSet inner ->
      resolve_type_parameters parameters inner
      |> Result.map (fun inner -> TSet inner)
  | TSeq inner ->
      resolve_type_parameters parameters inner
      |> Result.map (fun inner -> TSeq inner)
  | TTuple args ->
      let rec resolve_args acc = function
        | [] -> Ok (TTuple (List.rev acc))
        | arg :: rest -> (
            match resolve_type_parameters parameters arg with
            | Error _ as err -> err
            | Ok arg -> resolve_args (arg :: acc) rest)
      in
      resolve_args [] args
  | TFn (params, return_ty) ->
      let rec resolve_params acc = function
        | [] -> (
            match resolve_type_parameters parameters return_ty with
            | Error _ as err -> err
            | Ok return_ty -> Ok (TFn (List.rev acc, return_ty)))
        | param :: rest -> (
            match resolve_type_parameters parameters param with
            | Error _ as err -> err
            | Ok param -> resolve_params (param :: acc) rest)
      in
      resolve_params [] params
  | TOverloaded_fn arities ->
      let resolve_arity (arity : fn_arity) =
        let rec resolve_params acc = function
          | [] -> Ok (List.rev acc)
          | param :: rest -> (
              match resolve_type_parameters parameters param with
              | Error _ as err -> err
              | Ok param -> resolve_params (param :: acc) rest)
        in
        Result.bind (resolve_params [] arity.fixed_params) (fun fixed_params ->
            Result.bind
              (match arity.rest_param with
              | None -> Ok None
              | Some rest_param ->
                  Result.map Option.some
                    (resolve_type_parameters parameters rest_param))
              (fun rest_param ->
                Result.map
                  (fun return_ty -> { fixed_params; rest_param; return_ty })
                  (resolve_type_parameters parameters arity.return_ty)))
      in
      let rec resolve_arities acc = function
        | [] -> Ok (TOverloaded_fn (List.rev acc))
        | arity :: rest -> (
            match resolve_arity arity with
            | Error _ as err -> err
            | Ok arity -> resolve_arities (arity :: acc) rest)
      in
      resolve_arities [] arities
  | ty -> Ok ty

let of_keyword_with_parameters parameters keyword =
  match of_keyword keyword with
  | Error _ as err -> err
  | Ok ty -> resolve_type_parameters parameters ty

let of_param_annotation annotation =
  if annotation = "^:dynamic" then reject_dynamic_type ()
  else if String.starts_with ~prefix:"^:" annotation then
    match of_keyword (String.sub annotation 1 (String.length annotation - 1)) with
    | Ok ty -> Ok ty
    | (Error _ as err)
      when annotation = "^:transient-vector"
           || annotation = "^:transient-map"
           || (String.length annotation > 2
              && is_dynamic_runtime_type
                   (String.sub annotation 2 (String.length annotation - 2)))
           || String.starts_with ~prefix:"^:ocaml/" annotation
           || String.starts_with ~prefix:"^:param/" annotation ->
        err
    | Error _
      when String.starts_with ~prefix:"^:option<" annotation
           || String.starts_with ~prefix:"^:result<" annotation
           || String.starts_with ~prefix:"^:tuple<" annotation
           || String.contains annotation '<' ->
        Error.error ~code:Error_code.Invalid_form ("invalid type annotation " ^ annotation)
    | Error _ -> Error.error ~code:Error_code.Unresolved ("unknown parameter type " ^ annotation)
  else if String.starts_with ~prefix:"^" annotation && String.length annotation > 1
  then
    let type_name =
      String.sub annotation 1 (String.length annotation - 1)
    in
    (match type_name with
    | "int" | "long" | "number" -> Ok TInt
    | "string" -> Ok TString
    | "Object" | "java.lang.Object" | "Number" | "java.lang.Number"
    | "Comparable" | "java.lang.Comparable" | "Boolean" | "String" ->
        Error.error ~code:Error_code.Unsupported
          "Java interop is not supported; use static LG types and functions"
    | type_name
      when String.starts_with ~prefix:"java." type_name
           || String.starts_with ~prefix:"javax." type_name
           || String.starts_with ~prefix:"clojure.lang." type_name ->
        Error.error ~code:Error_code.Unsupported
          "Java interop is not supported; use static LG types and functions"
    | "boolean" -> Ok TBool
    | "double" | "float" -> Ok TFloat
    | "bytes" -> Ok TString
    | "seq" -> Ok (Types.optional_seqable_constraint TUnknown TUnknown)
    | type_name when String.contains type_name '<' ->
        parse_ocaml_type type_name
    | _ -> (
        match Host_interop.type_annotation type_name with
        | Some host_type -> Ok (TOcaml host_type)
        | None when String.contains type_name '.' -> Ok (TOcaml type_name)
        | None -> Ok (Types.named_record_marker type_name)))
  else Error.error ~code:Error_code.Semantic "function parameters must be symbols"

let parse_params = function
  | FVector params ->
      let rec loop acc = function
        | [] -> Ok (List.rev acc)
        | FSymbol annotation :: FSymbol name :: rest
          when String.starts_with ~prefix:"^" annotation -> (
            match of_param_annotation annotation with
            | Error _ as err -> err
            | Ok ty -> loop ((name, ty) :: acc) rest)
        | FSymbol name :: rest -> loop ((name, TUnknown) :: acc) rest
        | _ -> Error.error ~code:Error_code.Semantic "function parameters must be symbols"
      in
      loop [] params
  | _ -> Error.error ~code:Error_code.Semantic "function parameters must be a vector"
