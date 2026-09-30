open Ast
open Lowered

module Env = Compiler_environment

let qualified_name scope name =
  let host_qualified =
    match String.split_on_char '.' name with
    | first :: _ :: _ when first <> "" ->
        Char.uppercase_ascii first.[0] = first.[0]
    | _ -> false
  in
  if String.contains name '/' || host_qualified then name
  else Names.scoped_key scope name

let compile ?(type_parameters = []) scope env next_type name fields_form =
  let rec parse fields = function
    | [] -> Ok (List.rev fields)
    | (FKeyword keyword, FKeyword type_keyword) :: rest -> (
        match
          Type_annotation.of_keyword_with_parameters type_parameters
            type_keyword
        with
        | Error _ as error -> error
        | Ok ty ->
            let field =
              Types.make_field keyword
                (Function_elaborator.infer_named_record scope env ty)
            in
            if
              List.exists
                (fun (existing : Types.field) ->
                  existing.keyword = field.keyword)
                fields
            then Error.error ~code:Error_code.Duplicate ("duplicate sidecar signature field " ^ keyword)
            else parse (field :: fields) rest)
    | _ ->
        Error.error ~code:Error_code.Semantic
          "sidecar record signature fields must map keywords to type keywords"
  in
  match fields_form with
  | FMap entries ->
      Result.bind (parse [] entries) (fun fields ->
          let name = qualified_name scope name in
          Result.map
            (fun signatures ->
              ( scope,
                Env.with_signatures signatures env,
                next_type,
                Comment ("signature " ^ name) ))
            (Signature_overlay.add name (Signature_overlay.Record fields)
               (Env.signatures env)))
  | FKeyword keyword -> (
      match
        Type_annotation.of_keyword_with_parameters type_parameters keyword
      with
      | Error _ as error -> error
      | Ok ty ->
          let ty = Function_elaborator.infer_named_record scope env ty in
          let name = qualified_name scope name in
          let type_dependencies =
            Dependency_graph.type_annotation_symbols (FKeyword keyword)
            |> List.filter (fun dependency ->
                   not (List.mem dependency type_parameters))
          in
          Result.map
            (fun signatures ->
              ( scope,
                Env.with_signatures signatures env,
                next_type,
                Comment ("signature " ^ name) ))
            (Signature_overlay.add name
               (Signature_overlay.Value { ty; type_dependencies })
               (Env.signatures env)))
  | _ -> Error.error ~code:Error_code.Arity "signature expects a type keyword or record field map"
