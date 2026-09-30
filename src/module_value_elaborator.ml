open Ast
open Types
module Env = Compiler_environment

let pack module_name signature =
  let signature = Names.module_path_to_ocaml signature in
  Ok
    (typed_ir
       (Types.module_package_type signature)
       (Semantic_ir.PackModule
          (Names.module_path_to_ocaml module_name, signature)))

let unpack ~compile_expr ~compile_body scope env binding body_forms =
  match (binding, body_forms) with
  | FVector [ FSymbol name; value ], _ :: _ ->
      Result.bind (compile_expr scope env value) (fun package ->
          match Types.module_package_signature package.ty with
          | None -> Error.error ~code:Error_code.Arity "let-module requires a module package"
          | Some signature ->
              Result.bind
                (Module_metadata.signature_parameter_bindings ~scope env name
                   signature) (fun bindings ->
                  let prefix = name ^ "/" and nested = name ^ "." in
                  let env =
                    Env.to_bindings env
                    |> List.fold_left
                         (fun env (key, _) ->
                           if
                             String.starts_with ~prefix key
                             || String.starts_with ~prefix:nested key
                           then Env.remove key env
                           else env)
                         env
                  in
                  let env = Env.add_bindings bindings env in
                  Result.map
                    (fun body ->
                      {
                        body with
                        semantic_expr =
                          Semantic_ir.UnpackModule
                            ( Names.module_segment_to_ocaml name,
                              signature,
                              package.semantic_expr,
                              body.semantic_expr );
                      })
                    (compile_body scope env "let-module requires a body"
                       body_forms)))
  | _, [] -> Error.error ~code:Error_code.Arity "let-module requires a body"
  | _ -> Error.error ~code:Error_code.Arity "let-module expects [module-name package] and a body"
