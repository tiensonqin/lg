open Ast
open Lowered
module Env = Compiler_environment

let compile ?location scope env next_type signature_name item_forms =
  let rec parse_constraints acc = function
    | [] -> Ok (List.rev acc)
    | FList
        [
          FSymbol (("with-type" | "substitute-type") as kind);
          FSymbol name;
          FKeyword keyword;
        ]
      :: rest ->
        parse_constraints acc
          (FList [ FSymbol kind; FSymbol name; FVector []; FKeyword keyword ]
          :: rest)
    | FList
        [
          FSymbol (("with-type" | "substitute-type") as kind);
          (FSymbol name as name_form);
          (FVector _ as parameters);
          FKeyword keyword;
        ]
      :: rest ->
        let parameters =
          match parameters with
          | FVector [] -> Ok []
          | parameters -> Type_parameters.parse parameters
        in
        Result.bind parameters (fun parameters ->
            Result.bind
              (Type_annotation.of_keyword_with_parameters parameters keyword)
              (fun replacement ->
                let constraint_ =
                  {
                    constrained_name = Names.type_path_to_ocaml name;
                    constrained_parameters = parameters;
                    replacement;
                    destructive = kind = "substitute-type";
                    constraint_location = Source_context.find name_form;
                  }
                in
                parse_constraints (constraint_ :: acc) rest))
    | _ ->
        Error.error ~code:Error_code.Semantic
          "signature constraint expects with-type or substitute-type, a type \
           name, optional parameters, and a type"
  in
  let rec parse items = function
    | [] -> Ok (List.rev items)
    | FList
        [ FSymbol "val"; (FSymbol value_name as name_form); FKeyword keyword ]
      :: rest -> (
        match Type_annotation.of_keyword keyword with
        | Error _ -> Error.error ~code:Error_code.Unresolved ("unknown signature type " ^ keyword)
        | Ok value_type ->
            parse
              (Signature_value
                 {
                   source_name = value_name;
                   value_name = Names.sanitize_name value_name;
                   value_type;
                   location = Source_context.find name_form;
                 }
              :: items)
              rest)
    | FList
        [ FSymbol "type"; (FSymbol type_name as name_form); FKeyword keyword ]
      :: rest -> (
        match Type_annotation.of_keyword keyword with
        | Error _ -> Error.error ~code:Error_code.Unresolved ("unknown signature type " ^ keyword)
        | Ok manifest ->
            parse
              (Signature_type
                 {
                   type_name = Names.sanitize_name type_name;
                   type_parameters = [];
                   manifest = Some manifest;
                   location = Source_context.find name_form;
                 }
              :: items)
              rest)
    | FList [ FSymbol "type"; (FSymbol type_name as name_form) ] :: rest ->
        parse
          (Signature_type
             {
               type_name = Names.sanitize_name type_name;
               type_parameters = [];
               manifest = None;
               location = Source_context.find name_form;
             }
          :: items)
          rest
    | FList
        [
          FSymbol "module";
          (FSymbol module_name as name_form);
          (FSymbol module_signature as signature_form);
        ]
      :: rest ->
        parse
          (Signature_module
             {
               source_name = module_name;
               module_name = Names.module_segment_to_ocaml module_name;
               module_signature = Names.module_path_to_ocaml module_signature;
               location = Source_context.find name_form;
               signature_location = Source_context.find signature_form;
             }
          :: items)
          rest
    | FList
        (FSymbol "include"
        :: (FSymbol module_signature as signature_form)
        :: constraints)
      :: rest ->
        Result.bind (parse_constraints [] constraints) (fun type_constraints ->
            parse
              (Signature_include
                 {
                   module_signature =
                     Names.module_path_to_ocaml module_signature;
                   signature_location = Source_context.find signature_form;
                   type_constraints;
                 }
              :: items)
              rest)
    | FList (FSymbol "include" :: _) :: _ ->
        Error.error ~code:Error_code.Unresolved "module-signature include expects one module type"
    | FList
        [
          FSymbol "type";
          (FSymbol type_name as name_form);
          (FVector _ as parameter_form);
          FKeyword keyword;
        ]
      :: rest -> (
        match Type_parameters.parse parameter_form with
        | Error _ as err -> err
        | Ok type_parameters -> (
            match
              Type_annotation.of_keyword_with_parameters type_parameters keyword
            with
            | Error (err : Error.t)
              when String.starts_with ~prefix:"unknown type parameter "
                     err.message ->
                Error err
            | Error _ -> Error.error ~code:Error_code.Unresolved ("unknown signature type " ^ keyword)
            | Ok manifest ->
                parse
                  (Signature_type
                     {
                       type_name = Names.sanitize_name type_name;
                       type_parameters;
                       manifest = Some manifest;
                       location = Source_context.find name_form;
                     }
                  :: items)
                  rest))
    | FList
        [
          FSymbol "type";
          (FSymbol type_name as name_form);
          (FVector _ as parameter_form);
        ]
      :: rest -> (
        match Type_parameters.parse parameter_form with
        | Error _ as err -> err
        | Ok type_parameters ->
            parse
              (Signature_type
                 {
                   type_name = Names.sanitize_name type_name;
                   type_parameters;
                   manifest = None;
                   location = Source_context.find name_form;
                 }
              :: items)
              rest)
    | _ ->
        Error.error ~code:Error_code.Semantic
          "module-signature items must be val, type, module, or include \
           declarations"
  in
  match parse [] item_forms with
  | Error _ as err -> err
  | Ok [] -> Error.error ~code:Error_code.Arity "module-signature expects at least one signature item"
  | Ok items -> (
      let signature_id =
        Signature_id.create
          ~owner:(if scope = "" then [] else [ scope ])
          ~name:signature_name
      in
      let signature_name = Names.module_segment_to_ocaml signature_name in
      match
        Module_registry.declare_signature signature_id items (Env.modules env)
      with
      | Error _ as err -> err
      | Ok modules ->
          Result.bind (Module_registry.expanded_signature signature_id modules)
            (fun _ ->
              let env = Env.with_modules modules env in
              Ok
                ( scope,
                  env,
                  next_type,
                  Module_signature { signature_name; location; items } )))
