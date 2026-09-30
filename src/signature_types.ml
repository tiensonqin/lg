open Types
open Lowered

let resolve aliases ty =
  let rec resolve visiting ty =
    let ty = Semantic_type.map_children (resolve visiting) ty in
    let named =
      match ty with
      | TOcaml name -> Some (name, [])
      | TOcaml_app (name, arguments) -> Some (name, arguments)
      | _ -> None
    in
    match named with
    | Some (name, arguments) when not (List.mem name visiting) -> (
        match List.assoc_opt name aliases with
        | Some (parameters, replacement)
          when List.length parameters = List.length arguments ->
            let substitutions =
              List.map2
                (fun name ty -> (Type_solver.Declared name, ty))
                parameters arguments
              |> Type_solver.of_list
            in
            resolve (name :: visiting)
              (Type_solver.apply substitutions replacement)
        | _ -> ty)
    | _ -> ty
  in
  resolve [] ty

let substitute aliases items =
  List.map
    (function
      | Signature_value value ->
          Signature_value
            { value with value_type = resolve aliases value.value_type }
      | Signature_type declaration ->
          Signature_type
            {
              declaration with
              manifest = Option.map (resolve aliases) declaration.manifest;
            }
      | item -> item)
    items

let resolve_manifests items =
  let aliases =
    List.filter_map
      (function
        | Signature_type { type_name; type_parameters; manifest = Some ty; _ }
          ->
            Some (type_name, (type_parameters, ty))
        | _ -> None)
      items
  in
  substitute aliases items

let apply
    ?(resolve_module =
      fun name -> Error.error ~code:Error_code.Unresolved ("unknown module signature " ^ name)) constraints
    items =
  let rec apply items = function
    | [] -> Ok (resolve_manifests items)
    | constraint_ :: rest when String.contains constraint_.constrained_name '.'
      -> (
        let index = String.index constraint_.constrained_name '.' in
        let module_name = String.sub constraint_.constrained_name 0 index in
        let nested_name =
          String.sub constraint_.constrained_name (index + 1)
            (String.length constraint_.constrained_name - index - 1)
        in
        let nested =
          List.find_map
            (function
              | Signature_module declaration
                when declaration.module_name = module_name ->
                  Some
                    ( declaration.source_name,
                      declaration.location,
                      resolve_module declaration.module_signature )
              | Signature_inline_module declaration
                when declaration.module_name = module_name ->
                  Some
                    ( declaration.source_name,
                      declaration.location,
                      Ok declaration.items )
              | _ -> None)
            items
        in
        match nested with
        | None ->
            Error.error ~code:Error_code.Unresolved ("unknown constrained signature module " ^ module_name)
        | Some (source_name, location, nested) ->
            Result.bind nested (fun nested ->
                Result.bind
                  (apply nested
                     [ { constraint_ with constrained_name = nested_name } ])
                  (fun nested ->
                    let items =
                      List.map
                        (function
                          | Signature_module declaration
                            when declaration.module_name = module_name ->
                              Signature_inline_module
                                {
                                  source_name;
                                  module_name;
                                  location;
                                  items = nested;
                                }
                          | Signature_inline_module declaration
                            when declaration.module_name = module_name ->
                              Signature_inline_module
                                {
                                  source_name;
                                  module_name;
                                  location;
                                  items = nested;
                                }
                          | item -> item)
                        items
                    in
                    let items =
                      substitute
                        [
                          ( constraint_.constrained_name,
                            ( constraint_.constrained_parameters,
                              constraint_.replacement ) );
                        ]
                        items
                    in
                    apply items rest)))
    | constraint_ :: rest -> (
        let name = constraint_.constrained_name in
        let declaration =
          List.find_map
            (function
              | Signature_type declaration when declaration.type_name = name ->
                  Some declaration.type_parameters
              | _ -> None)
            items
        in
        match declaration with
        | None -> Error.error ~code:Error_code.Unresolved ("unknown constrained signature type " ^ name)
        | Some parameters
          when List.length parameters
               <> List.length constraint_.constrained_parameters ->
            Error.error ~code:Error_code.Type_mismatch
              ("signature type constraint parameter arity mismatch for " ^ name)
        | Some _ ->
            let items =
              List.filter_map
                (function
                  | Signature_type declaration when declaration.type_name = name
                    ->
                      if constraint_.destructive then None
                      else
                        Some
                          (Signature_type
                             {
                               declaration with
                               type_parameters =
                                 constraint_.constrained_parameters;
                               manifest = Some constraint_.replacement;
                             })
                  | item -> Some item)
                items
            in
            let items =
              substitute
                [
                  ( name,
                    (constraint_.constrained_parameters, constraint_.replacement)
                  );
                ]
                items
            in
            apply items rest)
  in
  apply items constraints
