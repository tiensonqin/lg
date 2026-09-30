open Ast
open Types

type param_spec = {
  pattern : form;
  source_name : string;
  ocaml_name : string;
  explicit_ty : ty option;
  destructured : bool;
  identity : (Source_node_id.t * Location.t) option;
}

type local_binding = {
  source_name : string;
  ocaml_name : string;
  ty : ty;
  semantic_expr : Semantic_ir.t;
  identity : (Source_node_id.t * Location.t) option;
}

let source_identity form =
  Source_context.find_identity form

let is_type_annotation name = String.starts_with ~prefix:"^" name
let keyword_for_local name = ":" ^ name
let ignore_name name = name = "_"

let normalize_binding_type_hints forms =
  let rec normalize normalized = function
    | FList [ FSymbol "__type-hint"; FSymbol annotation; pattern ]
      :: value :: rest ->
        normalize
          (FList [ FSymbol "__type-hint"; FSymbol annotation; value ]
          :: pattern :: normalized)
          rest
    | pattern :: FSymbol annotation :: value :: rest
      when is_type_annotation annotation ->
        normalize
          (FList [ FSymbol "__type-hint"; FSymbol annotation; value ]
          :: pattern :: normalized)
          rest
    | FSymbol annotation :: pattern :: value :: rest
      when is_type_annotation annotation ->
        normalize
          (FList [ FSymbol "__type-hint"; FSymbol annotation; value ]
          :: pattern :: normalized)
          rest
    | pattern :: value :: rest ->
        normalize (value :: pattern :: normalized) rest
    | remaining -> List.rev_append normalized remaining
  in
  normalize [] forms

let local_binding ?identity source_name ty semantic_expr =
  {
    source_name;
    ocaml_name = Names.sanitize_name source_name;
    ty;
    semantic_expr = Semantic_ir.annotate ty semantic_expr;
    identity;
  }

type map_binding = {
  binding_pattern : form;
  keyword : string;
  default_form : form option;
}

type map_pattern = {
  field_bindings : map_binding list;
  as_name : string option;
}

type sequence_pattern = {
  item_patterns : form list;
  rest_name : string option;
  sequence_as_name : string option;
}

let parse_sequence_pattern forms =
  let rec loop items rest_name as_name = function
    | [] ->
        Ok
          {
            item_patterns = List.rev items;
            rest_name;
            sequence_as_name = as_name;
          }
    | [ FKeyword ":as"; FSymbol name ] ->
        Ok
          {
            item_patterns = List.rev items;
            rest_name;
            sequence_as_name = (if ignore_name name then as_name else Some name);
          }
    | FKeyword ":as" :: _ ->
        Error.error ~code:Error_code.Destructure "sequential destructuring :as must be last"
    | FSymbol "&" :: FSymbol name :: rest ->
        if Option.is_some rest_name then
          Error.error ~code:Error_code.Destructure "sequential destructuring & can appear only once"
        else
          loop items
            (if ignore_name name then rest_name else Some name)
            as_name rest
    | FSymbol "&" :: _ ->
        Error.error ~code:Error_code.Destructure "sequential destructuring & must be followed by a symbol"
    | ((FSymbol _ | FVector _ | FMap _) as pattern) :: rest
      when Option.is_none rest_name ->
        loop (pattern :: items) rest_name as_name rest
    | _ :: _ when Option.is_some rest_name ->
        Error.error ~code:Error_code.Destructure "sequential destructuring only supports :as after & rest"
    | _ :: _ -> Error.error ~code:Error_code.Unsupported "unsupported sequential destructuring form"
  in
  loop [] None None forms

let rec pattern_names = function
  | FSymbol name -> if ignore_name name then [] else [ name ]
  | FList [ FSymbol "__type-hint"; FSymbol _; pattern ] ->
      pattern_names pattern
  | FVector forms -> sequence_pattern_names forms
  | FMap pairs -> map_pattern_names pairs
  | _ -> []

and sequence_pattern_names forms =
  match parse_sequence_pattern forms with
  | Error _ -> []
  | Ok { item_patterns; rest_name; sequence_as_name } ->
      List.concat_map pattern_names item_patterns
      @ (rest_name |> Option.to_list)
      @ (sequence_as_name |> Option.to_list)

and map_pattern_names pairs =
  let add_name acc name = if ignore_name name then acc else name :: acc in
  let add_keys acc = function
    | FVector keys ->
        List.fold_left
          (fun acc -> function FSymbol name -> add_name acc name | _ -> acc)
          acc keys
    | _ -> acc
  in
  pairs
  |> List.fold_left
       (fun acc -> function
         | FKeyword ":keys", value -> add_keys acc value
         | FKeyword ":as", FSymbol name -> add_name acc name
         | FSymbol name, FKeyword _ -> add_name acc name
         | (FList [ FSymbol "__type-hint"; FSymbol _; pattern ]), FKeyword _ ->
             List.rev_append (pattern_names pattern) acc
         | ((FVector _ | FMap _) as pattern), FKeyword _ ->
             List.rev_append (pattern_names pattern) acc
         | _ -> acc)
       []
  |> List.rev

let rec identity_for_name name = function
  | FSymbol candidate as form when candidate = name -> source_identity form
  | FList [ FSymbol "__type-hint"; FSymbol _; pattern ] ->
      identity_for_name name pattern
  | FVector forms -> List.find_map (identity_for_name name) forms
  | FMap pairs ->
      List.find_map
        (fun (key, value) ->
          match identity_for_name name key with
          | Some _ as identity -> identity
          | None -> identity_for_name name value)
        pairs
  | _ -> None

let attach_pattern_identities pattern bindings =
  List.map
    (fun binding ->
      { binding with identity = identity_for_name binding.source_name pattern })
    bindings

let parse_param_specs = function
  | FVector params ->
      let rec loop index acc = function
        | [] -> Ok (List.rev acc)
        | FSymbol annotation :: ((FVector _ | FMap _) as pattern) :: rest
          when is_type_annotation annotation -> (
            match Type_annotation.of_param_annotation annotation with
            | Error _ as error -> error
            | Ok ty ->
                let source_name = "__destructure" ^ string_of_int index in
                loop (index + 1)
                  ({
                     pattern;
                     source_name;
                     ocaml_name = Names.sanitize_name source_name;
                     explicit_ty = Some ty;
                     destructured = true;
                     identity = source_identity pattern;
                   }
                  :: acc)
                  rest)
        | FSymbol annotation :: (FSymbol name as name_form) :: rest
          when is_type_annotation annotation -> (
            match Type_annotation.of_param_annotation annotation with
            | Error _ as err -> err
            | Ok ty ->
                loop (index + 1)
                  ({
                     pattern = FSymbol name;
                     source_name = name;
                     ocaml_name = Names.sanitize_name name;
                     explicit_ty = Some ty;
                     destructured = false;
                     identity = source_identity name_form;
                   }
                  :: acc)
                  rest)
        | FList
            [
              FSymbol "__type-hint";
              FSymbol annotation;
              (FSymbol name as name_form);
            ]
          :: rest -> (
            match Type_annotation.of_param_annotation annotation with
            | Error _ as error -> error
            | Ok ty ->
                loop (index + 1)
                  ({
                     pattern = FSymbol name;
                     source_name = name;
                     ocaml_name = Names.sanitize_name name;
                     explicit_ty = Some ty;
                     destructured = false;
                     identity = source_identity name_form;
                   }
                  :: acc)
                  rest)
        | (FSymbol name as name_form) :: rest ->
            loop (index + 1)
              ({
                 pattern = FSymbol name;
                 source_name = name;
                 ocaml_name = Names.sanitize_name name;
                 explicit_ty = None;
                 destructured = false;
                 identity = source_identity name_form;
               }
              :: acc)
              rest
        | ((FVector _ | FMap _) as pattern) :: rest ->
            let source_name = "__destructure" ^ string_of_int index in
            loop (index + 1)
              ({
                 pattern;
                 source_name;
                 ocaml_name = Names.sanitize_name source_name;
                 explicit_ty = None;
                 destructured = true;
                 identity = source_identity pattern;
               }
              :: acc)
              rest
        | _ ->
            Error.error ~code:Error_code.Destructure
              "function parameters must be symbols or destructuring patterns"
      in
      loop 0 [] params
  | _ -> Error.error ~code:Error_code.Destructure "function parameters must be a vector"

let parse_map_pattern pairs =
  let default_for defaults name = List.assoc_opt name defaults in
  let parse_keys = function
    | FVector keys ->
        keys
        |> List.fold_left
             (fun acc -> function
               | FSymbol name when not (ignore_name name) ->
                   Result.map
                     (fun bindings ->
                       {
                         binding_pattern = FSymbol name;
                         keyword = keyword_for_local name;
                         default_form = None;
                       }
                       :: bindings)
                     acc
               | FSymbol _ -> acc
               | _ -> Error.error ~code:Error_code.Destructure "map destructuring :keys expects symbols")
             (Ok [])
    | _ -> Error.error ~code:Error_code.Destructure "map destructuring :keys expects a vector"
  in
  let parse_defaults = function
    | FMap pairs ->
        pairs
        |> List.fold_left
             (fun acc -> function
               | FSymbol name, value when not (ignore_name name) ->
                   Result.map (fun defaults -> (name, value) :: defaults) acc
               | FSymbol _, _ -> acc
               | _ ->
                   Error.error ~code:Error_code.Destructure "map destructuring :or defaults must use symbols")
             (Ok [])
    | _ -> Error.error ~code:Error_code.Destructure "map destructuring :or expects a map"
  in
  let apply_defaults defaults fields =
    fields
    |> List.map (fun field ->
           match field.binding_pattern with
           | FSymbol name ->
               { field with default_form = default_for defaults name }
           | _ -> field)
  in
  let rec loop fields as_name defaults = function
    | [] ->
        Ok
          {
            field_bindings = apply_defaults defaults (List.rev fields);
            as_name;
          }
    | (FKeyword ":keys", value) :: rest -> (
        match parse_keys value with
        | Error _ as err -> err
        | Ok key_fields ->
            loop (List.rev_append key_fields fields) as_name defaults rest)
    | (FKeyword ":as", FSymbol name) :: rest ->
        loop fields
          (if ignore_name name then as_name else Some name)
          defaults rest
    | (FKeyword ":or", defaults_form) :: rest -> (
        match parse_defaults defaults_form with
        | Error _ as err -> err
        | Ok parsed_defaults ->
            loop fields as_name (parsed_defaults @ defaults) rest)
    | ( ((FSymbol _ | FVector _ | FMap _
         | FList [ FSymbol "__type-hint"; FSymbol _; _ ]) as binding_pattern),
        FKeyword keyword )
      :: rest ->
        if binding_pattern = FSymbol "_" then loop fields as_name defaults rest
        else
          loop
            ({ binding_pattern; keyword; default_form = None } :: fields)
            as_name defaults rest
    | _ :: _ -> Error.error ~code:Error_code.Unsupported "unsupported map destructuring form"
  in
  loop [] None [] pairs

let field_type fields keyword =
  match find_field keyword fields with
  | Some field -> Ok field
  | None -> Error.error ~code:Error_code.Destructure ("cannot destructure missing field " ^ keyword)

let literal_default = function
  | FInt value ->
      Ok (typed_ir TInt (Semantic_ir.Int value))
  | FString value -> Ok (typed_ir TString (Semantic_ir.String value))
  | FBool value -> Ok (typed_ir TBool (Semantic_ir.Bool value))
  | FKeyword keyword -> Ok (typed_ir TKeyword (Semantic_ir.String keyword))
  | _ -> Error.error ~code:Error_code.Destructure "map destructuring :or defaults must be scalar literals"

let rec infer_map_type pattern lookup_local_ty =
  parse_map_pattern pattern
  |> Result.map (fun parsed ->
      let fields =
        parsed.field_bindings
        |> List.map (fun { binding_pattern; keyword; default_form } ->
               let ty =
                 infer_pattern_type binding_pattern lookup_local_ty
                 |> Result.value ~default:TUnknown
               in
               let ty =
                 match (parsed.as_name, ty) with
                 | Some _, (TUnknown | TMeta _ | TVar _) ->
                     Type_solver.fresh ()
                 | _ -> ty
               in
               let ty =
                 match (default_form, ty) with
                 | Some _, ty -> Types.normalize_nullable (TNullable ty)
                 | None, (TUnknown | TMeta _ | TVar _) ->
                     TNullable ty
                 | None, ty -> ty
               in
               make_map_field keyword ty)
      in
      let fields =
        match parsed.as_name with
        | None -> fields
        | Some name ->
            let source_ty =
              match lookup_local_ty name with
              | TUnknown | TMeta _ | TVar _ -> Type_solver.fresh ()
              | ty -> ty
            in
            fields
            @ [
                Types.make_record_extension_field
                  ~ty:source_ty
                  ();
              ]
      in
      TRecord fields)

and infer_sequence_type forms lookup_local_ty =
  match parse_sequence_pattern forms with
  | Error _ as err -> err
  | Ok pattern ->
      let element_ty =
        pattern.item_patterns
        |> List.fold_left
             (fun acc item_pattern ->
               let ty =
                 infer_pattern_type item_pattern lookup_local_ty
                 |> Result.value ~default:TUnknown
               in
               match acc with
               | None -> Some ty
               | Some existing when Types.equal existing ty -> Some existing
               | Some existing -> (
                   match Type_solver.unify Type_solver.empty existing ty with
                   | Ok substitutions ->
                       Some (Type_solver.apply substitutions existing)
                   | Error _ -> Some (Types.dynamic_constraint TUnknown)))
             None
        |> Option.value ~default:TUnknown
      in
      Ok (TVector element_ty)

and infer_pattern_type pattern lookup_local_ty =
  match pattern with
  | FSymbol name -> Ok (lookup_local_ty name)
  | FList [ FSymbol "__type-hint"; FSymbol annotation; _ ] ->
      Type_annotation.of_param_annotation annotation
  | FMap pairs -> infer_map_type pairs lookup_local_ty
  | FVector forms -> infer_sequence_type forms lookup_local_ty
  | _ -> Error.error ~code:Error_code.Unsupported "unsupported destructuring pattern"

let rec pattern_type_hints pattern ty =
  match (pattern, ty) with
  | FSymbol name, ty when not (ignore_name name) -> [ (name, ty) ]
  | FList [ FSymbol "__type-hint"; FSymbol _; pattern ], ty ->
      pattern_type_hints pattern ty
  | FVector forms, TTuple item_tys -> (
      match parse_sequence_pattern forms with
      | Error _ -> []
      | Ok pattern ->
          let rec pair_items acc patterns tys =
            match (patterns, tys) with
            | pattern :: patterns, ty :: tys ->
                pair_items
                  (List.rev_append (pattern_type_hints pattern ty) acc)
                  patterns tys
            | _ -> List.rev acc
          in
          let item_hints = pair_items [] pattern.item_patterns item_tys in
          (match pattern.sequence_as_name with
          | None -> item_hints
          | Some name -> (name, ty) :: item_hints))
  | FVector forms, (TVector item_ty | TList item_ty | TSeq item_ty) -> (
      match parse_sequence_pattern forms with
      | Error _ -> []
      | Ok pattern ->
          let item_hints =
            pattern.item_patterns
            |> List.concat_map (fun pattern -> pattern_type_hints pattern item_ty)
          in
          (match pattern.sequence_as_name with
          | None -> item_hints
          | Some name -> (name, ty) :: item_hints))
  | _ -> []

let infer_generator_pattern_type ?source_ty pattern lookup_local_ty =
  match pattern with
  | FVector forms -> (
      match parse_sequence_pattern forms with
      | Ok { item_patterns; rest_name = None; sequence_as_name = _ } ->
          let item_tys =
            List.map
              (fun item ->
                infer_pattern_type item lookup_local_ty
                |> Result.value ~default:TUnknown)
              item_patterns
          in
          (match item_tys with
          | [] -> Ok (TVector TUnknown)
          | first :: rest
            when (match source_ty with Some (TTuple _) -> false | _ -> true)
                 && List.for_all (fun ty -> Types.equal first ty) rest ->
              Ok (TVector first)
          | _ -> Ok (TTuple item_tys))
      | Ok _ | Error _ -> infer_pattern_type pattern lookup_local_ty)
  | _ -> infer_pattern_type pattern lookup_local_ty

let compile_default_value compile_default expected form =
  match compile_default with
  | Some compile -> compile expected form
  | None -> literal_default form

let apply_default compile_default default_form (value : typed_expr) =
  match (default_form, value.ty) with
  | Some form, (TNullable payload_ty | TOcaml_app ("option", [ payload_ty ])) ->
      Result.bind
        (compile_default_value compile_default payload_ty form)
        (fun default ->
          let result_ty =
            Types.instantiate_type ~templates:[ payload_ty ]
              ~actuals:[ default.ty ] payload_ty
          in
          if
            not
              (Types.assignable ~policy:Host_boundary ~expected:payload_ty
                 ~actual:default.ty)
          then Error.error ~code:Error_code.Destructure "map destructuring default has incompatible type"
          else
            Ok
              (typed_ir result_ty
                 (Semantic_ir.Match
                    ( value.semantic_expr,
                      [
                        ( Semantic_ir.PConstructor
                            ("Some", Some (Semantic_ir.PVar "default_value")),
                          Semantic_ir.Ident "default_value" );
                        ( Semantic_ir.PConstructor ("None", None),
                          default.semantic_expr );
                      ] ))))
  | _ -> Ok value

let rec bind_map ?compile_default ~env (target : typed_expr) pairs =
  match target.ty with
  | (TNullable map_ty | TOcaml_app ("option", [ map_ty ]))
    when Option.is_some (Types.record_fields map_ty) -> (
      let fields = Types.record_fields map_ty |> Option.get in
      match parse_map_pattern pairs with
      | Error _ as err -> err
      | Ok parsed ->
          let bind_field { binding_pattern; keyword; default_form } =
            match field_type fields keyword with
            | Error _ -> (
                match default_form with
                | None ->
                    Error.error ~code:Error_code.Destructure ("cannot destructure missing field " ^ keyword)
                | Some form -> (
                    match literal_default form with
                    | Error _ as err -> err
                    | Ok value ->
                        bind_pattern ?compile_default ~env value binding_pattern))
            | Ok field ->
                let payload_name = "__lg_nullable_destructure_map" in
                let payload =
                  typed_ir map_ty (Semantic_ir.Ident payload_name)
                in
                let projected = Structural_map.field_expr payload field in
                let ty, some_value, none_value =
                  match field.ty with
                  | ty when Types.is_dynamic ty ->
                      ( ty,
                        projected,
                        Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" )
                  | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                      ( field.ty,
                        projected,
                        Semantic_ir.Constructor ("None", None) )
                  | ty ->
                      ( TNullable ty,
                        Semantic_ir.Constructor ("Some", Some projected),
                        Semantic_ir.Constructor ("None", None) )
                in
                let value =
                  typed_ir ty
                    (Semantic_ir.Match
                       ( target.semantic_expr,
                         [
                           (Semantic_ir.PConstructor ("None", None), none_value);
                           ( Semantic_ir.PConstructor
                               ("Some", Some (Semantic_ir.PVar payload_name)),
                             some_value );
                         ] ))
                in
                Result.bind (apply_default compile_default default_form value)
                  (fun value ->
                    bind_pattern ?compile_default ~env value binding_pattern)
          in
          let rec bind_fields acc = function
            | [] ->
                let acc =
                  match parsed.as_name with
                  | None -> acc
                  | Some name ->
                      local_binding name target.ty target.semantic_expr :: acc
                in
                Ok (List.rev acc)
            | binding :: rest -> (
                match bind_field binding with
                | Error _ as err -> err
                | Ok bindings ->
                    bind_fields (List.rev_append bindings acc) rest)
          in
          bind_fields [] parsed.field_bindings)
  | TRecord fields | TNamed_record { fields; _ } -> (
      match parse_map_pattern pairs with
      | Error _ as err -> err
      | Ok parsed ->
          let bind_field { binding_pattern; keyword; default_form } =
            match field_type fields keyword with
            | Error _ -> (
                match default_form with
                | None ->
                    Error.error ~code:Error_code.Destructure ("cannot destructure missing field " ^ keyword)
                | Some form -> (
                    match literal_default form with
                    | Error _ as err -> err
                    | Ok value ->
                        bind_pattern ?compile_default ~env value binding_pattern))
            | Ok field ->
                let value =
                  typed_ir field.ty (Structural_map.field_expr target field)
                in
                Result.bind (apply_default compile_default default_form value)
                  (fun value ->
                    bind_pattern ?compile_default ~env value binding_pattern)
          in
          let rec bind_fields acc = function
            | [] ->
                let acc =
                  match parsed.as_name with
                  | None -> acc
                  | Some name ->
                      (match Types.find_record_extension_field fields with
                      | Some field
                        when Types.is_static_record_source_field field ->
                          local_binding name field.ty
                            (Structural_map.field_expr target field)
                          :: acc
                      | Some _ | None ->
                          local_binding name target.ty target.semantic_expr
                          :: acc)
                in
                Ok (List.rev acc)
            | binding :: rest -> (
                match bind_field binding with
                | Error _ as err -> err
                | Ok bindings -> bind_fields (List.rev_append bindings acc) rest
                )
          in
          bind_fields [] parsed.field_bindings)
  | ty when Types.is_dynamic ty -> (
      match parse_map_pattern pairs with
      | Error _ as error -> error
      | Ok parsed ->
          let rec bind_fields acc = function
            | [] ->
                let acc =
                  match parsed.as_name with
                  | None -> acc
                  | Some name ->
                      local_binding name target.ty target.semantic_expr :: acc
                in
                Ok (List.rev acc)
            | { binding_pattern; keyword; _ } :: rest -> (
                let value =
                  typed_ir
                    (Types.dynamic_constraint TUnknown)
                    (Semantic_ir.Apply
                       ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.get",
                         [
                           target.semantic_expr;
                           Semantic_ir.Apply
                             ( Semantic_ir.Ident
                                 "Lg_runtime.Runtime_dynamic.keyword",
                               [ Semantic_ir.String keyword ] );
                         ] ))
                in
                match
                  bind_pattern ?compile_default ~env value binding_pattern
                with
                | Error _ as error -> error
                | Ok bindings -> bind_fields (List.rev_append bindings acc) rest
                )
          in
          bind_fields [] parsed.field_bindings)
  | _ -> Error.error ~code:Error_code.Destructure "map destructuring expects a map"

and bind_sequence ?compile_default env (target : typed_expr) forms =
  let rec erased_sequence_storage ty =
    if Types.is_dynamic ty then true
    else
      match Types.seqable_constraint_info ty with
      | Some (_, _, (TUnknown | TMeta _ | TVar _)) -> true
      | Some (_, _, value_ty) -> Types.is_dynamic value_ty
      | None -> (
          match Types.protocol_constraint_info ty with
          | Some (_, _, value_ty) -> erased_sequence_storage value_ty
          | None -> false)
  in
  let rec materialize_erased_element = function
    | TUnknown | TMeta _ | TVar _ -> Types.dynamic_constraint TUnknown
    | TList inner -> TList (materialize_erased_element inner)
    | TVector inner -> TVector (materialize_erased_element inner)
    | ty -> ty
  in
  let item_at inner index =
    let nil_value_adapter =
      Compiler_environment.find_nil_value_adapter inner env
    in
    let semantic_expr =
      match (target.ty, Types.is_dynamic inner, nil_value_adapter) with
      | TList _, true, _ ->
          Semantic_ir.Match
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "List.nth_opt",
                  [ target.semantic_expr; Semantic_ir.Int index ] ),
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar "__lg_destructure_item")),
                  Semantic_ir.Ident "__lg_destructure_item" );
              ] )
      | TVector _, true, _ ->
          Semantic_ir.Match
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "Rrbvec.nth_opt",
                  [ target.semantic_expr; Semantic_ir.Int index ] ),
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar "__lg_destructure_item")),
                  Semantic_ir.Ident "__lg_destructure_item" );
              ] )
      | TList _, false, Some adapter ->
          Semantic_ir.Match
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "List.nth_opt",
                  [ target.semantic_expr; Semantic_ir.Int index ] ),
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Apply (Semantic_ir.Ident adapter, []) );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar "__lg_destructure_item")),
                  Semantic_ir.Ident "__lg_destructure_item" );
              ] )
      | TVector _, false, Some adapter ->
          Semantic_ir.Match
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "Rrbvec.nth_opt",
                  [ target.semantic_expr; Semantic_ir.Int index ] ),
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Apply (Semantic_ir.Ident adapter, []) );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar "__lg_destructure_item")),
                  Semantic_ir.Ident "__lg_destructure_item" );
              ] )
      | TList _, false, None ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "List.nth",
              [ target.semantic_expr; Semantic_ir.Int index ] )
      | TVector _, false, None ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Rrbvec.nth",
              [ target.semantic_expr; Semantic_ir.Int index ] )
      | _, _, _ -> target.semantic_expr
    in
    typed_ir inner semantic_expr
  in
  let rec bind_items item_at index acc = function
    | [] -> Ok (List.rev acc)
    | pattern :: rest -> (
        match bind_pattern ?compile_default ~env (item_at index) pattern with
        | Error _ as error -> error
        | Ok bindings ->
            bind_items item_at (index + 1) (List.rev_append bindings acc) rest)
  in
  let bind_rest count name =
    let optional_sequence ty semantic_expr =
      local_binding name (TNullable ty)
        (Semantic_ir.Match
           ( semantic_expr,
             [
               ( Semantic_ir.PList [],
                 Semantic_ir.Constructor ("None", None) );
               ( Semantic_ir.PVar "__lg_destructure_rest",
                 Semantic_ir.Constructor
                   ( "Some",
                     Some (Semantic_ir.Ident "__lg_destructure_rest") ) );
             ] ))
    in
    match target.ty with
    | TList inner ->
        optional_sequence (TList inner)
          (Core_sequence_transform.drop_list_expr
             (Semantic_ir.Int count)
             target.semantic_expr)
    | TVector inner ->
        optional_sequence (TList inner)
          (Core_sequence_transform.drop_list_expr
             (Semantic_ir.Int count)
             (Semantic_ir.Apply
                ( Semantic_ir.Ident "Rrbvec.to_list",
                  [ target.semantic_expr ] )))
    | _ ->
        local_binding name target.ty target.semantic_expr
  in
  let bind_seq_rest count name inner sequence =
    local_binding name (TNullable (TSeq inner))
      (Semantic_ir.Apply
         ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.non_empty",
           [
             Semantic_ir.Apply
               ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.drop",
                 [ Semantic_ir.Int count; sequence ] );
           ] ))
  in
  let bind_tuple element_tys nullable =
    match parse_sequence_pattern forms with
    | Error _ as err -> err
    | Ok pattern ->
        if Option.is_some pattern.rest_name then
          Error.error ~code:Error_code.Destructure "tuple destructuring does not support & rest"
        else if List.length pattern.item_patterns > List.length element_tys then
          Error.error ~code:Error_code.Destructure "tuple destructuring has too many elements"
        else
          let tuple_item_at index =
            let element_ty = List.nth element_tys index in
            let value_name = "__lg_tuple_item_" ^ string_of_int index in
            let patterns =
              List.mapi
                (fun element_index _ ->
                  if element_index = index then Semantic_ir.PVar value_name
                  else Semantic_ir.PAny)
                element_tys
            in
            if nullable then
              let ty, some_value, none_value =
                match element_ty with
                | ty when Types.is_dynamic ty ->
                    ( ty,
                      Semantic_ir.Ident value_name,
                      Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" )
                | TNullable _ | TOcaml_app ("option", [ _ ]) ->
                    ( element_ty,
                      Semantic_ir.Ident value_name,
                      Semantic_ir.Constructor ("None", None) )
                | ty ->
                    ( TNullable ty,
                      Semantic_ir.Constructor
                        ("Some", Some (Semantic_ir.Ident value_name)),
                      Semantic_ir.Constructor ("None", None) )
              in
              typed_ir ty
                (Semantic_ir.Match
                   ( target.semantic_expr,
                     [
                       (Semantic_ir.PConstructor ("None", None), none_value);
                       ( Semantic_ir.PConstructor
                           ("Some", Some (Semantic_ir.PTuple patterns)),
                         some_value );
                     ] ))
            else
              typed_ir element_ty
                (Semantic_ir.Match
                   ( target.semantic_expr,
                     [
                       ( Semantic_ir.PTuple patterns,
                         Semantic_ir.Ident value_name );
                     ] ))
          in
          Result.map
            (fun bindings ->
              match pattern.sequence_as_name with
              | None -> bindings
              | Some name ->
                  bindings
                  @ [ local_binding name target.ty target.semantic_expr ])
            (bind_items tuple_item_at 0 [] pattern.item_patterns)
  in
  match target.ty with
  | TTuple element_tys -> bind_tuple element_tys false
  | TNullable (TTuple element_tys)
  | TOcaml_app ("option", [ TTuple element_tys ]) ->
      bind_tuple element_tys true
  | TList inner | TVector inner -> (
      match parse_sequence_pattern forms with
      | Error _ as err -> err
      | Ok pattern ->
          let item_count = List.length pattern.item_patterns in
          Result.map
            (fun bindings ->
              let bindings =
                match pattern.rest_name with
                | None -> bindings
                | Some name -> bindings @ [ bind_rest item_count name ]
              in
              match pattern.sequence_as_name with
              | None -> bindings
              | Some name ->
                  bindings
                  @ [ local_binding name target.ty target.semantic_expr ])
            (bind_items (item_at inner) 0 [] pattern.item_patterns))
  | _ -> (
      match
        ( parse_sequence_pattern forms,
          Collection_capability.to_seq_expr env target )
      with
      | (Error _ as err), _ -> err
      | _, Error _ ->
          Error.error ~code:Error_code.Destructure
            ("sequential destructuring expects a seqable value, got "
           ^ Types.source_name target.ty)
      | Ok pattern, Ok (inner, sequence) ->
          let inner =
            if erased_sequence_storage target.ty then
              materialize_erased_element inner
            else inner
          in
          let item_count = List.length pattern.item_patterns in
          let sequence_item_at index =
            let item =
              Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.nth_opt",
                  [ Semantic_ir.Int index; sequence ] )
            in
            let expression =
              if Types.is_dynamic inner then
                let item_name = "__lg_destructure_item" in
                Semantic_ir.Match
                  ( item,
                    [
                      ( Semantic_ir.PConstructor ("None", None),
                        Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.nil" );
                      ( Semantic_ir.PConstructor
                          ("Some", Some (Semantic_ir.PVar item_name)),
                        Semantic_ir.Ident item_name );
                    ] )
              else
                match
                  Compiler_environment.find_nil_value_adapter inner env
                with
                | Some adapter ->
                    let item_name = "__lg_destructure_item" in
                    Semantic_ir.Match
                      ( item,
                        [
                          ( Semantic_ir.PConstructor ("None", None),
                            Semantic_ir.Apply
                              (Semantic_ir.Ident adapter, []) );
                          ( Semantic_ir.PConstructor
                              ("Some", Some (Semantic_ir.PVar item_name)),
                            Semantic_ir.Ident item_name );
                        ] )
                | None ->
                    Semantic_ir.Apply
                      (Semantic_ir.Ident "Option.get", [ item ])
            in
            typed_ir inner expression
          in
          Result.map
            (fun bindings ->
              let bindings =
                match pattern.rest_name with
                | None -> bindings
                | Some name ->
                    bindings
                    @ [ bind_seq_rest item_count name inner sequence ]
              in
              match pattern.sequence_as_name with
              | None -> bindings
              | Some name ->
                  bindings
                  @ [ local_binding name target.ty target.semantic_expr ])
            (bind_items sequence_item_at 0 [] pattern.item_patterns))

and bind_pattern ?compile_default ~env (target : typed_expr) pattern =
  let bindings =
    match pattern with
  | FSymbol name ->
      if ignore_name name then Ok []
      else Ok [ local_binding name target.ty target.semantic_expr ]
  | FList [ FSymbol "__type-hint"; FSymbol _; pattern ] ->
      bind_pattern ?compile_default ~env target pattern
  | FMap pairs -> bind_map ?compile_default ~env target pairs
  | FVector forms -> bind_sequence ?compile_default env target forms
  | _ -> Error.error ~code:Error_code.Unsupported "unsupported destructuring pattern"
  in
  Result.map (attach_pattern_identities pattern) bindings
