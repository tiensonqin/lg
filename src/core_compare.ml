open Types
open Expression_support

let nullable_equality_counter = ref 0

let fresh_nullable_equality_name () =
  incr nullable_equality_counter;
  "__lg_nullable_equality_value_"
  ^ string_of_int !nullable_equality_counter

let static_sequence_equal left right =
  Semantic_ir.Apply
    ( Semantic_ir.Ident "Seq.equal",
      [ Semantic_ir.Ident "="; left; right ] )

let requires_runtime_equality = function
  | TUnknown | TMeta _ | TVar _ | TOcaml "value" -> true
  | _ -> false

let sequential_type = function
  | TList _ | TVector _ | TArray _ | TSeq _ -> true
  | ty -> Option.is_some (Types.next_seq_element ty)

let source_equality_class = function
  | TInt | TFloat -> Some `Number
  | TBool -> Some `Bool
  | TChar -> Some `Char
  | TString -> Some `String
  | TRegex -> Some `Regex
  | TSymbol -> Some `Symbol
  | TKeyword -> Some `Keyword
  | TUnit -> Some `Unit
  | TNil -> Some `Nil
  | TList _ | TVector _ | TArray _ | TSeq _ -> Some `Sequential
  | TSet _ -> Some `Set
  | TRecord _ | TNamed_record _ -> Some `Record
  | TFn _ | TOverloaded_fn _ -> Some `Function
  | ty when Option.is_some (Types.next_seq_element ty) -> Some `Sequential
  | ty when Option.is_some (Types.dynamic_map_types ty) -> Some `Map
  | TUnknown | TMeta _ | TVar _ | TNullable _ | TOcaml _ | TOcaml_app _
  | TPoly_variant _ | TTuple _ | TRef _ | TMap_keys | TConstraint _ ->
      None

let disjoint_static_equality left_ty right_ty =
  (not (Types.same_shape left_ty right_ty))
  &&
  match (source_equality_class left_ty, source_equality_class right_ty) with
  | Some `Number, Some `Number -> false
  | Some `Sequential, Some `Sequential -> false
  | Some `Record, Some `Map | Some `Map, Some `Record -> false
  | Some left, Some right -> left <> right
  | _ -> false

let nullable_equality_compatible left_ty right_ty =
  match (left_ty, right_ty) with
  | TNil, (TNullable _ | TOcaml_app ("option", [ _ ]))
  | (TNullable _ | TOcaml_app ("option", [ _ ])), TNil ->
      true
  | TNil, ty when Option.is_some (Types.next_seq_element ty) -> true
  | ty, TNil when Option.is_some (Types.next_seq_element ty) -> true
  | (TNullable inner | TOcaml_app ("option", [ inner ])), actual
  | actual, (TNullable inner | TOcaml_app ("option", [ inner ])) ->
      Types.assignable ~policy:Host_boundary ~expected:inner ~actual
  | _ -> false

let structural_record_fields_for_equality = function
  | TRecord fields -> Some fields
  | TNamed_record { fields; nominal = false; _ } -> Some fields
  | _ -> None

let matching_record_fields left_fields right_fields =
  if List.length left_fields <> List.length right_fields then None
  else
    let rec loop pairs = function
      | [] -> Some (List.rev pairs)
      | (left_field : field) :: rest -> (
          match
            List.find_opt
              (fun (right_field : field) ->
                right_field.keyword = left_field.keyword)
              right_fields
          with
          | Some right_field -> loop ((left_field, right_field) :: pairs) rest
          | None -> None)
    in
    loop [] left_fields

let rec equality_type_compatible left_ty right_ty =
  (* Capability-constrained values are stored as (witness, value) pairs;
     equality applies to the value component. *)
  let left_ty = Types.constraint_value_type left_ty in
  let right_ty = Types.constraint_value_type right_ty in
  let directly_compatible =
    Types.is_dynamic left_ty
    || Types.is_dynamic right_ty
    || Types.same_shape left_ty right_ty
    || (Types.is_numeric left_ty && Types.is_numeric right_ty)
    || disjoint_static_equality left_ty right_ty
    || nullable_equality_compatible left_ty right_ty
    || Types.assignable ~policy:Host_boundary ~expected:left_ty ~actual:right_ty
    || Types.defer_to_ocaml ~expected:left_ty ~actual:right_ty
    || (sequential_type left_ty && sequential_type right_ty)
  in
  if directly_compatible then true
  else
    match
      ( structural_record_fields_for_equality left_ty,
        structural_record_fields_for_equality right_ty )
    with
    | Some left_fields, Some right_fields -> (
        match matching_record_fields left_fields right_fields with
        | Some pairs ->
            List.for_all
              (fun ((left_field : field), (right_field : field)) ->
                equality_type_compatible left_field.ty right_field.ty)
              pairs
        | None -> false)
    | _ -> false

let rec equality_expr ?env left right =
  let resolve value =
    match env with
    | None -> value
    | Some env ->
        {
          value with
          ty =
            Collection_capability.resolve_callback_record env value.ty;
        }
  in
  let left = resolve left in
  let right = resolve right in
  (* Capability constraints store (witness, value) pairs: compare the
     stored values. *)
  let unwrap_capability value =
    match Types.capability_constraint_value value.ty with
    | Some value_ty ->
        {
          value with
          ty = value_ty;
          semantic_expr =
            Semantic_ir.Apply
              (Semantic_ir.Ident "snd", [ value.semantic_expr ]);
        }
    | None -> value
  in
  let left = unwrap_capability left in
  let right = unwrap_capability right in
  match (left.ty, right.ty) with
  | TFloat, TInt ->
      let right =
        match Semantic_ir.unlocated right.semantic_expr with
        | Semantic_ir.Int value ->
            Semantic_ir.Float (string_of_int value ^ ".0")
        | _ ->
            Semantic_ir.Apply
              (Semantic_ir.Ident "float_of_int", [ right.semantic_expr ])
      in
      Semantic_ir.Infix
        ("=", left.semantic_expr, right)
  | TInt, TFloat -> equality_expr ?env right left
  | TOcaml "int", TInt ->
      Semantic_ir.Infix ("=", left.semantic_expr, right.semantic_expr)
  | TInt, TOcaml "int" -> equality_expr ?env right left
  | (TNullable left_inner | TOcaml_app ("option", [ left_inner ])),
    (TNullable right_inner | TOcaml_app ("option", [ right_inner ]))
    when Types.same_shape left_inner right_inner ->
      let left_value = fresh_nullable_equality_name () in
      let right_value = fresh_nullable_equality_name () in
      Semantic_ir.Match
        ( left.semantic_expr,
          [
            ( Semantic_ir.PConstructor ("None", None),
              Semantic_ir.Match
                ( right.semantic_expr,
                  [
                    ( Semantic_ir.PConstructor ("None", None),
                      Semantic_ir.Bool true );
                    ( Semantic_ir.PConstructor
                        ("Some", Some Semantic_ir.PAny),
                      Semantic_ir.Bool false );
                  ] ) );
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar left_value)),
              Semantic_ir.Match
                ( right.semantic_expr,
                  [
                    ( Semantic_ir.PConstructor ("None", None),
                      Semantic_ir.Bool false );
                    ( Semantic_ir.PConstructor
                        ("Some", Some (Semantic_ir.PVar right_value)),
                      equality_expr ?env
                        (typed_ir left_inner
                           (Semantic_ir.Ident left_value))
                        (typed_ir right_inner
                           (Semantic_ir.Ident right_value)) );
                  ] ) );
          ] )
  | (TNullable _ | TOcaml_app ("option", [ _ ])), TNil ->
      Semantic_ir.Match
        ( left.semantic_expr,
          [ (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool true);
            ( Semantic_ir.PConstructor ("Some", Some Semantic_ir.PAny),
              Semantic_ir.Bool false );
          ] )
  | TNil, (TNullable _ | TOcaml_app ("option", [ _ ])) ->
      equality_expr ?env right left
  | TNil, ty when Option.is_some (Types.next_seq_element ty) ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
          [ right.semantic_expr ] )
  | ty, TNil when Option.is_some (Types.next_seq_element ty) ->
      equality_expr ?env right left
  | (TNullable inner | TOcaml_app ("option", [ inner ])), right_ty
    when Types.assignable ~policy:Host_boundary ~expected:inner
           ~actual:right_ty ->
      let nullable_value = fresh_nullable_equality_name () in
      Semantic_ir.Match
        ( left.semantic_expr,
          [ (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool false);
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar nullable_value)),
      equality_expr ?env
                (typed_ir inner (Semantic_ir.Ident nullable_value))
                right );
          ] )
  | left_ty, (TNullable inner | TOcaml_app ("option", [ inner ]))
    when Types.assignable ~policy:Host_boundary ~expected:inner
           ~actual:left_ty ->
      equality_expr ?env right left
  | TNil, TNil -> Semantic_ir.Infix ("=", left.semantic_expr, right.semantic_expr)
  | TNil, _ | _, TNil ->
      Semantic_ir.Sequence
        [ left.semantic_expr; right.semantic_expr; Semantic_ir.Bool false ]
  | left_ty, right_ty when disjoint_static_equality left_ty right_ty ->
      Semantic_ir.Sequence
        [ left.semantic_expr; right.semantic_expr; Semantic_ir.Bool false ]
  | left_ty, right_ty
    when Option.is_some (Types.dynamic_map_types left_ty)
         && Option.is_some (Types.dynamic_map_types right_ty) -> (
      match
        (Types.dynamic_map_types left_ty, Types.dynamic_map_types right_ty)
      with
      | Some (left_key, left_value), Some (right_key, right_value) ->
          if
            Types.same_shape left_key right_key
            && Types.same_shape left_value right_value
          then
            let operation =
              if Option.is_some (Types.dynamic_map_types left_key) then
                "Lg_runtime.Runtime_map.equiv_map_key"
              else "Lg_runtime.Runtime_map.equiv"
            in
            Semantic_ir.Apply
              ( Semantic_ir.Ident operation,
                [ left.semantic_expr; right.semantic_expr ] )
          else
            Semantic_ir.Sequence
              [ left.semantic_expr; right.semantic_expr; Semantic_ir.Bool false ]
      | _ -> assert false)
  | _ -> (match (left.ty, right.ty) with
  | left_ty, right_ty
    when Types.is_dynamic left_ty && Types.is_dynamic right_ty ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.equal",
          [ left.semantic_expr; right.semantic_expr ] )
  | left_ty, _ when Types.is_dynamic left_ty -> (
      match pack_plain_dynamic_value right with
      | Some right ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.equal",
              [ left.semantic_expr; right ] )
      | None -> Semantic_ir.Bool false)
  | _, right_ty when Types.is_dynamic right_ty ->
      equality_expr ?env right left
  | left_ty, right_ty
    when sequential_type left_ty && sequential_type right_ty -> (
      match
        ( Core_sequence_transform.collection_to_seq_expr left,
          Core_sequence_transform.collection_to_seq_expr right )
      with
      | Ok (_, left_sequence), Ok (_, right_sequence) ->
          let equal = static_sequence_equal left_sequence right_sequence in
          let left_is_next = Option.is_some (Types.next_seq_element left_ty) in
          let right_is_next = Option.is_some (Types.next_seq_element right_ty) in
          if left_is_next = right_is_next then equal
          else
            let next_sequence =
              if left_is_next then left_sequence else right_sequence
            in
            Semantic_ir.Infix
              ( "&&",
                Semantic_ir.Prefix
                  ( "not",
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
                        [ next_sequence ] ) ),
                equal )
      | Error _, _ | _, Error _ -> Semantic_ir.Bool false)
  | (TFn _ | TOverloaded_fn _), (TFn _ | TOverloaded_fn _) ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Lg_runtime.Runtime_static_value.equal",
          [ left.semantic_expr; right.semantic_expr ] )
  | TRef _, TRef _ ->
      Semantic_ir.Infix ("==", left.semantic_expr, right.semantic_expr)
  | left_ty, right_ty
    when requires_runtime_equality left_ty
         && requires_runtime_equality right_ty ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Lg_runtime.Runtime_static_value.equal",
          [ left.semantic_expr; right.semantic_expr ] )
  | (TRecord _ | TNamed_record _), right_type
    when Option.is_some (Types.dynamic_map_types right_type) -> (
      match left.record_values with
      | None -> Semantic_ir.Bool false
      | Some values ->
          let dynamic_left =
            List.fold_left
              (fun map ((field : field), value) ->
                Semantic_ir.Apply
                  ( Semantic_ir.Ident "Lg_runtime.Runtime_map.assoc",
                    [ map; Semantic_ir.String field.keyword; value ] ))
              (Semantic_ir.Ident "Lg_runtime.Runtime_map.empty") values
          in
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_map.equiv",
              [ dynamic_left; right.semantic_expr ] ))
  | left_type, (TRecord _ | TNamed_record _)
    when Option.is_some (Types.dynamic_map_types left_type) ->
      equality_expr ?env right left
  | TSet left_inner, TSet right_inner -> (
      match Types.set_module_name left_inner with
      | Ok left_module -> (
          match Types.set_module_name right_inner with
          | Ok right_module when left_module = right_module ->
              Semantic_ir.Apply
                ( Semantic_ir.Ident (left_module ^ ".equal"),
                  [ left.semantic_expr; right.semantic_expr ] )
          | Ok _ when Types.equal right_inner TUnknown ->
              Semantic_ir.Apply
                ( Semantic_ir.Ident (left_module ^ ".equal"),
                  [ left.semantic_expr;
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident (left_module ^ ".of_list"),
                        [ right.semantic_expr ] ) ] )
          | Ok right_module when Types.equal left_inner TUnknown ->
              Semantic_ir.Apply
                ( Semantic_ir.Ident (right_module ^ ".equal"),
                  [ Semantic_ir.Apply
                      ( Semantic_ir.Ident (right_module ^ ".of_list"),
                        [ left.semantic_expr ] );
                    right.semantic_expr ] )
          | _ ->
              Semantic_ir.Infix
                ("=", left.semantic_expr, right.semantic_expr))
      | Error _ ->
          Semantic_ir.Infix ("=", left.semantic_expr, right.semantic_expr))
  | TSet inner, _ -> (
      match Types.set_module_name inner with
      | Ok set_module ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident (set_module ^ ".equal"),
              [ left.semantic_expr; right.semantic_expr ] )
      | Error _ -> Semantic_ir.Bool false)
  | (TRecord left_fields | TNamed_record { fields = left_fields; _ }),
    (TRecord right_fields | TNamed_record { fields = right_fields; _ }) -> (
      match matching_record_fields left_fields right_fields with
      | Some pairs ->
          let parts =
            pairs
            |> List.map
                 (fun ((left_field : field), (right_field : field)) ->
                   let left_field_value =
                     typed_ir left_field.ty
                       (Structural_map.field_expr left left_field)
                   in
                   let right_field_value =
                     typed_ir right_field.ty
                       (Structural_map.field_expr right right_field)
                   in
                   equality_expr ?env left_field_value right_field_value)
          in
          and_expressions parts
      | None ->
          Semantic_ir.Sequence
            [ left.semantic_expr; right.semantic_expr; Semantic_ir.Bool false ])
  | (TRecord fields | TNamed_record { fields; _ }), _ ->
      let parts =
        fields
        |> List.map (fun (field : field) ->
               let left_field =
                 typed_ir field.ty (Structural_map.field_expr left field)
               in
               let right_field =
                 typed_ir field.ty (Structural_map.field_expr right field)
               in
               equality_expr ?env left_field right_field)
      in
      and_expressions parts
  | _ -> Semantic_ir.Infix ("=", left.semantic_expr, right.semantic_expr))

and and_expressions = function
  | [] -> Semantic_ir.Bool true
  | first :: rest ->
      List.fold_left
        (fun expression next -> Semantic_ir.Infix ("&&", expression, next))
        first rest

let pairwise_expressions op args =
  let rec loop acc = function
    | left :: ((right :: _) as rest) ->
        loop (Semantic_ir.Infix (op, left.semantic_expr, right.semantic_expr) :: acc) rest
    | _ -> List.rev acc
  in
  loop [] args

let host_ordering_int_type = function
  | TInt | TOcaml "int" | TOcaml "int64" -> true
  | _ -> false

let host_ordering_int_family = function
  | TInt | TOcaml "int" -> true
  | _ -> false

let host_ordering_int64_type = function
  | TOcaml "int64" -> true
  | _ -> false

let host_int_ordering_expr op left right =
  match (left.ty, right.ty) with
  | TOcaml "int", TInt | TInt, TOcaml "int" ->
      Semantic_ir.Infix (op, left.semantic_expr, right.semantic_expr)
  | _ -> Semantic_ir.Infix (op, left.semantic_expr, right.semantic_expr)

let pairwise_host_int_ordering_expressions op args =
  let rec loop acc = function
    | left :: ((right :: _) as rest) ->
        loop (host_int_ordering_expr op left right :: acc) rest
    | _ -> List.rev acc
  in
  loop [] args

let pairwise_equality_expressions ?env args =
  let rec loop acc = function
    | left :: ((right :: _) as rest) ->
        loop (equality_expr ?env left right :: acc) rest
    | _ -> List.rev acc
  in
  loop [] args

let dynamic_numeric_function = function
  | "<" -> "numeric_less"
  | "<=" -> "numeric_less_equal"
  | ">" -> "numeric_greater"
  | ">=" -> "numeric_greater_equal"
  | _ -> assert false

let dynamic_numeric_pairwise_expressions name args =
  let runtime_function =
    "Lg_runtime.Runtime_dynamic." ^ dynamic_numeric_function name
  in
  let rec loop acc = function
    | left :: ((right :: _) as rest) -> (
        match
          (pack_plain_dynamic_value left, pack_plain_dynamic_value right)
        with
        | Some left, Some right ->
            loop
              (Semantic_ir.Apply
                 (Semantic_ir.Ident runtime_function, [ left; right ])
              :: acc)
              rest
        | _ -> None)
    | _ -> Some (List.rev acc)
  in
  loop [] args

let melange_nil_numeric_args env args =
  match env with
  | Some env when Compiler_environment.target env = Target.Melange ->
      let has_nil = List.exists (fun arg -> Types.equal arg.ty TNil) args in
      let has_numeric = List.exists (fun arg -> Types.is_numeric arg.ty) args in
      if has_nil && has_numeric then
        Some
          (List.map
             (fun arg ->
               if Types.equal arg.ty TNil then
                 typed_ir TFloat
                   (Semantic_ir.Sequence [ arg.semantic_expr; Semantic_ir.Float "0." ])
               else arg)
             args)
      else None
  | Some _ | None -> None

let numeric_type_error name args =
  Error.error
    (name ^ " numeric arguments must all have the same type: "
    ^ String.concat ", " (List.map (fun arg -> Types.source_name arg.ty) args))

let compile ?env name args =
  match args with
  | [] | [ _ ] ->
      Ok (typed_ir TBool (Semantic_ir.Bool (name <> "not=")))
  | first :: _ ->
      if name = "=" || name = "not=" then
        if
          List.for_all
            (fun arg -> equality_type_compatible first.ty arg.ty)
            args
        then
          let equal_expr =
            and_expressions (pairwise_equality_expressions ?env args)
          in
          let expression =
            if name = "not=" then Semantic_ir.Prefix ("not", equal_expr) else equal_expr
          in
          Ok (typed_ir TBool expression)
        else
          Error.error
            (name ^ " arguments must have the same type: "
            ^ String.concat ", " (List.map (fun arg -> Types.source_name arg.ty) args))
      else
        let has_dynamic = List.exists (fun arg -> Types.is_dynamic arg.ty) args in
        if has_dynamic then
          match dynamic_numeric_pairwise_expressions name args with
          | Some expressions ->
              Ok (typed_ir TBool (and_expressions expressions))
          | None ->
              Error.error (name ^ " expects numeric arguments")
        else if
          List.exists (fun arg -> host_ordering_int_type arg.ty) args
          && (List.for_all
                (fun arg -> host_ordering_int_family arg.ty)
                args
             || List.for_all
                  (fun arg -> host_ordering_int64_type arg.ty)
                  args)
        then
          Ok
            (typed_ir TBool
               (and_expressions
                  (pairwise_host_int_ordering_expressions name args)))
        else
          let numeric_ty =
            List.find_map
              (fun arg -> if Types.is_numeric arg.ty then Some arg.ty else None)
              args
          in
          (match numeric_ty with
        | Some expected
          when List.for_all
                 (fun arg ->
                   Types.assignable ~policy:Host_boundary ~expected
                     ~actual:arg.ty)
                 args ->
            Ok
              (typed_ir TBool
                 (and_expressions (pairwise_expressions name args)))
        | Some _
          when List.for_all
                 (fun arg -> Core_float.accepts_mixed_numeric arg.ty)
                 args ->
            Ok
              (typed_ir TBool
                 (and_expressions
                    (pairwise_expressions name
                       (List.map Core_float.widen_to_float args))))
        | Some _ -> (
            match melange_nil_numeric_args env args with
            | Some args
              when List.for_all
                     (fun arg -> Core_float.accepts_mixed_numeric arg.ty)
                     args ->
                Ok
                  (typed_ir TBool
                     (and_expressions
                        (pairwise_expressions name
                           (List.map Core_float.widen_to_float args))))
            | Some _ | None ->
                numeric_type_error name args)
        | _ ->
            numeric_type_error name args)
