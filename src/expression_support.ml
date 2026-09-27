open Types
open Lowered
module Env = Compiler_environment
module String_map = Map.Make (String)

(* Recursive host aliases can reach a callback at different unfolding depths. *)
let equivalent_host_types left right =
  let rec equivalent seen left right =
    if Types.equal left right then true
    else if List.exists (fun (a, b) -> Types.equal a left && Types.equal b right) seen then true
    else
      let seen = (left, right) :: seen in
      let expand name other flipped =
        match Ocaml_signature.transparent_manifest_alias name with
        | Some manifest when not (Types.equal manifest (TOcaml name)) ->
            if flipped then equivalent seen other manifest else equivalent seen manifest other
        | _ -> false
      in
      match left, right with
      | TOcaml name, other -> expand name other false
      | other, TOcaml name -> expand name other true
      | TPoly_variant a, TPoly_variant b when a.bound = b.bound ->
          List.length a.tags = List.length b.tags
          && List.for_all (fun (tag, payload) ->
            match payload, List.assoc_opt tag b.tags with
            | None, Some None -> true
            | Some left, Some (Some right) -> equivalent seen left right
            | _ -> false) a.tags
      | TList a, TList b | TVector a, TVector b | TArray a, TArray b
      | TNullable a, TNullable b | TSeq a, TSeq b -> equivalent seen a b
      | TTuple a, TTuple b ->
          List.length a = List.length b && List.for_all2 (equivalent seen) a b
      | TOcaml_app (a, xs), TOcaml_app (b, ys) when a = b ->
          List.length xs = List.length ys && List.for_all2 (equivalent seen) xs ys
      | _ -> false
  in
  equivalent [] left right

(* Unfold host recursive rows only along the finite constructed value. *)
let rec contextual_variant_type expected actual =
  match (expected, actual) with
  | TOcaml name, TPoly_variant _ -> (
      match Ocaml_signature.of_compiler_type
              (Lg_compiler_support.Ocaml_value.Constructor (name, [])) with
      | TPoly_variant _ as manifest -> contextual_variant_type manifest actual
      | _ -> expected)
  | TPoly_variant expected_row, TPoly_variant actual_row ->
      TPoly_variant
        { expected_row with
          tags = List.map (fun (tag, payload) ->
            let payload = match (payload, List.assoc_opt tag actual_row.tags) with
              | Some expected, Some (Some actual) -> Some (contextual_variant_type expected actual)
              | _ -> payload in
            tag, payload) expected_row.tags }
  | TList expected, TList actual -> TList (contextual_variant_type expected actual)
  | TVector expected, TVector actual -> TVector (contextual_variant_type expected actual)
  | TArray expected, TArray actual -> TArray (contextual_variant_type expected actual)
  | TTuple expected, TTuple actual when List.length expected = List.length actual ->
      TTuple (List.map2 contextual_variant_type expected actual)
  | TNullable expected, TNullable actual -> TNullable (contextual_variant_type expected actual)
  | TOcaml_app ("option", [expected]), TOcaml_app ("option", [actual]) ->
      TOcaml_app ("option", [contextual_variant_type expected actual])
  | _ -> expected

let is_identity_expr name expression =
  match Semantic_ir.unlocated expression with
  | Semantic_ir.Ident candidate -> String.equal candidate name
  | _ -> false

let resolve_forward_record env = function
  | TOcaml name as ty when String.starts_with ~prefix:"__lg_record:" name ->
      let source_name =
        String.sub name (String.length "__lg_record:")
          (String.length name - String.length "__lg_record:")
      in
      (match Resolver.lookup_record_type "" env source_name with
      | Ok record -> TNamed_record record
      | Error _ -> ty)
  | ty -> ty

let rec inject_contextual_closed_sum env ~expected (argument : typed_expr) =
  let identical_closed_sum_option =
    match (expected, argument.ty) with
    | ( (TNullable expected_inner | TOcaml_app ("option", [ expected_inner ])),
        (TNullable actual_inner | TOcaml_app ("option", [ actual_inner ])) ) ->
        (Types.equal expected_inner actual_inner
        || String.equal (Types.ocaml_name expected_inner)
             (Types.ocaml_name actual_inner))
        && Env.variant_constructors expected_inner env <> []
    | _ -> false
  in
  let same_closed_sum_head =
    match (Env.closed_sum_head expected, Env.closed_sum_head argument.ty) with
    | Some expected_name, Some actual_name ->
        String.equal expected_name actual_name
        && Env.is_closed_sum expected env
        && Env.is_closed_sum argument.ty env
    | Some _, None | None, Some _ | None, None -> false
  in
  if identical_closed_sum_option then Some (Ok argument)
  else if same_closed_sum_head then
    let argument_compatible expected actual =
      Types.equal expected actual
      ||
      match (expected, actual) with
      | TVar _, _ | _, TVar _ | TUnknown, _ | _, TUnknown | TMeta _, _
      | _, TMeta _ ->
          true
      | _ -> Types.assignable ~policy:Nominal ~expected ~actual
    in
    match (expected, argument.ty) with
    | TOcaml_app (_, expected_args), TOcaml_app (_, actual_args)
      when List.length expected_args = List.length actual_args
           && List.for_all2 argument_compatible expected_args actual_args ->
        Some (Ok { argument with ty = expected })
    | TOcaml _, TOcaml _ -> Some (Ok { argument with ty = expected })
    | _ ->
        Some
          (Error.error
             ("cannot inject " ^ Types.source_name argument.ty
            ^ " into closed sum " ^ Types.source_name expected))
  else if
    not (Types.equal argument.ty (Types.constraint_value_type argument.ty))
    && Types.equal expected (Types.constraint_value_type argument.ty)
  then None
  else if
    Option.fold ~none:false ~some:(Types.equal expected)
      (Types.reduced_element argument.ty)
    || Option.fold ~none:false ~some:(Types.equal expected)
         (Types.maybe_reduced_callback_element argument.ty)
  then None
  else if
    Env.variant_constructors expected env <> []
    && Option.is_some (Env.find_nil_value_adapter expected env)
    &&
    match argument.ty with
    | TNullable _ | TOcaml_app ("option", [ _ ]) -> true
    | _ -> false
  then
    let actual_inner =
      match argument.ty with
      | TNullable inner | TOcaml_app ("option", [ inner ]) -> inner
      | _ -> assert false
    in
    let payload_name = "__lg_optional_closed_sum_payload" in
    let payload = typed_ir actual_inner (Semantic_ir.Ident payload_name) in
    Option.map
      (Result.map (fun injected ->
           typed_ir expected
             (Semantic_ir.Match
                ( argument.semantic_expr,
                  [
                    ( Semantic_ir.PConstructor ("None", None),
                      Semantic_ir.Apply
                        ( Semantic_ir.Ident
                            (Option.get
                               (Env.find_nil_value_adapter expected env)),
                          [] ) );
                    ( Semantic_ir.PConstructor
                        ("Some", Some (Semantic_ir.PVar payload_name)),
                      injected.semantic_expr );
                  ] ))))
      (inject_contextual_closed_sum env ~expected payload)
  else if
    match (expected, argument.ty) with
    | ( (TNullable _ | TOcaml_app ("option", [ _ ])),
        (TNullable _ | TOcaml_app ("option", [ _ ])) ) ->
        false
    | _, (TNullable _ | TOcaml_app ("option", [ _ ])) -> true
    | _ -> false
  then None
  else
  let constructors =
    Env.variant_constructors expected env
    |> List.map (fun (constructor, payload_types) ->
           (constructor, List.map (resolve_forward_record env) payload_types))
  in
  if constructors = [] then
    match (expected, argument.ty) with
    | ( (TNullable expected_inner | TOcaml_app ("option", [ expected_inner ])),
        (TNullable actual_inner | TOcaml_app ("option", [ actual_inner ])) ) ->
        let payload_name = "__lg_closed_sum_payload" in
        let payload = typed_ir actual_inner (Semantic_ir.Ident payload_name) in
        Option.map
          (Result.map (fun injected ->
               typed_ir expected
                 (Semantic_ir.Match
                    ( argument.semantic_expr,
                      [
                        ( Semantic_ir.PConstructor ("None", None),
                          Semantic_ir.Constructor ("None", None) );
                        ( Semantic_ir.PConstructor
                            ("Some", Some (Semantic_ir.PVar payload_name)),
                          Semantic_ir.Constructor
                            ("Some", Some injected.semantic_expr) );
                      ] ))))
          (inject_contextual_closed_sum env ~expected:expected_inner payload)
    | (TNullable _ | TOcaml_app ("option", [ _ ])), _
      when Option.is_some (Types.next_seq_element argument.ty) ->
        None
    | (TNullable expected_inner | TOcaml_app ("option", [ expected_inner ])), _
      when not (Types.equal argument.ty TNil) ->
        (match
           inject_contextual_closed_sum env ~expected:expected_inner argument
         with
        | Some injected ->
            Some
              (Result.map
                 (fun injected ->
                   typed_ir expected
                     (Semantic_ir.Constructor
                        ("Some", Some injected.semantic_expr)))
                 injected)
        | None
          when Types.equal expected_inner
                 (Types.constraint_value_type expected_inner)
               && String.equal (Types.ocaml_name expected_inner)
                    (Types.ocaml_name argument.ty) ->
            Some
              (Ok
                 (typed_ir expected
                    (Semantic_ir.Constructor
                       ( "Some",
                         Some argument.semantic_expr ))))
        | None -> None)
    | _ -> None
  else if
    Types.is_dynamic argument.ty
    || match argument.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false
  then None
  else if Types.equal expected argument.ty then Some (Ok argument)
  else
    let source_constructors =
      Env.variant_constructors argument.ty env
      |> List.map (fun (constructor, payload_types) ->
             (constructor, List.map (resolve_forward_record env) payload_types))
    in
    let rec inject_source_sum branches = function
      | [] when branches <> [] ->
          Some
            (Ok
               (typed_ir expected
                  (Semantic_ir.Match
                     (argument.semantic_expr, List.rev branches))))
      | [] -> None
      | (constructor, [ payload_ty ]) :: rest ->
          let payload_name = "__lg_source_sum_payload" in
          let payload = typed_ir payload_ty (Semantic_ir.Ident payload_name) in
          (match inject_contextual_closed_sum env ~expected payload with
          | None -> None
          | Some (Error _ as error) -> Some error
          | Some (Ok injected) ->
              inject_source_sum
                (( Semantic_ir.PConstructor
                     (constructor, Some (Semantic_ir.PVar payload_name)),
                   injected.semantic_expr )
                :: branches)
                rest)
      | _ -> None
    in
    match inject_source_sum [] source_constructors with
    | Some _ as injected -> injected
    | None ->
    let directly_assignable expected (argument : typed_expr) =
      let directly_assignable =
        match (expected, argument.ty) with
        | TNamed_record _, _ | _, TNamed_record _ ->
            Types.equal expected argument.ty
        | ( TOcaml_app ("Lg_runtime.Runtime_map.t", _),
            TOcaml_app ("Lg_runtime.Runtime_map.t", _) ) ->
            Types.assignable ~policy:Host_boundary ~expected
              ~actual:argument.ty
        | TOcaml_app ("Lg_runtime.Runtime_map.t", _), _
        | _, TOcaml_app ("Lg_runtime.Runtime_map.t", _) ->
            false
        | _ ->
            Types.assignable ~policy:Host_boundary ~expected
              ~actual:argument.ty
      in
      if directly_assignable then Some (Ok { argument with ty = expected })
      else None
    in
    let adapt_payload expected (argument : typed_expr) =
      if Types.equal expected argument.ty then Some (Ok argument)
      else
        let adapt_item expected actual name =
          let item = typed_ir actual (Semantic_ir.Ident name) in
          if Types.equal expected actual then Some (Ok item)
          else inject_contextual_closed_sum env ~expected item
        in
        let adapt_collection expected_item actual_item item_name mapper =
          match adapt_item expected_item actual_item item_name with
          | Some injected ->
              Some
                (Result.map
                   (fun injected ->
                     typed_ir expected
                       (Semantic_ir.Apply
                          ( Semantic_ir.Ident mapper,
                            [
                              Semantic_ir.Fun
                                ( [ Semantic_ir.PVar item_name ],
                                  injected.semantic_expr );
                              argument.semantic_expr;
                            ] )))
                   injected)
          | None -> directly_assignable expected argument
        in
        match (expected, argument.ty) with
        | TVector expected_item, TVector actual_item ->
            adapt_collection expected_item actual_item
              "__lg_closed_sum_vector_item" "Rrbvec.map"
        | TList expected_item, TList actual_item ->
            adapt_collection expected_item actual_item
              "__lg_closed_sum_list_item" "List.map"
        | _ -> (
            match
              ( Types.dynamic_map_types expected,
                Types.dynamic_map_types argument.ty )
            with
            | Some (expected_key, expected_value),
              Some (actual_key, actual_value) ->
                let key_name = "__lg_closed_sum_map_key" in
                let value_name = "__lg_closed_sum_map_value" in
                let key = adapt_item expected_key actual_key key_name in
                let value = adapt_item expected_value actual_value value_name in
                (match (key, value) with
                | Some key, Some value ->
                    Some
                      (Result.bind key (fun key ->
                           Result.map
                             (fun value ->
                               typed_ir expected
                                 (Semantic_ir.Apply
                                    ( Semantic_ir.Ident
                                        "Lg_runtime.Runtime_map.of_list",
                                      [
                                        Semantic_ir.Apply
                                          ( Semantic_ir.Ident "List.map",
                                            [
                                              Semantic_ir.Fun
                                                ( [
                                                    Semantic_ir.PTuple
                                                      [
                                                        Semantic_ir.PVar key_name;
                                                        Semantic_ir.PVar value_name;
                                                      ];
                                                  ],
                                                  Semantic_ir.Tuple
                                                    [
                                                      key.semantic_expr;
                                                      value.semantic_expr;
                                                    ] );
                                              Semantic_ir.Apply
                                                ( Semantic_ir.Ident
                                                    "Lg_runtime.Runtime_map.to_list",
                                                  [ argument.semantic_expr ] );
                                            ] );
                                      ] )))
                             value))
                | _ -> directly_assignable expected argument)
            | _ -> directly_assignable expected argument)
    in
    let candidates =
      List.filter_map
        (fun ((_, payload_types) as constructor) ->
          match payload_types with
          | [ payload_ty ] ->
              Option.map
                (fun payload -> (constructor, payload))
                (adapt_payload payload_ty argument)
          | [] | _ :: _ :: _ -> None)
        constructors
    in
    let exact_candidates =
      List.filter
        (fun ((_, payload_types), _) ->
          match payload_types with
          | [ payload_ty ] -> Types.equal payload_ty argument.ty
          | [] | _ :: _ :: _ -> false)
        candidates
    in
    let same_collection_shape expected actual =
      match (expected, actual) with
      | TVector _, TVector _
      | TList _, TList _
      | TSeq _, TSeq _
      | TSet _, TSet _
      | TArray _, TArray _ ->
          true
      | ( TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]),
          TOcaml_app ("Lg_runtime.Runtime_map.t", [ _; _ ]) ) ->
          true
      | _ -> false
    in
    let shape_candidates =
      List.filter
        (fun ((_, payload_types), _) ->
          match payload_types with
          | [ payload_ty ] ->
              same_collection_shape payload_ty argument.ty
          | [] | _ :: _ :: _ -> false)
        candidates
    in
    let candidates =
      if exact_candidates <> [] then exact_candidates
      else if shape_candidates <> [] then shape_candidates
      else candidates
    in
    (match candidates with
    | [ ((constructor, [ _ ]), payload) ] ->
        Some
          (Result.map
             (fun payload ->
               typed_ir expected
                 (Semantic_ir.Constructor
                    (constructor, Some payload.semantic_expr)))
             payload)
    | [] ->
        Some
          (Error.error
             ("cannot inject " ^ Types.source_name argument.ty
            ^ " into closed sum " ^ Types.source_name expected))
    | candidates ->
        let names =
          List.map (fun ((name, _), _) -> name) candidates
          |> String.concat ", "
        in
        Some
          (Error.error
             ("ambiguous closed sum injection into " ^ Types.source_name expected
            ^ ": " ^ names ^ " from " ^ Types.source_name argument.ty)))

let adapt_set_callable callable =
  match callable.ty with
  | TSet element_ty ->
      Result.map
        (fun set_module ->
          let set_name = "__lg_callable_set" in
          let item_name = "__lg_callable_set_item" in
          let item = Semantic_ir.Ident item_name in
          let present =
            Semantic_ir.Apply
              ( Semantic_ir.Ident (set_module ^ ".mem"),
                [ item; Semantic_ir.Ident set_name ] )
          in
          typed_ir (TFn ([ element_ty ], TNullable element_ty))
            (Semantic_ir.Let
               ( [ (Semantic_ir.PVar set_name, callable.semantic_expr) ],
                 Semantic_ir.Fun
                   ( [ Semantic_ir.PVar item_name ],
                     Semantic_ir.If
                       ( present,
                         Semantic_ir.Constructor ("Some", Some item),
                         Semantic_ir.Constructor ("None", None) ) ) )))
        (Types.set_module_name element_ty)
  | _ -> Ok callable

let rec truthiness_expression ?(constrained_identifier = true) ?env ty
    expression =
  match Option.bind env (Env.find_truthiness_adapter ty) with
  | Some adapter -> Semantic_ir.Apply (Semantic_ir.Ident adapter, [ expression ])
  | None -> (
  match ty with
  | ty when Edn_value_elaborator.is_value_type ty ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_edn.truthy", [ expression ])
  | ty when Types.is_dynamic ty ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.truthy", [ expression ])
  | ty when Option.is_some (Types.truthy_constraint_info ty) ->
      (match Semantic_ir.unlocated expression with
      | Semantic_ir.Ident name when constrained_identifier ->
          Semantic_ir.Apply
            (Semantic_ir.Ident (name ^ "__truthy"), [ expression ])
      | _ ->
          (* Stable expressions are pure projections safe to duplicate;
             effectful ones get a single-use binding. *)
          if Semantic_ir.is_stable expression then
            Semantic_ir.Apply
              ( Semantic_ir.Apply (Semantic_ir.Ident "fst", [ expression ]),
                [ Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ]) ] )
          else
            let value_name = "__lg_truthy_constrained_value" in
            let value = Semantic_ir.Ident value_name in
            Semantic_ir.Let
              ( [ (Semantic_ir.PVar value_name, expression) ],
                Semantic_ir.Apply
                  ( Semantic_ir.Apply
                      (Semantic_ir.Ident "fst", [ value ]),
                    [ Semantic_ir.Apply (Semantic_ir.Ident "snd", [ value ]) ] ) ))
  | TBool -> expression
  | TNil -> Semantic_ir.Sequence [ expression; Semantic_ir.Bool false ]
  | TNullable payload_ty | TOcaml_app ("option", [ payload_ty ]) ->
      let truthy_payload =
        let payload = Semantic_ir.Ident "truthy_value" in
        match payload_ty with
        | TSeq _ -> Semantic_ir.Bool true
        | TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
            Semantic_ir.Bool true
        | _ -> (
        match Types.truthy_constraint_info payload_ty with
        | Some _ ->
            Semantic_ir.Apply
              ( Semantic_ir.Apply
                  (Semantic_ir.Ident "fst", [ payload ]),
                [ Semantic_ir.Apply (Semantic_ir.Ident "snd", [ payload ]) ] )
        | None -> truthiness_expression ?env payload_ty payload)
      in
      Semantic_ir.Match
        ( expression,
          [
            (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool false);
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar "truthy_value")),
              truthy_payload );
          ] )
  | TOcaml "option" ->
      Semantic_ir.Match
        ( expression,
          [
            (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool false);
            ( Semantic_ir.PConstructor ("Some", Some Semantic_ir.PAny),
              Semantic_ir.Bool true );
          ] )
  | TSeq _ ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "not",
          [
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
                [ expression ] );
          ] )
  | TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "not",
          [
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
                [ expression ] );
          ] )
  | _ -> Semantic_ir.Sequence [ expression; Semantic_ir.Bool true ])

let truthiness_needs_value ?env ty =
  Option.fold ~none:false
    ~some:(fun env -> Option.is_some (Env.find_truthiness_adapter ty env))
    env
  || Types.is_dynamic ty
  || Option.is_some (Types.truthy_constraint_info ty)
  || Edn_value_elaborator.is_value_type ty
  ||
  match ty with
  | TBool | TNullable _ | TOcaml_app ("option", [ _ ]) | TOcaml "option"
  | TSeq _ ->
      true
  | TOcaml_app (name, [ _ ]) -> Types.is_next_seq_type_name name
  | _ -> false

let nil_predicate_needs_value ty =
  Option.is_some (Types.nil_predicate_constraint_info ty)
  || Types.is_dynamic ty
  ||
  match Types.seqable_constraint_info ty with
  | Some ((`Optional | `Optional_sequential), _, _) -> true
  | Some (`Required, _, _) -> false
  | None -> (
      match ty with
      | TNullable _ | TOcaml_app ("option", [ _ ])
      | TOcaml "Lg_edn_backend.t" ->
          true
      | TOcaml_app (name, [ _ ]) -> Types.is_next_seq_type_name name
      | _ -> false)

let rec nil_predicate_expression ty expression =
  match Types.nil_predicate_constraint_info ty with
  | Some _ -> (
      match Semantic_ir.unlocated expression with
      | Semantic_ir.Ident name ->
          Semantic_ir.Apply
            (Semantic_ir.Ident (name ^ "__nil"), [ expression ])
      | _ ->
          Semantic_ir.Apply
            ( Semantic_ir.Apply
                (Semantic_ir.Ident "fst", [ expression ]),
              [ Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ]) ] ))
  | None -> (
      match Types.seqable_constraint_info ty with
      | Some ((`Optional | `Optional_sequential), _, value_ty) ->
          let value =
            match Semantic_ir.unlocated expression with
            | Semantic_ir.Ident _ -> expression
            | _ ->
                Semantic_ir.Apply
                  (Semantic_ir.Ident "snd", [ expression ])
          in
          nil_predicate_expression value_ty value
      | Some (`Required, _, _) | None -> (
      match ty with
      | ty when Types.is_dynamic ty ->
          Semantic_ir.Apply
            (Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.is_nil", [ expression ])
      | TNil -> Semantic_ir.Sequence [ expression; Semantic_ir.Bool true ]
      | TNullable payload_ty | TOcaml_app ("option", [ payload_ty ]) ->
          let value_name = "__lg_optional_nil_value" in
          let value = Semantic_ir.Ident value_name in
          let payload_pattern, payload_is_nil =
            if nil_predicate_needs_value payload_ty then
              let payload_is_nil =
                match Types.nil_predicate_constraint_info payload_ty with
                | Some _ ->
                    Semantic_ir.Apply
                      ( Semantic_ir.Apply
                          (Semantic_ir.Ident "fst", [ value ]),
                        [
                          Semantic_ir.Apply
                            (Semantic_ir.Ident "snd", [ value ]);
                        ] )
                | None -> nil_predicate_expression payload_ty value
              in
              (Semantic_ir.PVar value_name, payload_is_nil)
            else
              ( Semantic_ir.PAny,
                Semantic_ir.Bool (Types.equal payload_ty TNil) )
          in
          Semantic_ir.Match
            ( expression,
              [
                (Semantic_ir.PConstructor ("None", None), Semantic_ir.Bool true);
                ( Semantic_ir.PConstructor
                    ("Some", Some payload_pattern),
                  payload_is_nil );
              ] )
      | TOcaml "Lg_edn_backend.t" ->
          Semantic_ir.Apply
            (Semantic_ir.Ident "Lg_runtime.Runtime_edn.is_nil", [ expression ])
      | TOcaml_app (name, [ _ ]) when Types.is_next_seq_type_name name ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
              [ expression ] )
      | _ -> Semantic_ir.Sequence [ expression; Semantic_ir.Bool false ]))

let condition_expression ~env expr =
  Ok (truthiness_expression ~env expr.ty expr.semantic_expr)

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

let rec drop n xs =
  if n <= 0 then xs
  else match xs with [] -> [] | _ :: rest -> drop (n - 1) rest

let option_for_all predicate = function
  | None -> true
  | Some value -> predicate value

let is_ocaml_owned_type = function
  | TFloat | TChar | TArray _ | TRef _ | TOcaml _ | TOcaml_app _ | TTuple _ ->
      true
  | _ -> false

let is_ocaml_constructor_pattern_target target_ty name =
  is_ocaml_owned_type target_ty
  ||
  match target_ty with
     | TNullable _ -> List.mem name [ "Some"; "None" ]
     | TUnknown | TMeta _ | TVar _ ->
         List.mem name [ "Some"; "None"; "Ok"; "Error" ]
         || String.contains name '.' || String.contains name '/'
  | _ -> false

let protocol_value_type ty =
  let value_ty = Types.constraint_value_type ty in
  if Types.equal value_ty ty then None else Some value_ty

let protocol_has_value expected ty =
  match protocol_value_type ty with
  | Some value_ty -> Types.equal expected value_ty
  | None -> false

let rec implicit_edn_branch_value ty =
  match Types.constraint_value_type ty with
  | TNamed_record _ -> false
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      implicit_edn_branch_value inner
  | (TList _ | TVector _ | TSet _ | TSeq _ | TArray _ | TTuple _) -> false
  | ty when Option.is_some (Types.dynamic_map_types ty) -> false
  | ty -> Edn_value_elaborator.is_packable ty

let rec merge_branch_types left right =
  let compiler_generated_anonymous_record (record : named_record) =
    let name = record.type_name in
    let is_generated_name =
      String.length name > 1
      && name.[0] = 't'
      && String.for_all
           (fun character -> character >= '0' && character <= '9')
           (String.sub name 1 (String.length name - 1))
    in
    (not record.nominal) && record.extensible && is_generated_name
  in
  let merge_named_record_fields left_fields right_fields =
    let rec merge_fields merged = function
      | [] -> Some (List.rev merged)
      | (left_field : field) :: rest -> (
          match Types.find_field left_field.keyword right_fields with
          | None -> None
          | Some right_field ->
              Option.bind
                (merge_branch_types left_field.ty right_field.ty)
                (fun ty -> merge_fields ({ left_field with ty } :: merged) rest))
    in
    merge_fields [] left_fields
  in
  let anonymous_record_type_arguments record fields =
    let rec find_map2 f left right =
      match (left, right) with
      | [], [] -> None
      | left :: left_rest, right :: right_rest -> (
          match f left right with
          | Some _ as result -> result
          | None -> find_map2 f left_rest right_rest)
      | _ -> None
    in
    let field_by_keyword keyword fields =
      Types.find_field keyword fields
    in
    let rec argument_for parameter original merged =
      match (original, merged) with
      | TVar name, ty when name = parameter -> Some ty
      | (TUnknown | TMeta _ | TNil), ty when parameter = "a" -> Some ty
      | TNullable original, TNullable merged
      | TArray original, TArray merged
      | TRef original, TRef merged
      | TList original, TList merged
      | TVector original, TVector merged
      | TSet original, TSet merged
      | TSeq original, TSeq merged ->
          argument_for parameter original merged
      | TOcaml_app (_, original), TOcaml_app (_, merged)
      | TTuple original, TTuple merged
        when List.length original = List.length merged ->
          find_map2 (argument_for parameter) original merged
      | TRecord original_fields, TRecord merged_fields ->
          original_fields
          |> List.find_map (fun (field : field) ->
                 match field_by_keyword field.keyword merged_fields with
                 | None -> None
                 | Some merged_field ->
                     argument_for parameter field.ty merged_field.ty)
      | TNamed_record original, TNamed_record merged
        when List.length original.type_arguments
             = List.length merged.type_arguments ->
          find_map2
            (argument_for parameter)
            original.type_arguments merged.type_arguments
      | _ -> None
    in
    let argument_for_field parameter (field : field) =
      match field_by_keyword field.keyword fields with
      | None -> None
      | Some merged_field -> argument_for parameter field.ty merged_field.ty
    in
    List.map2
      (fun parameter fallback ->
        record.fields
        |> List.find_map (argument_for_field parameter)
        |> Option.value ~default:fallback)
      record.type_parameters record.type_arguments
  in
  let host_record_type = function
    | TOcaml type_name -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record) -> Some (TNamed_record record)
        | Ok _ | Error _ -> None)
    | TOcaml_app (type_name, arguments) -> (
        match Ocaml_signature.record_type type_name with
        | Ok (TNamed_record record)
          when List.length record.type_parameters = List.length arguments ->
            let substitutions =
              List.combine record.type_parameters arguments
              |> List.map (fun (parameter, argument) ->
                     (Type_solver.Declared parameter, argument))
              |> Type_solver.of_list
            in
            Some (Type_solver.apply substitutions (TNamed_record record))
        | Ok _ | Error _ -> None)
    | _ -> None
  in
  match (left, right) with
  | TPoly_variant left, TPoly_variant right -> Option.map (fun row -> TPoly_variant row) (Variant_row.merge merge_branch_types left right)
  | TNamed_record left_record, TNamed_record right_record
    when Type_id.equal left_record.type_id right_record.type_id
         && left_record.type_arguments <> right_record.type_arguments -> (
      match Type_solver.unify Type_solver.empty left right with
      | Ok substitutions -> Some (Type_solver.apply substitutions left)
      | Error _ -> None)
  | left, right when Types.equal left right -> Some left
  | left, right ->
    match (left, right) with
    | TNamed_record left_record, TNamed_record right_record
      when compiler_generated_anonymous_record left_record
           && compiler_generated_anonymous_record right_record
           && Types.row_compatible ~expected:left ~actual:right
           && Types.row_compatible ~expected:right ~actual:left ->
        Option.map
          (fun fields ->
            let type_arguments =
              anonymous_record_type_arguments left_record fields
            in
            TNamed_record { left_record with fields; type_arguments })
          (merge_named_record_fields left_record.fields right_record.fields)
    | TNamed_record left_record, TNamed_record right_record
      when left_record.type_name = right_record.type_name
           && List.length left_record.type_arguments
              = List.length right_record.type_arguments -> (
        let rec merge_arguments merged left right =
          match (left, right) with
          | [], [] ->
              Some
                (TNamed_record
                   { left_record with type_arguments = List.rev merged })
          | left :: left_rest, right :: right_rest ->
              Option.bind (merge_branch_types left right) (fun argument ->
                  merge_arguments (argument :: merged) left_rest right_rest)
          | _ -> None
        in
        merge_arguments [] left_record.type_arguments
          right_record.type_arguments)
    | TNamed_record record, TOcaml name
    | TOcaml name, TNamed_record record
      when (record.type_name = name || Type_id.name record.type_id = name)
           && record.type_arguments = [] ->
        Some (TNamed_record record)
    | TNamed_record record, TOcaml_app (name, arguments)
    | TOcaml_app (name, arguments), TNamed_record record
      when (record.type_name = name || Type_id.name record.type_id = name)
           && List.length record.type_arguments = List.length arguments ->
        let rec merge_arguments merged left right =
          match (left, right) with
          | [], [] ->
              Some
                (TNamed_record
                   { record with type_arguments = List.rev merged })
          | left :: left_rest, right :: right_rest ->
              Option.bind (merge_branch_types left right) (fun argument ->
                  merge_arguments (argument :: merged) left_rest right_rest)
          | _ -> None
        in
        merge_arguments [] record.type_arguments arguments
    | (TRecord _ as structural), host
      when Option.is_some (host_record_type host) ->
        let named = Option.get (host_record_type host) in
        merge_branch_types structural named
    | host, (TRecord _ as structural)
      when Option.is_some (host_record_type host) ->
        let named = Option.get (host_record_type host) in
        merge_branch_types named structural
    | TRecord left_fields, TRecord right_fields
      when List.length left_fields = List.length right_fields ->
        Option.map
          (fun fields -> TRecord fields)
          (merge_named_record_fields left_fields right_fields)
    | TOcaml_app (left_name, left_args), TOcaml_app (right_name, right_args)
      when left_name = right_name
           && List.length left_args = List.length right_args ->
        let merge_host_arg left right =
          match (left, right) with
          (* An absent constructor payload must not erase a shared type variable. *)
          | TUnknown, ty | ty, TUnknown -> Some ty
          | (TMeta _ | TVar _), ty
          | ty, (TMeta _ | TVar _) ->
              Some ty
          | _ -> merge_branch_types left right
        in
        let rec merge_arguments merged left right =
          match (left, right) with
          | [], [] ->
              Some (TOcaml_app (left_name, List.rev merged))
          | left :: left_rest, right :: right_rest ->
              Option.bind (merge_host_arg left right) (fun ty ->
                  merge_arguments (ty :: merged) left_rest right_rest)
          | _ -> None
        in
        merge_arguments [] left_args right_args
    | TRecord _, (TNamed_record _ as named)
      when Types.row_compatible ~expected:left ~actual:named ->
        Some named
    | (TNamed_record _ as named), TRecord _
      when Types.row_compatible ~expected:right ~actual:named ->
        Some named
    | (TRecord _ as structural), (TNamed_record _ as named)
      when Types.row_compatible ~expected:structural ~actual:right ->
        Some named
    | (TNamed_record _ as named), (TRecord _ as structural)
      when Types.row_compatible ~expected:structural ~actual:left ->
        Some named
    | left, right when protocol_has_value right left ->
        Some right
    | left, right when protocol_has_value left right ->
        Some left
    | left, right
      when Option.is_some (protocol_value_type right) ->
        merge_branch_types left (Option.get (protocol_value_type right))
    | left, right
      when Option.is_some (protocol_value_type left) ->
        merge_branch_types (Option.get (protocol_value_type left)) right
    | left, right when Types.is_dynamic left || Types.is_dynamic right ->
        Some (Types.dynamic_constraint TUnknown)
    | TNil, (TOcaml_app ("option", _) as option_ty)
    | (TOcaml_app ("option", _) as option_ty), TNil
    | TNil, (TOcaml "option" as option_ty)
    | (TOcaml "option" as option_ty), TNil ->
        Some option_ty
    | TNil, TNullable inner | TNullable inner, TNil -> Some (TNullable inner)
    | TNil, ty | ty, TNil -> Some (TNullable ty)
    | ( TNullable (TVector (TOcaml "Lg_edn_backend.t") as vector_ty),
        TVector actual )
    | ( TVector actual,
        TNullable (TVector (TOcaml "Lg_edn_backend.t") as vector_ty) )
    | ( TOcaml_app
          ("option", [ (TVector (TOcaml "Lg_edn_backend.t") as vector_ty) ]),
        TVector actual )
    | ( TVector actual,
        TOcaml_app
          ("option", [ (TVector (TOcaml "Lg_edn_backend.t") as vector_ty) ]) )
      when Edn_value_elaborator.is_packable actual ->
        Some (TNullable vector_ty)
    | TNullable left, TNullable right -> (
        match merge_branch_types left right with
        | Some inner -> Some (TNullable inner)
        | None -> None)
    | TOcaml_app ("option", [ left ]), TOcaml_app ("option", [ right ]) ->
        Option.map
          (fun merged -> TOcaml_app ("option", [ merged ]))
          (merge_branch_types left right)
    | TNullable left, TOcaml_app ("option", [ right ])
    | TOcaml_app ("option", [ left ]), TNullable right ->
        Option.map
          (fun merged -> TNullable merged)
          (merge_branch_types left right)
    | TNullable inner, ty | ty, TNullable inner ->
        Option.map
          (fun merged -> TNullable merged)
          (merge_branch_types inner ty)
    | TOcaml_app ("option", [ inner ]), ty
    | ty, TOcaml_app ("option", [ inner ]) ->
        Option.map
          (fun merged -> TOcaml_app ("option", [ merged ]))
          (merge_branch_types inner ty)
    | TFn (left_params, left_return), TFn (right_params, right_return)
      when List.length left_params = List.length right_params ->
        let merge_parameter left right =
          match (left, right) with
          | TArray (TUnknown | TMeta _ | TVar _), (TUnknown | TMeta _ | TVar _)
          | (TUnknown | TMeta _ | TVar _), TArray (TUnknown | TMeta _ | TVar _) ->
              Some (TArray (Types.dynamic_constraint TUnknown))
          | _ when Types.equal left right -> Some left
          | _ -> merge_branch_types left right
        in
        let rec merge_parameters merged left right =
          match (left, right) with
          | [], [] -> Some (List.rev merged)
          | left :: left_rest, right :: right_rest ->
              Option.bind (merge_parameter left right) (fun parameter ->
                  merge_parameters (parameter :: merged) left_rest right_rest)
          | _ -> None
        in
        Option.bind (merge_parameters [] left_params right_params)
          (fun parameters ->
            Option.map
              (fun return_ty -> TFn (parameters, return_ty))
              (merge_branch_types left_return right_return))
    | TTuple left, TTuple right ->
        let rec merge_items merged left right =
          match (left, right) with
          | [], [] -> Some (TTuple (List.rev merged))
          | left :: left_rest, right :: right_rest ->
              Option.bind (merge_branch_types left right) (fun item ->
                  merge_items (item :: merged) left_rest right_rest)
          | _ -> None
        in
        merge_items [] left right
    | TList left, TList right ->
        Option.map (fun inner -> TList inner) (merge_branch_types left right)
    | TVector left, TVector right ->
        let merged_element =
          match (left, right) with
          | (TUnknown | TMeta _ | TVar _), ty
          | ty, (TUnknown | TMeta _ | TVar _) ->
              Some ty
          | _ -> merge_branch_types left right
        in
        Option.map (fun inner -> TVector inner) merged_element
    | TSet left, TSet right ->
        Option.map (fun inner -> TSet inner) (merge_branch_types left right)
    | TSeq left, TSeq right ->
        Option.map (fun inner -> TSeq inner) (merge_branch_types left right)
    | TSeq left, TList right | TList right, TSeq left ->
        Option.map (fun inner -> TSeq inner) (merge_branch_types left right)
    | TArray left, TArray right ->
        let merged_element =
          match (left, right) with
          | (TUnknown | TMeta _ | TVar _), ty | ty, (TUnknown | TMeta _ | TVar _) -> Some ty
          | _ -> merge_branch_types left right
        in
        Option.map (fun inner -> TArray inner) merged_element
    | (TOcaml "Lg_edn_backend.t" as edn), ty
      when implicit_edn_branch_value ty ->
        Some edn
    | ty, (TOcaml "Lg_edn_backend.t" as edn)
      when implicit_edn_branch_value ty ->
        Some edn
    | TUnknown, ty | ty, TUnknown -> Some ty
    | TVar _, TVar _ -> Some left
    | TVar _, ty | ty, TVar _ -> Some ty
    | TMeta _, _ | _, TMeta _ -> (
        match Type_solver.unify Type_solver.empty left right with
        | Ok substitutions -> Some (Type_solver.apply substitutions left)
        | Error _ -> None)
    | _ when Types.defer_to_ocaml ~expected:left ~actual:right -> Some left
    | _ -> None

let branch_types_compatible left right =
  Option.is_some (merge_branch_types left right)

let heterogeneous_collection_type_error collection types =
  let types =
    types |> List.map Types.source_name |> List.sort_uniq String.compare
  in
  Error.error
    ("heterogeneous " ^ collection
   ^ (if collection = "map keys" || collection = "map values" then
        " have types "
      else " has element types ")
   ^ String.concat " | " types
   ^ "; define a closed sum type containing these types")

let heterogeneous_collection_error collection values =
  heterogeneous_collection_type_error collection
    (List.map (fun value -> value.ty) values)

let edn_scalar_collection_type = function
  | TNil | TBool | TInt | TOcaml "int" | TChar | TString | TRegex | TSymbol
  | TKeyword | TOcaml "Lg_edn_backend.t" ->
      true
  | _ -> false

let merge_collection_types collection types =
  let normalize_named_host_records types =
    let named_records =
      List.filter_map
        (function
          | TNamed_record record -> Some record
          | _ -> None)
        types
    in
    let matching_record name arguments =
      named_records
      |> List.find_opt (fun record ->
             (record.type_name = name || Type_id.name record.type_id = name)
             && List.length record.type_arguments = List.length arguments)
    in
    List.map
      (function
        | TOcaml name -> (
            match matching_record name [] with
            | Some record -> TNamed_record record
            | None -> TOcaml name)
        | TOcaml_app (name, arguments) -> (
            match matching_record name arguments with
            | Some record -> TNamed_record record
            | None -> TOcaml_app (name, arguments))
        | ty -> ty)
      types
  in
  let types = normalize_named_host_records types in
  match types with
  | [] -> Ok TUnknown
  | first :: rest ->
      let merged =
        List.fold_left
          (fun merged ty ->
            Option.bind merged (fun merged -> merge_branch_types merged ty))
          (Some first) rest
      in
      (match merged with
      | Some ty when not (Types.contains_dynamic ty) -> Ok ty
      | Some _ | None
        when collection = "list"
             && List.for_all edn_scalar_collection_type types ->
          Ok (TOcaml "Lg_edn_backend.t")
      | Some _ | None -> heterogeneous_collection_type_error collection types)

let merge_collection_value_types collection values =
  merge_collection_types collection (List.map (fun value -> value.ty) values)

let set_module_name env ty =
  match Types.set_module_name ty with
  | Ok _ as set_module -> set_module
  | Error _ as error ->
      let emitted_name =
        match ty with
        | TOcaml name | TOcaml_app (name, _) -> Some name
        | _ -> None
      in
      (match
         Option.bind emitted_name (fun name ->
             Type_registry.find_by_emitted_name name
               (Compiler_environment.types env))
       with
      | Some { kind = Type_registry.Variant; _ } ->
          Ok "Lg_runtime.Runtime_poly_set"
      | Some _ | None -> error)

let capability_storage_expression ty expression =
  let rec build name = function
    | ty when Types.is_dynamic ty -> Semantic_ir.Ident name
    | ty ->
        let layer witness_name value_ty =
          Semantic_ir.Tuple
            [ Semantic_ir.Ident witness_name; build name value_ty ]
        in
        match Types.protocol_constraint_info ty with
        | Some (protocol_id, _, value_ty) ->
            layer (Types.protocol_witness_name name protocol_id) value_ty
        | None -> (
            match Types.truthy_constraint_info ty with
            | Some value_ty -> layer (name ^ "__truthy") value_ty
            | None -> (
                match Types.nil_predicate_constraint_info ty with
                | Some value_ty -> layer (name ^ "__nil") value_ty
                | None -> (
                    match Types.printable_constraint_info ty with
                    | Some value_ty ->
                        Semantic_ir.Tuple
                          [
                            Semantic_ir.Tuple
                              [ Semantic_ir.Ident (name ^ "__print");
                                Semantic_ir.Ident (name ^ "__pr");
                              ];
                            build name value_ty;
                          ]
                    | None -> (
                        match Types.exception_data_constraint_info ty with
                        | Some value_ty -> layer (name ^ "__ex_data") value_ty
                        | None -> (
                        match Types.hashable_constraint_info ty with
                        | Some value_ty -> layer (name ^ "__hash") value_ty
                        | None -> (
                            match Types.comparable_constraint_info ty with
                            | Some value_ty ->
                                layer (name ^ "__compare") value_ty
                            | None -> (
                                match Types.array_index_constraint_info ty with
                                | Some value_ty ->
                                    layer (name ^ "__index") value_ty
                                | None -> (
                        match Types.symbol_predicate_constraint_info ty with
                        | Some value_ty -> layer (name ^ "__symbol") value_ty
                        | None -> (
                            match Types.contains_constraint_info ty with
                            | Some (_, value_ty) ->
                                layer (name ^ "__contains") value_ty
                            | None -> (
                                match ty with
                                | TConstraint
                                    (Seqable_constraint
                                      { requirement; storage = value_ty; _ }) ->
                                    let witness_name =
                                      if requirement = Required
                                      then name ^ "__seq"
                                      else name ^ "__seq_optional"
                                    in
                                    layer witness_name value_ty
                                | _ -> Semantic_ir.Ident name))))))))))
  in
  match Semantic_ir.unlocated expression with
  | Semantic_ir.Ident name -> build name ty
  | _ -> expression

let pack_plain_dynamic_value value =
  if
    Types.is_dynamic value.ty
    || match value.ty with TUnknown | TMeta _ | TVar _ -> true | _ -> false
  then
      Some
        (Semantic_ir.PackDynamic
           {
             source_ty = value.ty;
             target_ty = Types.dynamic_constraint value.ty;
             conversion = value.semantic_expr;
           })
  else None

let coerce_expression_to_type ?(stored = false) target_ty source_ty expression =
  match (target_ty, source_ty) with
  | TOcaml "Lg_edn_backend.t", TOcaml "Lg_edn_backend.t" -> expression
  | TOcaml "Lg_edn_backend.t", TNil ->
      Semantic_ir.Sequence
        [ expression; Semantic_ir.Ident "Lg_runtime.Runtime_metadata.nil" ]
  | TOcaml "Lg_edn_backend.t", TBool ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_bool", [ expression ])
  | TOcaml "Lg_edn_backend.t", (TInt | TOcaml "int") ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_int", [ expression ])
  | TOcaml "Lg_edn_backend.t", TChar ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_char", [ expression ])
  | TOcaml "Lg_edn_backend.t", TString ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_string", [ expression ])
  | TOcaml "Lg_edn_backend.t", TRegex ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_regex", [ expression ])
  | TOcaml "Lg_edn_backend.t", TSymbol ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_symbol", [ expression ])
  | TOcaml "Lg_edn_backend.t", TKeyword ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "Lg_runtime.Runtime_metadata.of_keyword", [ expression ])
  | target_ty, source_ty when protocol_has_value target_ty source_ty ->
      let rec unwrap ty expression =
        let unwrap_stored value_ty =
          let expression =
            if stored then
              Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ])
            else
              match Semantic_ir.unlocated expression with
              | Semantic_ir.Ident _ -> expression
              | _ ->
                  Semantic_ir.Apply (Semantic_ir.Ident "snd", [ expression ])
          in
          unwrap value_ty expression
        in
        match Types.protocol_constraint_info ty with
        | Some (_, _, value_ty) -> unwrap_stored value_ty
        | None -> (
            match Types.truthy_constraint_info ty with
            | Some value_ty -> unwrap_stored value_ty
            | None -> (
                match Types.nil_predicate_constraint_info ty with
                | Some value_ty -> unwrap_stored value_ty
                | None -> (
                match Types.printable_constraint_info ty with
                | Some value_ty -> unwrap_stored value_ty
                | None -> (
                    match Types.exception_data_constraint_info ty with
                    | Some value_ty -> unwrap_stored value_ty
                    | None -> (
                    match Types.hashable_constraint_info ty with
                    | Some value_ty -> unwrap_stored value_ty
                    | None -> (
                        match Types.comparable_constraint_info ty with
                        | Some value_ty -> unwrap_stored value_ty
                        | None -> (
                            match Types.array_index_constraint_info ty with
                            | Some value_ty -> unwrap_stored value_ty
                            | None -> (
                    match Types.symbol_predicate_constraint_info ty with
                    | Some value_ty -> unwrap_stored value_ty
                    | None -> expression))))))))
      in
      unwrap source_ty expression
  | TSeq target_inner, (TList source_inner | TVector source_inner) ->
      let sequence =
        match source_ty with
        | TList _ ->
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.of_list",
                [ expression ] )
        | TVector _ ->
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.of_vector",
                [ expression ] )
        | _ -> assert false
      in
      let _ = (target_inner, source_inner) in
      sequence
  | TVector target_inner, TSeq source_inner
    when Types.assignable ~policy:Host_boundary ~expected:target_inner
           ~actual:source_inner ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Rrbvec.of_list",
          [
            Semantic_ir.Apply
              (Semantic_ir.Ident "List.of_seq", [ expression ]);
          ] )
  | TVector target_inner, TList source_inner
    when Types.assignable ~policy:Host_boundary ~expected:target_inner
           ~actual:source_inner ->
      Semantic_ir.Apply (Semantic_ir.Ident "Rrbvec.of_list", [ expression ])
  | TSet target_inner, TSet (TUnknown | TMeta _ | TVar _) -> (
      match Types.set_module_name target_inner with
      | Ok set_module ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident (set_module ^ ".of_list"),
              [
                Semantic_ir.Apply
                  ( Semantic_ir.Ident
                      "Lg_runtime.Runtime_poly_set.elements",
                    [ expression ] );
              ] )
      | Error _ -> expression)
  | TSet (TUnknown | TMeta _ | TVar _), TSet source_inner -> (
      match Types.set_module_name source_inner with
      | Ok set_module ->
          Semantic_ir.Apply
            ( Semantic_ir.Ident "Lg_runtime.Runtime_poly_set.of_list",
              [
                Semantic_ir.Apply
                  ( Semantic_ir.Ident (set_module ^ ".elements"),
                    [ expression ] );
              ] )
      | Error _ -> expression)
  | target_ty, (TNullable source_ty | TOcaml_app ("option", [ source_ty ]))
    when (match target_ty with
         | TRecord _ | TNamed_record _ | TArray _
         | TOcaml_app ("array", [ _ ]) ->
             true
         | _ -> false)
         && Types.assignable ~policy:Host_boundary ~expected:target_ty
              ~actual:source_ty ->
      Semantic_ir.Apply (Semantic_ir.Ident "Option.get", [ expression ])
  | ( (TNullable target | TOcaml_app ("option", [ target ])),
      TOcaml_app (name, [ _ ]) )
    when Types.is_next_seq_type_name name ->
      let sequence_name = "__lg_nullable_next_sequence" in
      let sequence = Semantic_ir.Ident sequence_name in
      let _ = target in
      let present = sequence in
      Semantic_ir.Let
        ( [ (Semantic_ir.PVar sequence_name, expression) ],
          Semantic_ir.If
            ( Semantic_ir.Apply
                ( Semantic_ir.Ident "Lg_runtime.Runtime_seq.is_empty",
                  [ sequence ] ),
              Semantic_ir.Constructor ("None", None),
              Semantic_ir.Constructor ("Some", Some present) ) )
  | target_ty,
    TConstraint (Seqable_constraint { requirement; _ })
    when (match target_ty with
         | TSeq _ -> true
         | TOcaml_app (name, [ _ ]) -> Types.is_next_seq_type_name name
         | _ -> false) ->
      let adapter_name = "__lg_coerce_seq_adapter" in
      let value_name = "__lg_coerce_seq_value" in
      let adapter = Semantic_ir.Ident adapter_name in
      let adapter =
        if requirement = Required then adapter
        else
          Semantic_ir.Match
            ( adapter,
              [
                ( Semantic_ir.PConstructor ("None", None),
                  Semantic_ir.Apply
                    ( Semantic_ir.Ident "invalid_arg",
                      [ Semantic_ir.String "value is not sequential" ] ) );
                ( Semantic_ir.PConstructor
                    ("Some", Some (Semantic_ir.PVar adapter_name)),
                  Semantic_ir.Ident adapter_name );
              ] )
      in
      Semantic_ir.Match
        ( (if stored then expression
           else capability_storage_expression source_ty expression),
          [
            ( Semantic_ir.PTuple
                [ Semantic_ir.PVar adapter_name; Semantic_ir.PVar value_name ],
              Semantic_ir.Apply (adapter, [ Semantic_ir.Ident value_name ]) );
          ] )
  | TNullable _, TNil -> expression
  | TNullable _, TNullable _ -> expression
  | TNullable _, TOcaml_app ("option", [ _ ]) -> expression
  | TNullable _, _ ->
      Semantic_ir.Constructor
        ("Some", Some (Semantic_ir.annotate source_ty expression))
  | TOcaml_app ("option", [ _ ]), TNil -> expression
  | TOcaml_app ("option", [ _ ]), TNullable _ -> expression
  | TOcaml_app ("option", [ _ ]), TOcaml_app ("option", [ _ ]) -> expression
  | TOcaml_app ("option", [ _ ]), _ ->
      Semantic_ir.Constructor
        ("Some", Some (Semantic_ir.annotate source_ty expression))
  | _ -> expression

let merge_branch_expressions left right =
  let merge_tuple_items left_types left_items right_types right_items =
    let rec merge types left_values right_values =
      match (types, left_values, right_values) with
      | [], [], [] -> Some ([], [], [])
      | ( (left_ty, right_ty) :: types,
          left_value :: left_values,
          right_value :: right_values ) ->
          let merged_ty = merge_branch_types left_ty right_ty in
          Option.bind merged_ty (fun merged_ty ->
              Option.map
                (fun (merged_types, merged_left, merged_right) ->
                  ( merged_ty :: merged_types,
                    coerce_expression_to_type ~stored:true merged_ty left_ty
                      left_value
                    :: merged_left,
                    coerce_expression_to_type ~stored:true merged_ty right_ty
                      right_value
                    :: merged_right ))
                (merge types left_values right_values))
      | _ -> None
    in
    merge (List.combine left_types right_types) left_items right_items
  in
  match (left.ty, right.ty) with
  | TTuple left_types, TTuple right_types
    when List.length left_types = List.length right_types ->
      let left_names =
        List.mapi
          (fun index _ -> "__lg_left_tuple_" ^ string_of_int index)
          left_types
      in
      let right_names =
        List.mapi
          (fun index _ -> "__lg_right_tuple_" ^ string_of_int index)
          right_types
      in
      Option.map
        (fun (types, left_items, right_items) ->
          let rebuild expression names items =
            Semantic_ir.Match
              ( expression,
                [
                  ( Semantic_ir.PTuple
                      (List.map (fun name -> Semantic_ir.PVar name) names),
                    Semantic_ir.Tuple items );
                ] )
          in
          ( TTuple types,
            rebuild left.semantic_expr left_names left_items,
            rebuild right.semantic_expr right_names right_items ))
        (merge_tuple_items left_types
           (List.map (fun name -> Semantic_ir.Ident name) left_names)
           right_types
           (List.map (fun name -> Semantic_ir.Ident name) right_names))
  | _ -> (
  let continue expression =
    Semantic_ir.Apply
          ( Semantic_ir.Ident "Lg_runtime.Runtime_reduced.continue",
            [ expression ] )
  in
  match (Types.reduced_element left.ty, Types.reduced_element right.ty) with
      | Some left_inner, Some right_inner
        when Types.equal left_inner right_inner ->
      Some (left.ty, left.semantic_expr, right.semantic_expr)
  | Some TNil, None ->
      let nullable = TNullable right.ty in
      Some
        ( Types.reduced nullable,
          left.semantic_expr,
              continue
                (Semantic_ir.Constructor ("Some", Some right.semantic_expr)) )
  | None, Some TNil ->
      let nullable = TNullable left.ty in
      Some
        ( Types.reduced nullable,
              continue
                (Semantic_ir.Constructor ("Some", Some left.semantic_expr)),
          right.semantic_expr )
  | Some inner, None when Types.equal inner right.ty ->
      Some (left.ty, left.semantic_expr, continue right.semantic_expr)
  | None, Some inner when Types.equal left.ty inner ->
      Some (right.ty, continue left.semantic_expr, right.semantic_expr)
  | _ -> (
      match merge_branch_types left.ty right.ty with
      | None -> None
      | Some result_ty ->
          let coerce branch =
            let expression =
              match (result_ty, branch.ty) with
              | TNamed_record target_record, TNamed_record source_record
                when (not target_record.nominal)
                     && (not source_record.nominal)
                     && not
                          (Type_id.equal target_record.type_id
                             source_record.type_id)
                     && Types.row_compatible ~expected:result_ty
                          ~actual:branch.ty ->
                  let branch = { branch with record_values = None } in
                  (Structural_map.as_named_record target_record branch)
                    .semantic_expr
              | _ ->
                  coerce_expression_to_type result_ty branch.ty
                    branch.semantic_expr
            in
            match Semantic_ir.unlocated expression with
            | Semantic_ir.Ident name
              when Types.equal result_ty branch.ty
                   && Option.is_some (protocol_value_type branch.ty)
                   && not (String.starts_with ~prefix:"__lg_" name) ->
                capability_storage_expression branch.ty expression
            | _ -> expression
          in
          Some
            (result_ty, coerce left, coerce right)))

let unresolved_contextual_type = function TList TUnknown -> true | _ -> false

let lg_metadata_type_for_ocaml_payload = function
  | TOcaml "int64" as ty -> ty
  | TOcaml "float" -> TFloat
  | TOcaml "char" -> TChar
  | TOcaml "string" -> TString
  | TOcaml "bool" -> TBool
  | TOcaml "unit" -> TUnit
  | ty -> ty

let rec lg_metadata_type_for_ocaml_type = function
  | TOcaml "int64" as ty -> ty
  | TOcaml "float" -> TFloat
  | TOcaml "char" -> TChar
  | TOcaml "string" -> TString
  | TOcaml "bool" -> TBool
  | TOcaml "unit" -> TUnit
  | TTuple args -> TTuple (List.map lg_metadata_type_for_ocaml_type args)
  | ty -> ty

let ocaml_builtin_constructor_payloads target_ty constructor_name =
  match (target_ty, constructor_name) with
  | TNullable payload_ty, "Some" -> Some [ payload_ty ]
  | TNullable _, "None" -> Some []
  | TOcaml "option", "Some" -> Some [ TUnknown ]
  | TOcaml "option", "None" -> Some []
  | TOcaml_app ("option", [ payload_ty ]), "Some" ->
      Some [ lg_metadata_type_for_ocaml_payload payload_ty ]
  | TOcaml_app ("option", [ _ ]), "None" -> Some []
  | TOcaml "result", "Ok" -> Some [ TUnknown ]
  | TOcaml "result", "Error" -> Some [ TUnknown ]
  | TOcaml_app ("result", [ ok_ty; _ ]), "Ok" ->
      Some [ lg_metadata_type_for_ocaml_payload ok_ty ]
  | TOcaml_app ("result", [ _; error_ty ]), "Error" ->
      Some [ lg_metadata_type_for_ocaml_payload error_ty ]
  | _ -> None

let record_type_key = Resolver.record_type_key

let record_type_application type_name arguments =
  let type_name = Types.ocaml_record_type_name type_name in
  let argument_name = function
    | TUnknown | TMeta _ | TVar _ -> "_"
    | argument -> Types.ocaml_type_argument_name argument
  in
  match arguments with
  | [] -> type_name
  | [ argument ] -> argument_name argument ^ " " ^ type_name
  | arguments ->
      "("
      ^ String.concat ", " (List.map argument_name arguments)
      ^ ") " ^ type_name

let existential_record_type_application (record : named_record) =
  record_type_application record.type_name
    (List.map (fun parameter -> TVar parameter) record.type_parameters)

let lookup_record_type = Resolver.lookup_record_type

let starts_with_uppercase name =
  String.length name > 0
  &&
  let first = name.[0] in
  first >= 'A' && first <= 'Z'

let is_constructor_name name =
  let segments =
    name |> String.split_on_char '/'
    |> List.concat_map (String.split_on_char '.')
  in
  match List.rev segments with
  | segment :: _ -> starts_with_uppercase segment
  | [] -> false

let lookup_binding = Resolver.lookup_binding

let deftype_method_name (record : named_record) method_name arity =
  "__deftype/"
  ^ Type_id.to_string record.type_id
  ^ "/" ^ method_name ^ "/" ^ string_of_int arity

let lookup_deftype_method scope env record method_name arity =
  lookup_binding scope env (deftype_method_name record method_name arity)

let print_method_name (record : named_record) =
  "__print_method/" ^ Type_id.to_string record.type_id

let lookup_print_method scope env record =
  lookup_binding scope env (print_method_name record)

let binding_of_expr ?(row_param_types = []) ocaml_name expr =
  let never_returns =
    match Semantic_ir.unlocated expr.semantic_expr with
    | Semantic_ir.Fun (_, body) -> Semantic_ir.never_returns body
    | _ -> false
  in
  let binding =
    Types.binding ~row_param_types ?return_param_index:expr.return_param_index
      ~never_returns ocaml_name expr.ty
  in
  {
    binding with
    ty = Types.align_deferred_param_types binding.ty expr.semantic_expr;
  }
  |> Types.generalize_binding

type anonymous_record_allocation = {
  record : named_record;
  env : Env.t;
  next_type : int;
  fresh : bool;
}

(* Replace unresolved positions with named type variables so the emitted
   declaration actually binds them: each metavariable or declared var keeps one
   parameter per identity, while unknowns/nils get independent parameters.
   Also returns the site's own argument for each parameter so a reused
   canonical record can be instantiated with the site's metavariables. *)
let parameterize_anonymous_record_fields fields =
  let parameters = ref [] in
  let arguments = ref [] in
  let next_unresolved = ref 0 in
  let add name argument =
    if not (List.mem name !parameters) then (
      parameters := !parameters @ [ name ];
      arguments := !arguments @ [ argument ])
  in
  let rec parameterize = function
    | TUnknown as ty ->
        incr next_unresolved;
        let name = "u" ^ string_of_int !next_unresolved in
        add name ty;
        TVar name
    | TNil as ty ->
        incr next_unresolved;
        let name = "u" ^ string_of_int !next_unresolved in
        add name ty;
        TNullable (TVar name)
    | TMeta meta as ty ->
        let name = "m" ^ string_of_int meta.id in
        add name ty;
        TVar name
    | TVar name as ty -> add name ty; TVar name
    | ty -> Semantic_type.map_children parameterize ty
  in
  let fields =
    List.map
      (fun (field : field) -> { field with ty = parameterize field.ty })
      fields
  in
  (fields, !parameters, !arguments)

(* Structural records are content-addressed: a site whose field shape matches
   an already-allocated anonymous record reuses that nominal OCaml type
   instead of minting another `tN`. The oldest match is preferred so the
   declaration always precedes every use site. *)
let find_canonical_anonymous_record fields env =
  let canonical = Env.canonical_anonymous_fields fields in
  env.Compiler_environment.anonymous_records
  |> List.filter_map (fun (_, (record : Semantic_type.named_record)) ->
         if
           Env.anonymous_fields_equal canonical
             (Env.canonical_anonymous_fields record.fields)
         then Some record
         else None)
  |> Env.oldest_candidate

let allocate_anonymous_record ~owner env next_type fields =
  let owner = Source_context.anonymous_record_owner owner in
  let fields, type_parameters, site_arguments =
    parameterize_anonymous_record_fields fields
  in
  match find_canonical_anonymous_record fields env with
  | Some record ->
      {
        record = { record with type_arguments = site_arguments };
        env;
        next_type;
        fresh = false;
      }
  | None ->
      let type_name = "t" ^ string_of_int next_type in
      let set_module_name = "Set_" ^ type_name in
      let type_id =
        Type_id.create
          ~owner:(if String.equal owner "" then [] else [ owner ])
          ~name:type_name
      in
      let record =
        match
          Types.named_record ~type_id ~extensible:true ~type_name
            ~set_module_name ~type_parameters fields
        with
        | TNamed_record record -> record
        | _ -> assert false
      in
      {
        record;
        env = Env.add_anonymous_record ~owner record env;
        next_type = next_type + 1;
        fresh = true;
      }

type nested_record_allocation = {
  nested_fields : field list;
  env : Env.t;
  next_type : int;
  items : compiled_item list;
}

let allocate_nested_anonymous_records ~owner env next_type fields =
  let rec allocate_type env next_type items = function
    | TPoly_variant row ->
        let tags, env, next_type, items = List.fold_left
          (fun (tags, env, next_type, items) (tag, payload) ->
            match payload with
            | None -> ((tag, None) :: tags, env, next_type, items)
            | Some ty ->
                let ty, env, next_type, items = allocate_type env next_type items ty in
                ((tag, Some ty) :: tags, env, next_type, items))
          ([], env, next_type, items) row.tags in
        (TPoly_variant {row with tags = List.rev tags}, env, next_type, items)
    | TRecord fields when Types.is_homogeneous_record fields ->
        let allocated = allocate_fields env next_type items fields in
        ( TRecord allocated.nested_fields,
          allocated.env,
          allocated.next_type,
          allocated.items )
    | TRecord fields ->
        let allocated = allocate_fields env next_type items fields in
        let record =
          allocate_anonymous_record ~owner allocated.env allocated.next_type
            allocated.nested_fields
        in
        let items =
          if record.fresh then
            allocated.items
            @ [
                Type_def
                  {
                    type_id = record.record.type_id;
                    type_name = record.record.type_name;
                    type_parameters = record.record.type_parameters;
                    fields = record.record.fields;
                    nominal = false;
                    location = None;
                  };
              ]
          else allocated.items
        in
        (TNamed_record record.record, record.env, record.next_type, items)
    | TNullable inner ->
        map_inner env next_type items (fun inner -> TNullable inner) inner
    | TOcaml_app (name, arguments) ->
        let arguments, env, next_type, items =
          allocate_types env next_type items arguments
        in
        (TOcaml_app (name, arguments), env, next_type, items)
    | TConstraint constraint_ ->
        allocate_constraint env next_type items constraint_
    | TTuple arguments ->
        let arguments, env, next_type, items =
          allocate_types env next_type items arguments
        in
        (TTuple arguments, env, next_type, items)
    | TArray inner ->
        map_inner env next_type items (fun inner -> TArray inner) inner
    | TRef inner ->
        map_inner env next_type items (fun inner -> TRef inner) inner
    | TList inner ->
        map_inner env next_type items (fun inner -> TList inner) inner
    | TVector inner ->
        map_inner env next_type items (fun inner -> TVector inner) inner
    | TSet inner ->
        map_inner env next_type items (fun inner -> TSet inner) inner
    | TSeq inner ->
        map_inner env next_type items (fun inner -> TSeq inner) inner
    | TFn (parameters, return_type) ->
        let parameters, env, next_type, items =
          allocate_types env next_type items parameters
        in
        let return_type, env, next_type, items =
          allocate_type env next_type items return_type
        in
        (TFn (parameters, return_type), env, next_type, items)
    | TOverloaded_fn arities ->
        let rec allocate_arities env next_type items allocated = function
          | [] -> (TOverloaded_fn (List.rev allocated), env, next_type, items)
          | arity :: rest ->
              let fixed_params, env, next_type, items =
                allocate_types env next_type items arity.fixed_params
              in
              let rest_param, env, next_type, items =
                match arity.rest_param with
                | None -> (None, env, next_type, items)
                | Some rest_param ->
                    let rest_param, env, next_type, items =
                      allocate_type env next_type items rest_param
                    in
                    (Some rest_param, env, next_type, items)
              in
              let return_ty, env, next_type, items =
                allocate_type env next_type items arity.return_ty
              in
              allocate_arities env next_type items
                ({ fixed_params; rest_param; return_ty } :: allocated)
                rest
        in
        allocate_arities env next_type items [] arities
    | ( TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _
      | TNamed_record _ ) as ty ->
        (ty, env, next_type, items)
  and map_inner env next_type items wrap inner =
    let inner, env, next_type, items =
      allocate_type env next_type items inner
    in
    (wrap inner, env, next_type, items)
  and allocate_types env next_type items types =
    let rec loop env next_type items allocated = function
      | [] -> (List.rev allocated, env, next_type, items)
      | ty :: rest ->
          let ty, env, next_type, items =
            allocate_type env next_type items ty
          in
          loop env next_type items (ty :: allocated) rest
    in
    loop env next_type items [] types
  and allocate_constraint env next_type items constraint_ =
    let map_one build value =
      map_inner env next_type items (fun value -> TConstraint (build value)) value
    in
    let map_two build left right =
      let values, env, next_type, items =
        allocate_types env next_type items [ left; right ]
      in
      match values with
      | [ left; right ] -> (TConstraint (build left right), env, next_type, items)
      | _ -> (TConstraint constraint_, env, next_type, items)
    in
    match constraint_ with
    | Seqable_constraint ({ element; storage; _ } as seqable) ->
        map_two
          (fun element storage ->
            Seqable_constraint { seqable with element; storage })
          element storage
    | Contains_constraint { key; storage } ->
        map_two (fun key storage -> Contains_constraint { key; storage }) key
          storage
    | Truthy_constraint value -> map_one (fun value -> Truthy_constraint value) value
    | Nil_predicate_constraint value ->
        map_one (fun value -> Nil_predicate_constraint value) value
    | Printable_constraint value ->
        map_one (fun value -> Printable_constraint value) value
    | Exception_data_constraint value ->
        map_one (fun value -> Exception_data_constraint value) value
    | Hashable_constraint value ->
        map_one (fun value -> Hashable_constraint value) value
    | Comparable_constraint value ->
        map_one (fun value -> Comparable_constraint value) value
    | Array_index_constraint value ->
        map_one (fun value -> Array_index_constraint value) value
    | Symbol_predicate_constraint value ->
        map_one (fun value -> Symbol_predicate_constraint value) value
    | Open_boundary_constraint value ->
        map_one (fun value -> Open_boundary_constraint value) value
    | Protocol_constraint ({ witness; value; _ } as protocol) ->
        map_two
          (fun witness value ->
            Protocol_constraint { protocol with witness; value })
          witness value
  and allocate_fields env next_type items fields =
    let rec loop env next_type items allocated = function
      | [] -> { nested_fields = List.rev allocated; env; next_type; items }
      | (field : field) :: rest ->
          let ty, env, next_type, items =
            allocate_type env next_type items field.ty
          in
          loop env next_type items ({ field with ty } :: allocated) rest
    in
    loop env next_type items [] fields
  in
  allocate_fields env next_type [] fields

let check_emitted_name_collision = Resolver.check_emitted_name_collision

let binding_value_expression (binding : Types.binding) =
  let rec overloaded_value = function
    | [] -> Semantic_ir.Unit
    | target :: rest ->
        Semantic_ir.Tuple
          [ Semantic_ir.Ident target; overloaded_value rest ]
  in
  match binding.ty with
  | TOverloaded_fn arities
    when List.length binding.overload_targets = List.length arities ->
      overloaded_value binding.overload_targets
  | _ when binding.multimethod ->
      Semantic_ir.Apply
        (Semantic_ir.Ident "snd", [ Semantic_ir.Ident binding.ocaml_name ])
  | _ -> Semantic_ir.Ident binding.ocaml_name

let binding_runtime_value (binding : Types.binding) =
  match (binding.dynamically_bindable, Types.runtime_root_value_type binding) with
  | true, Some value_ty ->
      typed_ir value_ty
        (Semantic_ir.Apply
           ( Semantic_ir.Ident "Lg_runtime.Runtime_reference.deref",
             [ Semantic_ir.Ident binding.ocaml_name ] ))
  | _ -> typed_ir binding.ty (binding_value_expression binding)

let untyped_first_class_collection_function_error name =
  name
  ^ " cannot be used as an untyped first-class function; define a statically \
     typed wrapper"

let untyped_first_class_function_error = function
  | ( "!="
    | "abs"
    | "array-value?"
    | "array?"
    | "array-map"
    | "assoc"
    | "char?"
    | "contains?"
    | "count"
    | "dissoc"
    | "false?"
    | "hash-map"
    | "identical?"
    | "keyword?"
    | "list"
    | "neg?"
    | "nil?"
    | "number?"
    | "pos?"
    | "re-find"
    | "re-matches"
    | "re-pattern"
    | "re-seq"
    | "reduced?"
    | "set"
    | "string?"
    | "symbol?"
    | "true?"
    | "vec"
    | "vector"
    | "zero?" ) as name ->
      Some (untyped_first_class_collection_function_error name)
  | ("clojure.core/dissoc" | "cljs.core/dissoc") as name ->
      let separator = String.rindex name '/' in
      let basename =
        String.sub name (separator + 1) (String.length name - separator - 1)
      in
      Some (untyped_first_class_collection_function_error basename)
  | ("resolve" | "requiring-resolve") as name ->
      Some
        (name
        ^ " cannot be used without a closed result type; define a closed sum \
           type containing the supported Vars")
  | _ -> None

let rec clj_function_type = function
  | TFn ([ TUnit ], return_ty) -> TFn ([], clj_function_type return_ty)
  | TFn (parameters, return_ty) ->
      TFn (List.map clj_function_type parameters, clj_function_type return_ty)
  | ty -> ty

let lookup_function scope env name =
  match lookup_binding scope env name with
  | Ok binding ->
      Ok (binding_runtime_value binding)
  | Error _ -> (
      match untyped_first_class_function_error name with
      | Some message -> Error.error message
      | None -> (
          match Resolver.ocaml_call_target scope env name with
          | Some target -> (
              match Ocaml_signature.value_signature target with
              | Ok { parameters = []; return_type; _ }
                when not (Types.equal return_type TUnknown) ->
                  Ok (typed_ir return_type (Semantic_ir.Ident target))
              | Ok { parameters; return_type }
                when parameters <> [] && List.for_all
                       (fun (parameter : Ocaml_signature.parameter) ->
                         parameter.label = Ocaml_signature.Positional)
                       parameters ->
                  let ty =
                    TFn (List.map (fun (parameter : Ocaml_signature.parameter) -> parameter.ty) parameters,
                         return_type)
                    |> clj_function_type
                  in
                  Ok (typed_ir ty (Semantic_ir.Ident target))
              | Ok _ | Error _ -> Error.error ("unknown function " ^ name))
          | None -> Error.error ("unknown function " ^ name)))

let record_constructor_type scope env name =
  if String.ends_with ~suffix:"." name then
    let type_name = String.sub name 0 (String.length name - 1) in
    match Resolver.lookup_record_type scope env type_name with
    | Ok record ->
        Some
          (TFn
             ( List.map (fun (field : field) -> field.ty) record.fields,
               TNamed_record record ))
    | Error _ -> None
  else None

let map_record_constructor_type_name name =
  let owner, basename =
    match String.rindex_opt name '/' with
    | None -> ("", name)
    | Some index ->
        ( String.sub name 0 (index + 1),
          String.sub name (index + 1) (String.length name - index - 1) )
  in
  if String.starts_with ~prefix:"map->" basename then
    Some
      (owner ^ String.sub basename 5 (String.length basename - 5))
  else None

let map_record_constructor_type scope env name =
  match map_record_constructor_type_name name with
  | Some type_name -> (
      match Resolver.lookup_record_type scope env type_name with
      | Ok record ->
          Some (TFn ([ TRecord record.fields ], TNamed_record record))
      | Error _ -> None)
  | None -> None

let named_records_in_scope env =
  let registered_records =
    Type_registry.bindings (Env.types env)
    |> List.filter_map
         (fun (_, (declaration : Type_registry.declaration)) ->
           match declaration.kind with
           | Type_registry.Record ->
               let scope =
                 Type_id.owner declaration.type_id |> String.concat "."
               in
               let key =
                 Resolver.record_type_key scope
                   (Type_id.name declaration.type_id)
               in
               (match Env.find_opt key env with
               | Some { ty = TNamed_record record; _ } -> Some record
               | Some _ | None -> None)
           | Type_registry.Alias | Type_registry.Variant | Type_registry.Opaque -> None)
  in
  if registered_records <> [] then registered_records
  else
    Env.filter_record_bindings
      (fun key (binding : binding) ->
        if String.starts_with ~prefix:"__record/" key then
          match binding.ty with
          | TNamed_record record -> Some record
          | _ -> None
        else None)
      env

(* A keyword read `(:key x)` on an open target resolves the field's declared
   type via the unique named record declaring that field. When several
   records share the field, a candidate named after the binding being read
   (e.g. `session` for `:host`) wins; otherwise the read stays a row
   constraint rather than committing to an arbitrary record. *)
(* A unique keyword -> record match is only safe when the record is actually
   visible to the module being inferred: corpus and namespace compilation share
   one environment, so records from unrequired sibling modules must not
   speculate. Host package records stay visible because they resolve through
   implicit module paths rather than namespace aliases. *)
let record_visible_in_scope ~scope env (record : named_record) =
  match Type_id.owner record.type_id with
  | [] -> true
  | [ owner ] ->
      String.equal owner scope
      || String.starts_with ~prefix:"ocaml." owner
      || Option.is_some (Env.resolve_namespace_alias ~scope owner env)
      || List.exists
           (fun target -> String.equal target owner)
           (Env.namespace_alias_targets ~scope env)
  | _ -> true

let record_type_for_keyword ~scope env keyword preferred_name =
  let candidates =
    named_records_in_scope env
    |> List.filter (record_visible_in_scope ~scope env)
    |> List.filter_map (fun (record : named_record) ->
           match Types.find_field keyword record.fields with
           | Some field
             when not (Types.is_record_extension_field field) ->
               Some record
           | Some _ | None -> None)
    |> List.sort_uniq (fun left right ->
           Type_id.compare left.type_id right.type_id)
  in
  match candidates with
  | [ record ] -> Some (TNamed_record record)
  | [] -> None
  | _ :: _ :: _ ->
      candidates
      |> List.find_opt (fun (record : named_record) ->
             String.equal record.type_name preferred_name
             || String.equal (Type_id.name record.type_id) preferred_name)
      |> Option.map (fun record -> TNamed_record record)

let dynamic_key_record_type env expected_field_ty =
  let expected_field_ty =
    match Types.dynamic_constraint_info expected_field_ty with
    | Some capability when not (Types.equal capability TUnknown) -> capability
    | Some _ | None -> expected_field_ty
  in
  let expected_field_ty = Types.constraint_value_type expected_field_ty in
  let named_records = named_records_in_scope env in
  let record_index =
    let add name record index =
      String_map.update name
        (fun records -> Some (record :: Option.value ~default:[] records))
        index
    in
    List.fold_left
      (fun index record ->
        let index = add record.type_name record index in
        let id_name = Type_id.name record.type_id in
        if id_name = record.type_name then index else add id_name record index)
      String_map.empty named_records
  in
  let resolve_named_application = function
    | TOcaml_app (name, arguments) as ty ->
        let records =
          String_map.find_opt name record_index
          |> Option.value ~default:[]
          |> List.filter_map (fun record ->
                 if
                   List.length record.type_parameters = List.length arguments
                 then
                  let substitutions =
                    List.combine record.type_parameters arguments
                    |> List.filter (fun (parameter, argument) ->
                           argument <> TVar parameter)
                    |> List.map (fun (parameter, argument) ->
                           (Type_solver.Declared parameter, argument))
                    |> Type_solver.of_list
                  in
                  Some
                    (Types.substitute_type_variables substitutions
                       (TNamed_record record))
                 else None)
        in
        (match records with [ record ] -> record | [] | _ :: _ :: _ -> ty)
    | ty -> ty
  in
  let rec same_outer_shape expected actual =
    let expected = resolve_named_application expected in
    let actual = resolve_named_application actual in
    match (expected, actual) with
    | TNamed_record expected, TNamed_record actual ->
        Type_id.equal expected.type_id actual.type_id
    | TNamed_record record, TOcaml_app (name, arguments)
    | TOcaml_app (name, arguments), TNamed_record record ->
        (name = record.type_name || name = Type_id.name record.type_id)
        && List.length arguments = List.length record.type_parameters
    | TArray expected, TArray actual
    | TList expected, TList actual
    | TVector expected, TVector actual
    | TSet expected, TSet actual
    | TSeq expected, TSeq actual
    | TRef expected, TRef actual
    | TNullable expected, TNullable actual ->
        same_outer_shape expected actual
    | TOcaml_app (expected_name, expected_args),
      TOcaml_app (actual_name, actual_args)
      when expected_name = actual_name
           && List.length expected_args = List.length actual_args ->
        List.for_all2 same_outer_shape expected_args actual_args
    | TRecord expected, TNamed_record actual ->
        record_shape expected actual.fields
    | TNamed_record expected, TRecord actual ->
        record_shape expected.fields actual
    | TRecord expected, TRecord actual -> record_shape expected actual
    | TUnknown, _ | TVar _, _ | _, TUnknown | _, TVar _ -> true
    | expected, actual -> Types.equal expected actual
  and record_shape expected actual =
    List.for_all
      (fun (expected : field) ->
        match Types.find_field expected.keyword actual with
        | Some actual -> same_outer_shape expected.ty actual.ty
        | None -> false)
      expected
  in
  let compatible_fields (record : named_record) =
    record.fields
    |> List.filter (fun (field : field) ->
           (not (Types.is_record_extension_field field))
           && same_outer_shape expected_field_ty field.ty)
  in
  let specialize_record (record : named_record) =
    match compatible_fields record with
    | [] -> None
    | (first : field) :: rest -> (
        let first_ty = resolve_named_application first.ty in
        let substitutions =
          rest
          |> List.fold_left
               (fun substitutions (field : field) ->
                 Result.bind substitutions (fun substitutions ->
                     Type_solver.unify substitutions first_ty
                       (resolve_named_application field.ty)))
               (Ok Type_solver.empty)
        in
        let substitutions =
          Result.bind substitutions (fun substitutions ->
              Type_solver.unify substitutions first_ty
                (resolve_named_application expected_field_ty))
        in
        match substitutions with
        | Ok substitutions -> (
            match Type_solver.apply substitutions (TNamed_record record) with
            | TNamed_record record -> Some record
            | _ -> None)
        | Error _ -> None)
  in
  let records =
    named_records
    |> List.filter_map (fun record ->
           if List.length (compatible_fields record) >= 2 then
             specialize_record record
           else None)
      |> List.sort_uniq (fun left right ->
           Type_id.compare left.type_id right.type_id)
  in
    match records with
    | [ record ] -> Some (TNamed_record record)
  | [] | _ :: _ :: _ -> None

let lookup_function_ty scope env name =
  let ocaml_function_type target =
    match Ocaml_signature.value_signature target with
    | Ok signature ->
        let parameters =
          List.map
            (fun (parameter : Ocaml_signature.parameter) ->
              clj_function_type parameter.ty)
            signature.parameters
        in
        let parameters =
          match parameters with [ TUnit ] -> [] | _ -> parameters
        in
        Ok (TFn (parameters, clj_function_type signature.return_type))
    | Error _ -> (
        match Ocaml_signature.constructor_signature target with
        | Ok signature ->
            Ok (TFn (signature.payload_types, signature.result_type))
        | Error _ as error -> error)
  in
  let precise_ocaml_binding () =
    Option.bind (Resolver.ocaml_call_target scope env name) (fun target ->
        match ocaml_function_type target with
        | Ok ty -> Some ty
        | Error _ -> None)
  in
  match lookup_function scope env name with
  | Ok fn
    when Types.is_dynamic fn.ty
         || Types.contains_dynamic fn.ty
         || Types.equal fn.ty TUnknown -> (
      match precise_ocaml_binding () with
      | Some ty -> Ok ty
      | None -> Ok fn.ty)
  | Ok fn -> Ok fn.ty
  | Error original_error -> (
      match Resolver.ocaml_call_target scope env name with
      | Some target -> (
          match ocaml_function_type target with
          | Ok ty -> Ok ty
          | Error _ -> Error original_error)
      | None ->
      match record_constructor_type scope env name with
      | Some ty -> Ok ty
      | None -> (
          match map_record_constructor_type scope env name with
          | Some ty -> Ok ty
          | None -> (
              match Protocol.lookup_marker scope env name with
              | Some
                  {
                    protocol_id = Some _;
                    ty = TFn (receiver_ty :: rest, return_ty);
                    _;
                  } ->
                  Ok (TFn (receiver_ty :: rest, return_ty))
              | Some marker -> Ok marker.ty
              | None
                when is_constructor_name name
                     && not (List.mem name [ "Some"; "None"; "Ok"; "Error" ]) ->
                  let candidates =
                    Env.bindings_named name env
                    |> List.filter_map (fun (binding : binding) ->
                           match binding.ty with
                           | TFn (_, (TOcaml _ | TOcaml_app _)) ->
                               Some binding.ty
                           | _ -> None)
                    |> List.sort_uniq Stdlib.compare
                  in
                  (match candidates with
                  | [ constructor_ty ] -> Ok constructor_ty
                  | [] ->
                      let constructor_name =
                        Resolver.resolve_ocaml_constructor_target scope env name
                      in
                      (match
                         Ocaml_signature.constructor_signature constructor_name
                       with
                      | Ok signature ->
                          Ok
                            (TFn
                               ( signature.payload_types,
                                 signature.result_type ))
                      | Error _ -> Error.error ("unknown function " ^ name))
                  | _ :: _ :: _ -> Error.error ("ambiguous constructor " ^ name))
              | None -> Error.error ("unknown function " ^ name))))

let lookup_call_ty scope env name forms =
  let source_binding_shadows_call_target =
    match Env.find_opt (Names.scoped_key scope name) env with
    | Some { host_reference = None; _ } -> true
    | Some _ | None -> false
  in
  if source_binding_shadows_call_target then None
  else Option.bind (Resolver.ocaml_call_target scope env name) (fun target ->
      match
        (Ocaml_signature.value_signature target,
         Ocaml_signature.parse_argument_forms forms)
      with
      | Ok signature, Ok arguments ->
          Option.bind
            (Ocaml_signature.expected_argument_types signature arguments)
            (fun expected ->
              let labelled_types =
                List.map2 (fun (label, _) ty -> (label, ty)) arguments expected
              in
              match Ocaml_signature.result_after_application signature labelled_types with
              | Error _ -> None
              | Ok return_ty ->
                  (* Labels occupy source forms, but never consume positional parameters. *)
                  let parameter_tys =
                    List.concat_map
                      (fun (label, ty) ->
                        match label with
                        | None -> [clj_function_type ty]
                        | Some _ -> [TKeyword; clj_function_type ty])
                      labelled_types
                  in
                  Some (TFn (parameter_tys, clj_function_type return_ty)))
      | _ -> None)

let ocaml_call_target = Resolver.ocaml_call_target
let resolve_ocaml_call_target = Resolver.resolve_ocaml_call_target
let resolve_ocaml_constructor_target = Resolver.resolve_ocaml_constructor_target

let inherit_scope_ocaml_value_refers scope module_path env =
  let prefix = scope ^ "/" in
  let prefix_len = String.length prefix in
  let inherited =
    Env.namespace_binding_entries scope env
    |> List.filter_map
      (fun (key, (binding : binding)) ->
           match binding.host_reference with
        | Some (Ocaml_value _)
          when String.length key > prefix_len
               && String.sub key 0 prefix_len = prefix ->
               let name =
                 String.sub key prefix_len (String.length key - prefix_len)
               in
               Some (Names.scoped_key module_path name, binding)
        | _ -> None)
  in
  Env.add_bindings inherited env

type compiled_fn_parts = {
  param_bindings : (string * binding) list;
  param_identities : (Source_node_id.t * Location.t) option list;
  destructured_bindings : Destructure.local_binding list;
  return_param_index_hint : int option;
  body : typed_expr;
}

let parameterize_row_fields fields =
  let next_parameter = ref 0 in
  let named_parameters = ref [] in
  let parameters = ref [] in
  let fresh_parameter () =
    let parameter = "a" ^ string_of_int !next_parameter in
    incr next_parameter;
    parameters := parameter :: !parameters;
    parameter
  in
  let named_parameter name =
    match List.assoc_opt name !named_parameters with
    | Some parameter -> parameter
    | None ->
        let parameter = fresh_parameter () in
        named_parameters := (name, parameter) :: !named_parameters;
        parameter
  in
  let rec parameterize = function
    | TPoly_variant _ as ty -> Semantic_type.map_children parameterize ty
    | TUnknown | TMeta _ -> TVar (fresh_parameter ())
    | TVar name -> TVar (named_parameter name)
    | TNullable ty -> TNullable (parameterize ty)
    | TOcaml_app (name, arguments) ->
        TOcaml_app (name, List.map parameterize arguments)
    | TConstraint constraint_ ->
        TConstraint (map_constraint parameterize constraint_)
    | TTuple items -> TTuple (List.map parameterize items)
    | TArray ty -> TArray (parameterize ty)
    | TRef ty -> TRef (parameterize ty)
    | TList ty -> TList (parameterize ty)
    | TVector ty -> TVector (parameterize ty)
    | TSet ty -> TSet (parameterize ty)
    | TSeq ty -> TSeq (parameterize ty)
    | TFn (parameters, return_type) ->
        TFn (List.map parameterize parameters, parameterize return_type)
    | TOverloaded_fn arities ->
        TOverloaded_fn
          (List.map
             (fun (arity : fn_arity) ->
               { fixed_params = List.map parameterize arity.fixed_params;
                 rest_param = Option.map parameterize arity.rest_param;
                 return_ty = parameterize arity.return_ty })
             arities)
    | TRecord _ -> TVar (fresh_parameter ())
    | TNamed_record record ->
        TNamed_record
          {
            record with
            type_parameters =
              List.map named_parameter record.type_parameters;
            type_arguments = List.map parameterize record.type_arguments;
            fields = List.map parameterize_field record.fields;
          }
    | TNil -> TNullable (TVar (fresh_parameter ()))
    | (TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TOcaml _) as ty ->
        ty
  and parameterize_field (field : field) =
    { field with ty = parameterize field.ty }
  in
  let fields = List.map parameterize_field fields in
  (fields, List.rev !parameters)

let direct_row_fields ?(allow_nullable = false) = function
  | TRecord fields when not (Types.is_homogeneous_record fields) -> Some fields
  | TNullable (TRecord fields) | TOcaml_app ("option", [ TRecord fields ])
    when allow_nullable && not (Types.is_homogeneous_record fields) ->
      Some fields
  | _ -> None

let tuple_row_fields = function
  | TRecord fields | TNamed_record { fields; nominal = false; _ } -> Some fields
  | _ -> None

let row_param_fields ?(allow_nullable = false) = function
  | ty when Option.is_some (direct_row_fields ~allow_nullable ty) ->
      direct_row_fields ~allow_nullable ty
  | ty when Option.is_some (Types.contains_constraint_info ty) ->
      let _, value_ty = Types.contains_constraint_info ty |> Option.get in
      direct_row_fields ~allow_nullable value_ty
  | TConstraint (Seqable_constraint { element = element_ty; _ }) ->
      (match direct_row_fields ~allow_nullable element_ty with
      | Some _ as fields -> fields
      | None -> (
          match element_ty with
          | TTuple items ->
              items
              |> List.filter_map tuple_row_fields
              |> (function
                   | [ fields ] -> Some fields
                   | [] | _ :: _ :: _ -> None)
          | _ -> None))
  | _ -> None

(* A parameter whose row position is already occupied by a named record type:
   reusing that type's application keeps the emitted signature identical to the
   stored one instead of minting a duplicate <fn>_row<N> declaration. *)
let named_row_record param_ty =
  (* Only nominal records have a declaration that is guaranteed to be
     emitted; reusing an anonymous record's application would leave the
     parameter referencing a type that may never be declared. *)
  let tuple_record = function
    | TNamed_record ({ nominal = true; _ } as record) -> Some record
    | _ -> None
  in
  match param_ty with
  | TConstraint (Seqable_constraint { element = element_ty; _ }) -> (
      match element_ty with
      | TNamed_record ({ nominal = true; _ } as record) -> Some record
      | TTuple items -> (
          match List.filter_map tuple_record items with
          | [ record ] -> Some record
          | [] | _ :: _ :: _ -> None)
      | _ -> None)
  | _ -> None

(* When a parameter's row type uniquely matches a declared named record, bind
   it as that record: assoc and other whole-record operations then emit
   nominal-typed OCaml instead of anonymous record literals that OCaml cannot
   resolve to the intended type. Host type aliases (e.g. Datascript.attr =
   string) are expanded before comparing field types. *)
let canonical_row_named_record env fields =
  let rec expand_host_aliases ty =
    let ty = Semantic_type.map_children expand_host_aliases ty in
    match ty with
    | TOcaml name | TOcaml_app (name, []) -> (
        match Ocaml_signature.transparent_manifest_alias name with
        | Some manifest when not (Types.equal manifest ty) ->
            expand_host_aliases manifest
        | _ -> ty)
    | _ -> ty
  in
  let expected_fields =
    List.map
      (fun (field : field) -> { field with ty = expand_host_aliases field.ty })
      fields
  in
  let candidates =
    named_records_in_scope env
    |> List.filter_map (fun (record : named_record) ->
           let actual_fields =
             List.map
               (fun (field : field) ->
                 { field with ty = expand_host_aliases field.ty })
               record.fields
           in
           if
             Types.row_compatible ~expected:(TRecord expected_fields)
               ~actual:(TRecord actual_fields)
           then Some record
           else None)
  in
  match candidates with
  | [ record ] -> Some record
  | _ -> None

let row_param_type_names ?env ?(nullable_row_indices = []) prefix param_tys =
  let has_named_candidate fields =
    match env with
    | None -> false
    | Some env ->
        Env.filter_record_bindings
          (fun key (binding : binding) ->
            if String.starts_with ~prefix:"__record/" key then
              match binding.ty with
              | TNamed_record record
                when Types.row_compatible ~expected:(TRecord fields)
                       ~actual:(TNamed_record record) ->
                  Some ()
              | _ -> None
            else None)
          env
        <> []
  in
  param_tys
  |> List.mapi (fun index param_ty ->
       let named_constraint_row =
         match Types.contains_constraint_info param_ty with
         | Some (_, TNamed_record record) ->
             Some (Structural_map.record_type_application record)
         | Some _ | None -> (
             match named_row_record param_ty with
             | Some record ->
                 Some (Structural_map.record_type_application record)
             | None -> None)
       in
       let nullable_fields =
         match param_ty with
         | TNullable (TRecord fields)
         | TOcaml_app ("option", [ TRecord fields ]) ->
             Some fields
         | _ -> None
       in
       let unresolved_nullable_row =
         Option.fold ~none:false
           ~some:(fun fields -> not (has_named_candidate fields))
           nullable_fields
       in
       match named_constraint_row with
       | Some type_name -> Some type_name
       | None -> (
       match
         row_param_fields
           ~allow_nullable:
             (unresolved_nullable_row || List.mem index nullable_row_indices)
           param_ty
       with
       | Some fields ->
           let type_name = prefix ^ "_row" ^ string_of_int index in
           let _, parameters =
             parameterize_row_fields fields
           in
           (* Application arguments must be distinct across a function's
              parameters: OCaml unifies same-named type variables in one
              signature, so reusing 'a0 in two row applications would
              collapse unrelated metas. *)
           let parameters =
             List.map (fun name -> "'a" ^ string_of_int index ^ "_" ^ name)
               parameters
           in
           let applied_name =
             match parameters with
             | [] -> type_name
             | [ parameter ] -> parameter ^ " " ^ type_name
          | parameters -> "(" ^ String.concat ", " parameters ^ ") " ^ type_name
           in
           Some applied_name
       | None -> None))

let row_type_items row_type_names param_tys =
  List.map2
    (fun row_type_name param_ty ->
      match named_row_record param_ty with
      | Some _ -> None
      | None -> (
      match (row_type_name, row_param_fields ~allow_nullable:true param_ty) with
      | Some applied_name, Some fields ->
          let type_name =
            match String.rindex_opt applied_name ' ' with
            | None -> applied_name
            | Some index ->
                String.sub applied_name (index + 1)
                  (String.length applied_name - index - 1)
          in
          let fields, type_parameters =
            parameterize_row_fields fields
          in
          Some
            (Type_def
               {
                 type_id = Types.type_id_of_name type_name;
                 type_name;
                 type_parameters;
                 fields;
                 nominal = false;
                 location = None;
               })
      | _ -> None))
    row_type_names param_tys
  |> List.filter_map Fun.id

let row_call_type_name type_name =
  let length = String.length type_name in
  let buffer = Buffer.create length in
  let is_type_variable_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' -> true
    | _ -> false
  in
  let rec copy index =
    if index < length then
      if type_name.[index] = '\'' then (
        Buffer.add_char buffer '_';
        skip_variable (index + 1))
      else (
        Buffer.add_char buffer type_name.[index];
        copy (index + 1))
  and skip_variable index =
    if index < length && is_type_variable_char type_name.[index] then
      skip_variable (index + 1)
    else copy index
  in
  copy 0;
  Buffer.contents buffer

let row_project_expr type_name fields arg =
  let type_name = row_call_type_name type_name in
  let source = "__row_source" in
  Semantic_ir.Let
    ( [ (Semantic_ir.PVar source, arg.semantic_expr) ],
      Semantic_ir.Record
        ( List.map
            (fun (field : field) ->
              ( field.ocaml_name,
                Semantic_ir.Field (Semantic_ir.Ident source, field.ocaml_name)
              ))
            fields,
          Some type_name ) )

let row_arg_expr row_type_name expected_ty arg =
  match (row_type_name, expected_ty, arg.ty) with
  | Some type_name, TRecord fields, (TRecord _ | TNamed_record _) ->
      row_project_expr type_name fields arg
  | _ -> arg.semantic_expr

let coerce_set_element element_ty value =
  let rec coerce_closed expected actual expression =
    let metadata name argument =
      Semantic_ir.Apply
        ( Semantic_ir.Ident ("Lg_runtime.Runtime_metadata." ^ name),
          [ argument ] )
    in
    match (expected, actual) with
    | expected, actual when Types.equal expected actual -> Ok expression
    | TOcaml "Lg_edn_backend.t", TNil ->
        Ok
          (Semantic_ir.Sequence
             [ expression; Semantic_ir.Ident "Lg_runtime.Runtime_metadata.nil" ])
    | TOcaml "Lg_edn_backend.t", TBool -> Ok (metadata "of_bool" expression)
    | TOcaml "Lg_edn_backend.t", (TInt | TOcaml "int") ->
        Ok (metadata "of_int" expression)
    | TOcaml "Lg_edn_backend.t", TFloat -> Ok (metadata "of_float" expression)
    | TOcaml "Lg_edn_backend.t", TChar -> Ok (metadata "of_char" expression)
    | TOcaml "Lg_edn_backend.t", TString -> Ok (metadata "of_string" expression)
    | TOcaml "Lg_edn_backend.t", TSymbol -> Ok (metadata "of_symbol" expression)
    | TOcaml "Lg_edn_backend.t", TKeyword ->
        Ok (metadata "of_keyword" expression)
    | TOcaml "Lg_edn_backend.t", TRegex -> Ok (metadata "of_regex" expression)
    | TVector expected_item, TTuple actual_items ->
        let names =
          List.mapi
            (fun index _ -> "__lg_set_tuple_item_" ^ string_of_int index)
            actual_items
        in
        let pattern_names = names in
        let rec coerce_tuple_items acc types names =
          match (types, names) with
          | [], [] ->
              Ok
                (Semantic_ir.Let
                   ( [
                       ( Semantic_ir.PTuple
                           (List.map
                              (fun name -> Semantic_ir.PVar name)
                              pattern_names),
                         expression );
                     ],
                     Semantic_ir.Apply
                       ( Semantic_ir.Ident "Rrbvec.of_list",
                         [ Semantic_ir.List (List.rev acc) ] ) ))
          | actual_item :: rest, name :: rest_names ->
              Result.bind
                (coerce_closed expected_item actual_item
                   (Semantic_ir.Ident name))
                (fun item ->
                  coerce_tuple_items (item :: acc) rest rest_names)
          | _ -> assert false
        in
        coerce_tuple_items [] actual_items names
    | TVector expected_item, TVector actual_item ->
        let item_name = "__lg_set_vector_item" in
        Result.map
          (fun item ->
            Semantic_ir.Apply
              ( Semantic_ir.Ident "Rrbvec.map",
                [
                  Semantic_ir.Fun ([ Semantic_ir.PVar item_name ], item);
                  expression;
                ] ))
          (coerce_closed expected_item actual_item (Semantic_ir.Ident item_name))
    | _ ->
        Error.error
          ("set value type must match element type: expected "
         ^ Types.source_name expected ^ ", got " ^ Types.source_name actual)
  in
  match element_ty with
  | TNamed_record expected -> (
      match value.ty with
      | TNamed_record actual when actual.type_name = expected.type_name ->
          Ok value.semantic_expr
      | (TRecord actual_fields | TNamed_record { fields = actual_fields; _ })
        when Types.assignable ~policy:Structural ~expected:element_ty
               ~actual:value.ty ->
          let rec project_fields acc = function
            | [] -> Ok (List.rev acc)
            | (field : field) :: rest -> (
                match find_field field.keyword actual_fields with
                | None -> Error.error "set record coercion is missing a field"
                | Some actual_field ->
                    project_fields
                      (( field.ocaml_name,
                         Structural_map.field_expr value actual_field )
                      :: acc)
                      rest)
          in
          project_fields [] expected.fields
          |> Result.map (fun fields ->
              Semantic_ir.Record
                ( fields,
                  Some
                    (record_type_application expected.type_name
                       expected.type_arguments) ))
      | _ ->
          Error.error
            ("set value type must match record element type: expected "
           ^ Types.source_name element_ty ^ ", got "
            ^ Types.source_name value.ty))
  | _ ->
      coerce_closed element_ty value.ty value.semantic_expr

let constrain_record_function_argument_expr fn element_ty =
  let rec constrain_pattern type_name = function
    | Semantic_ir.PVar name ->
        Some (Semantic_ir.PConstraint (Semantic_ir.PVar name, type_name))
    | Semantic_ir.PLocated (node_id, location, pattern) ->
        constrain_pattern type_name pattern
        |> Option.map (fun pattern ->
               Semantic_ir.PLocated (node_id, location, pattern))
    | _ -> None
  in
  match (Semantic_ir.unlocated fn.semantic_expr, element_ty) with
  | Semantic_ir.Fun ([ pattern ], body), TNamed_record record -> (
      match
        constrain_pattern
          (record_type_application record.type_name record.type_arguments)
          pattern
      with
      | Some pattern -> Semantic_ir.Fun ([ pattern ], body)
      | None -> fn.semantic_expr)
  | Semantic_ir.Fun ([ pattern ], body), TRecord _ ->
      Semantic_ir.Fun ([ Semantic_ir.PTyped (pattern, element_ty) ], body)
  | _ -> fn.semantic_expr

let rec concrete_constraint_type = function
  | TPoly_variant row -> List.for_all concrete_constraint_type (List.filter_map snd row.tags)
  | ty when Types.is_dynamic ty -> true
  | TUnknown | TMeta _ | TVar _ | TOverloaded_fn _ -> false
  | TRecord fields -> (
      match Types.homogeneous_record_value_type fields with
      | Some value_ty -> concrete_constraint_type value_ty
      | None -> false)
  | TNullable ty | TArray ty | TRef ty | TList ty | TVector ty | TSet ty
  | TSeq ty ->
      concrete_constraint_type ty
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.for_all concrete_constraint_type arguments
  | TConstraint constraint_ ->
      List.for_all concrete_constraint_type (constraint_children constraint_)
  | TFn (parameters, return_type) ->
      List.for_all concrete_constraint_type (return_type :: parameters)
  | TNamed_record record ->
      List.for_all concrete_constraint_type record.type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TOcaml _ ->
      true

let param_constraint_name = function
  | TConstraint (Seqable_constraint { requirement = Required; _ }) -> None
  | TPoly_variant { bound = Exact_row; _ } as ty
    when concrete_constraint_type ty -> Some (Types.ocaml_name ty)
  | TFn _ as ty when concrete_constraint_type ty -> Some (Types.ocaml_name ty)
  | (TNullable _ | TList _ | TVector _ | TSet _ | TSeq _) as ty
    when concrete_constraint_type ty ->
      Some (Types.ocaml_name ty)
  | TRecord fields as ty
    when Types.is_homogeneous_record fields && concrete_constraint_type ty ->
      Some (Types.ocaml_name ty)
  | (TInt | TFloat | TChar | TString | TSymbol | TKeyword | TBool | TUnit
    | TArray _ | TRef _ | TOcaml _ | TOcaml_app _ | TTuple _ | TNamed_record _
    | TConstraint _) as ty ->
      Some (Types.ocaml_name ty)
  | _ -> None
