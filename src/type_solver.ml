open Semantic_type

type variable = Metavariable of int | Declared of string

let variable_equal left right =
  match (left, right) with
  | Metavariable left, Metavariable right -> left = right
  | Declared left, Declared right -> String.equal left right
  | Metavariable _, Declared _ | Declared _, Metavariable _ -> false

module Variable_map = Persistent_hash_map.Make (struct
  type t = variable

  let equal = variable_equal

  let hash = function
    | Metavariable id -> id lsl 1
    | Declared name -> (Hashtbl.hash name lsl 1) lor 1
end)

type substitutions = ty Variable_map.t

let empty = Variable_map.empty
let find_opt = Variable_map.find_opt
let add = Variable_map.add

let of_list bindings =
  List.fold_right
    (fun (variable, ty) substitutions -> add variable ty substitutions)
    bindings empty

let filter predicate substitutions =
  Variable_map.fold
    (fun variable ty filtered ->
      if predicate variable ty then add variable ty filtered else filtered)
    substitutions empty

type conflict = { left : ty; right : ty }

let next_metavariable = ref 0

(* Global metavariable solutions: successful unifications commit their
   metavariable bindings here so a meta solved at one call site is visible
   everywhere its `TMeta` node is read later — the union-find behaviour a
   threaded substitution map cannot provide across isolated `unify` calls.
   Only Metavariable bindings are committed; Declared names stay scoped to
   the scheme they came from. *)
let meta_solutions : (int, ty) Hashtbl.t = Hashtbl.create 1024

let clear_meta_solutions () = Hashtbl.reset meta_solutions

let fresh ?location () =
  let id = !next_metavariable in
  incr next_metavariable;
  TMeta { id; location }

let rec variable_mem variable = function
  | [] -> false
  | candidate :: _ when variable_equal candidate variable -> true
  | _ :: rest -> variable_mem variable rest

let map_preserving_identity map values =
  let rec map_values = function
    | [] as values -> values
    | head :: tail as values ->
        let mapped_head = map head in
        let mapped_tail = map_values tail in
        if mapped_head == head && mapped_tail == tail then values
        else mapped_head :: mapped_tail
  in
  map_values values

let rec variables ty =
  let union left right =
    List.fold_left
      (fun variables variable ->
        if variable_mem variable variables then variables
        else variable :: variables)
      left right
  in
  let variables_all types =
    List.fold_left (fun names ty -> union names (variables ty)) [] types
  in
  let field_variables fields =
    List.fold_left
      (fun names (field : field) ->
        let free =
          variables field.ty
          |> List.filter (function
            | Declared name -> not (List.mem name field.quantified)
            | Metavariable _ -> true)
        in
        union names free)
      [] fields
  in
  match ty with
  | TPoly_variant row -> variables_all (List.filter_map snd row.tags)
  | TMeta { id; _ } -> [ Metavariable id ]
  | TVar name -> [ Declared name ]
  | TNullable inner
  | TArray inner
  | TRef inner
  | TList inner
  | TVector inner
  | TSet inner
  | TSeq inner ->
      variables inner
  | TOcaml_app (_, arguments) | TTuple arguments -> variables_all arguments
  | TConstraint constraint_ -> variables_all (constraint_children constraint_)
  | TFn (parameters, return_ty) -> variables_all (return_ty :: parameters)
  | TOverloaded_fn arities ->
      arities
      |> List.concat_map (fun arity ->
          (arity.return_ty :: arity.fixed_params)
          @ Option.to_list arity.rest_param)
      |> variables_all
  | TRecord fields -> field_variables fields
  | TNamed_record { type_arguments; fields; _ } ->
      union (variables_all type_arguments) (field_variables fields)
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TOcaml _ ->
      []

module Physical_type_nodes = Hashtbl.Make (struct
  type t = ty
  let equal left right = left == right
  let hash ty = Hashtbl.hash_param 4 16 ty
end)

let may_contain_variable ?visited predicate ty =
  (* This is only a preflight check. Bound repeated visits to shared type graphs;
     exhausting the budget conservatively falls back to normal substitution. *)
  let remaining = ref 2048 in
  let rec affects ty =
    let already_visited =
      match visited with
      | None -> false
      | Some nodes ->
          if Physical_type_nodes.mem nodes ty then true
          else (Physical_type_nodes.add nodes ty (); false)
    in
    if already_visited then false
    else (
    decr remaining;
    if !remaining < 0 then true
    else
      match ty with
      | TMeta { id; _ } ->
          predicate (Metavariable id)
      | TVar name -> predicate (Declared name)
      | TNullable inner | TArray inner | TRef inner | TList inner
      | TVector inner | TSet inner | TSeq inner -> affects inner
      | TOcaml_app (_, items) | TTuple items -> List.exists affects items
      | TConstraint constraint_ ->
          List.exists affects (constraint_children constraint_)
      | TFn (parameters, result) ->
          List.exists affects parameters || affects result
      | TOverloaded_fn arities ->
          List.exists
            (fun arity ->
              List.exists affects arity.fixed_params
              || Option.fold ~none:false ~some:affects arity.rest_param
              || affects arity.return_ty)
            arities
      | TRecord fields ->
          List.exists (fun (field : field) -> affects field.ty) fields
      | TNamed_record record ->
          List.exists affects record.type_arguments
          || List.exists (fun (field : field) -> affects field.ty) record.fields
      | TPoly_variant row ->
          List.exists
            (fun (_, payload) -> Option.fold ~none:false ~some:affects payload)
            row.tags
      | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TNil | TUnknown | TOcaml _ -> false)
  in
  affects ty

let globally_bound variable =
  match variable with
  | Metavariable id -> Hashtbl.mem meta_solutions id
  | Declared _ -> false

let potentially_affected substitutions ty =
  may_contain_variable
    (fun variable ->
      Variable_map.mem variable substitutions || globally_bound variable)
    ty

(* Quantified names may be included: this summary only proves absence.
   None means the traversal budget was exhausted, so substitution must run. *)
let potential_variables ty =
  let variables = ref [] in
  let collect variable =
    if not (variable_mem variable !variables) then
      variables := variable :: !variables;
    false
  in
  let exhausted = may_contain_variable collect ty in
  (* Only allocate graph memoization when the inexpensive tree walk cannot
     finish. Physical identity preserves distinct types even on hash collisions. *)
  let exhausted = exhausted &&
    may_contain_variable ~visited:(Physical_type_nodes.create 32) collect ty in
  if exhausted then None else Some !variables

let rec apply substitutions ty =
  match ty with
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TOcaml _ -> ty
  | (TMeta _ | TVar _) -> apply_with_substitutions substitutions ty
  | _ when not (potentially_affected substitutions ty) -> ty
  | _ -> apply_with_substitutions substitutions ty
and apply_with_substitutions substitutions ty =
    let visiting = ref [] in
    (* Keep adjacent and separated shared children without hashing whole types.
       Cyclic replacements can map the same node differently while visiting. *)
    let last_mapped = ref None in
    let previous_mapped = ref None in
    let memoized_node = function
      | TNullable _ | TOcaml_app _ | TTuple _ | TArray _ | TRef _ | TList _
      | TVector _ | TSet _ | TSeq _ | TFn _ | TOverloaded_fn _ | TRecord _
      | TPoly_variant _ | TNamed_record _ | TConstraint _ ->
          true
      | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _
        ->
          false
    in
    let rec apply_ty ty =
      if not (memoized_node ty) then apply_uncached ty
      else
        let context = !visiting in
        match !last_mapped with
        | Some (original, previous_context, mapped)
          when original == ty && previous_context == context -> mapped
        | Some _ | None -> (
            match !previous_mapped with
            | Some (original, previous_context, mapped)
              when original == ty && previous_context == context -> mapped
            | Some _ | None ->
                let mapped = apply_uncached ty in
                previous_mapped := !last_mapped;
                last_mapped := Some (ty, context, mapped);
                mapped)
    and apply_replacement variable original replacement =
      if variable_mem variable !visiting then original
      else
        let previous = !visiting in
        visiting := variable :: previous;
        let mapped = apply_ty replacement in
        visiting := previous;
        mapped
    and apply_inner original build inner =
      let mapped = apply_ty inner in
      if mapped == inner then original else build mapped
    and apply_field (field : field) =
      if field.quantified = [] then
        let field_ty = apply_ty field.ty in
        if field_ty == field.ty then field else { field with ty = field_ty }
      else
        let free = variables field.ty in
        let substitutions =
          filter
            (fun variable _ ->
              variable_mem variable free
              &&
              match variable with
              | Declared name -> not (List.mem name field.quantified)
              | Metavariable _ -> true)
            substitutions
        in
        let replacement_variables =
          Variable_map.fold
            (fun _ ty names -> variables ty @ names)
            substitutions []
        in
        let occupied = free @ replacement_variables in
        let fresh_name () =
          let rec choose () =
            let id = !next_metavariable in
            incr next_metavariable;
            let name = "lg_field_" ^ string_of_int id in
            if variable_mem (Declared name) occupied then choose () else name
          in
          choose ()
        in
        let renamings =
          List.filter_map
            (fun name ->
              if variable_mem (Declared name) replacement_variables then
                Some (name, fresh_name ())
              else None)
            field.quantified
        in
        let quantified =
          List.map
            (fun name ->
              Option.value (List.assoc_opt name renamings) ~default:name)
            field.quantified
        in
        let field_ty =
          apply
            (of_list
               (List.map
                  (fun (name, replacement) -> (Declared name, TVar replacement))
                  renamings))
            field.ty
        in
        let field_ty = apply substitutions field_ty in
        if quantified = field.quantified && field_ty == field.ty then field
        else { field with ty = field_ty; quantified }
    and apply_uncached ty =
      match ty with
      | TPoly_variant _ -> Semantic_type.map_children apply_ty ty
      | TMeta { id; _ } -> (
          match find_opt (Metavariable id) substitutions with
          | Some (TMeta replacement) when replacement.id = id -> ty
          | Some replacement ->
              apply_replacement (Metavariable id) ty replacement
          | None -> (
              match Hashtbl.find_opt meta_solutions id with
              | None -> ty
              | Some replacement ->
                  apply_replacement (Metavariable id) ty replacement))
      | TVar name -> (
          match find_opt (Declared name) substitutions with
          | None -> ty
          | Some (TVar candidate) when String.equal candidate name -> ty
          | Some replacement -> apply_replacement (Declared name) ty replacement
          )
      | TNullable inner -> apply_inner ty (fun inner -> TNullable inner) inner
      | TOcaml_app (name, arguments) ->
          let mapped = map_preserving_identity apply_ty arguments in
          if mapped == arguments then ty else TOcaml_app (name, mapped)
      | TConstraint constraint_ ->
          let mapped = map_constraint apply_ty constraint_ in
          if mapped == constraint_ then ty else TConstraint mapped
      | TTuple items ->
          let mapped = map_preserving_identity apply_ty items in
          if mapped == items then ty else TTuple mapped
      | TArray inner -> apply_inner ty (fun inner -> TArray inner) inner
      | TRef inner -> apply_inner ty (fun inner -> TRef inner) inner
      | TList inner -> apply_inner ty (fun inner -> TList inner) inner
      | TVector inner -> apply_inner ty (fun inner -> TVector inner) inner
      | TSet inner -> apply_inner ty (fun inner -> TSet inner) inner
      | TSeq inner -> apply_inner ty (fun inner -> TSeq inner) inner
      | TFn (parameters, return_ty) ->
          let mapped_parameters = map_preserving_identity apply_ty parameters in
          let mapped_return = apply_ty return_ty in
          if mapped_parameters == parameters && mapped_return == return_ty then
            ty
          else TFn (mapped_parameters, mapped_return)
      | TOverloaded_fn arities ->
          let apply_optional = function
            | None as value -> value
            | Some inner as value ->
                let mapped = apply_ty inner in
                if mapped == inner then value else Some mapped
          in
          let apply_arity arity =
            let fixed_params =
              map_preserving_identity apply_ty arity.fixed_params
            in
            let rest_param = apply_optional arity.rest_param in
            let return_ty = apply_ty arity.return_ty in
            if
              fixed_params == arity.fixed_params
              && rest_param == arity.rest_param
              && return_ty == arity.return_ty
            then arity
            else { fixed_params; rest_param; return_ty }
          in
          let mapped = map_preserving_identity apply_arity arities in
          if mapped == arities then ty else TOverloaded_fn mapped
      | TRecord fields ->
          let mapped = map_preserving_identity apply_field fields in
          if mapped == fields then ty else TRecord mapped
      | TNamed_record record ->
          let type_arguments =
            map_preserving_identity apply_ty record.type_arguments
          in
          let fields = map_preserving_identity apply_field record.fields in
          if type_arguments == record.type_arguments && fields == record.fields
          then ty
          else TNamed_record { record with type_arguments; fields }
      | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol
      | TKeyword | TBool | TUnit | TNil | TUnknown | TOcaml _ ->
          ty
    in
    apply_ty ty

let rec occurs variable ty =
  match ty with
  | TPoly_variant row -> List.exists (occurs variable) (List.filter_map snd row.tags)
  | TMeta { id; _ } -> variable_equal variable (Metavariable id)
  | TVar name -> variable_equal variable (Declared name)
  | TNullable inner
  | TArray inner
  | TRef inner
  | TList inner
  | TVector inner
  | TSet inner
  | TSeq inner ->
      occurs variable inner
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists (occurs variable) arguments
  | TConstraint constraint_ ->
      List.exists (occurs variable) (constraint_children constraint_)
  | TFn (parameters, return_ty) ->
      List.exists (occurs variable) parameters || occurs variable return_ty
  | TOverloaded_fn arities ->
      List.exists
        (fun arity ->
          List.exists (occurs variable) arity.fixed_params
          || Option.fold ~none:false ~some:(occurs variable) arity.rest_param
          || occurs variable arity.return_ty)
        arities
  | TRecord fields ->
      List.exists
        (fun (field : field) ->
          (not
             (List.exists
                (fun name -> variable_equal variable (Declared name))
                field.quantified))
          && occurs variable field.ty)
        fields
  | TNamed_record { type_arguments; fields; _ } ->
      List.exists (occurs variable) type_arguments
      || List.exists
           (fun (field : field) ->
             (not
                (List.exists
                   (fun name -> variable_equal variable (Declared name))
                   field.quantified))
             && occurs variable field.ty)
           fields
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TOcaml _ ->
      false

let bind substitutions variable ty =
  let ty = apply substitutions ty in
  let variable_ty =
    match variable with
    | Metavariable id -> TMeta { id; location = None }
    | Declared name -> TVar name
  in
  let same_variable =
    match (variable, ty) with
    | Metavariable id, TMeta meta -> id = meta.id
    | Declared name, TVar candidate -> name = candidate
    | _ -> false
  in
  if same_variable then Ok substitutions
  else
    match ty with
    | TUnknown -> Ok substitutions
    | _ when occurs variable ty -> Error { left = variable_ty; right = ty }
    | _ -> Ok (add variable ty substitutions)

let bind_meta substitutions meta ty =
  bind substitutions (Metavariable meta.id) ty

let conflict_is_occurs conflict =
  List.exists
    (fun variable -> occurs variable conflict.right)
    (variables conflict.left)
  || List.exists
       (fun variable -> occurs variable conflict.left)
       (variables conflict.right)

let rec is_open = function
  | TPoly_variant row -> row.bound <> Exact_row || List.exists is_open (List.filter_map snd row.tags)
  | TUnknown | TMeta _ | TVar _ -> true
  | TNullable inner
  | TArray inner
  | TRef inner
  | TList inner
  | TVector inner
  | TSet inner
  | TSeq inner ->
      is_open inner
  | TOcaml_app (_, arguments) | TTuple arguments ->
      List.exists is_open arguments
  | TConstraint constraint_ ->
      List.exists is_open (constraint_children constraint_)
  | TFn (parameters, return_ty) -> List.exists is_open (return_ty :: parameters)
  | TOverloaded_fn arities ->
      List.exists
        (fun arity ->
          List.exists is_open
            ((arity.return_ty :: arity.fixed_params)
            @ Option.to_list arity.rest_param))
        arities
  | TRecord fields ->
      List.exists (fun (field : field) -> is_open field.ty) fields
  | TNamed_record { type_arguments; _ } -> List.exists is_open type_arguments
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TOcaml _ ->
      false

let force substitutions variable ty = add variable ty substitutions

let matching_fields left right =
  let find_right =
    if List.compare_length_with left 8 >= 0
       && List.compare_length_with right 32 >= 0 then (
      let fields = Hashtbl.create (List.length right) in
      List.iter
        (fun (field : field) ->
          (* Match the first occurrence, as the ordered scan does. *)
          if not (Hashtbl.mem fields field.keyword) then
            Hashtbl.add fields field.keyword field.ty)
        right;
      fun keyword -> Hashtbl.find_opt fields keyword)
    else
      fun keyword ->
        List.find_opt (fun (field : field) -> keyword = field.keyword) right
        |> Option.map (fun (field : field) -> field.ty)
  in
  List.filter_map
    (fun (field : field) ->
      Option.map (fun right_ty -> field.ty, right_ty) (find_right field.keyword))
    left

let resolve_head substitutions ty =
  let rec resolve visiting ty =
    let resolve_variable variable =
      if variable_mem variable visiting then ty
      else
        match find_opt variable substitutions with
        | Some replacement -> resolve (variable :: visiting) replacement
        | None -> (
            match variable with
            | Metavariable id -> (
                match Hashtbl.find_opt meta_solutions id with
                | None -> ty
                | Some replacement -> resolve (variable :: visiting) replacement)
            | Declared _ -> ty)
    in
    match ty with
    | TMeta meta -> resolve_variable (Metavariable meta.id)
    | TVar name -> resolve_variable (Declared name)
    | _ -> ty
  in
  resolve [] ty

let unify ?(resolve_alias = fun _ -> None) substitutions left right =
 let active_alias_pairs = ref [] in
 let pending_commits = ref [] in
 (* Probing calls start from `empty` and compare two types in isolation;
    solving calls thread an accumulating substitution. Only the latter may
    publish ground bindings — a discarded probe result must not pin metas
    globally. *)
 let committing = Variable_map.cardinal substitutions > 0 in
 let bind_meta_tracked substitutions meta ty =
   match bind_meta substitutions meta ty with
   | Ok substitutions ->
       pending_commits := (meta, ty) :: !pending_commits;
       Ok substitutions
   | Error _ as error -> error
 in
 let rec unify substitutions left right =
  let left = resolve_head substitutions left in
  let right = resolve_head substitutions right in
  if left == right then Ok substitutions
  else
    match (left, right) with
    | TPoly_variant left_row, TPoly_variant right_row ->
        if not (Variant_row.compatible left_row right_row) then Error {left; right}
        else List.fold_left (fun result (tag, payload) ->
          Result.bind result (fun substitutions ->
            match List.assoc_opt tag right_row.tags, payload with
            | None, _ | Some None, None -> Ok substitutions
            | Some (Some right), Some left -> unify substitutions left right
            | _ -> Error {left; right})) (Ok substitutions) left_row.tags
    | TInt, TOcaml "int"
    | TOcaml "int", TInt
    | TInt, TInt
    | TFloat, TFloat
    | TChar, TChar
    | TString, TString
    | TRegex, TRegex
    | TMap_keys, TMap_keys
    | TSymbol, TSymbol
    | TKeyword, TKeyword
    | TBool, TBool
    | TUnit, TUnit
    | TNil, TNil ->
        Ok substitutions
    | TOcaml left_name, TOcaml right_name when String.equal left_name right_name
      ->
        Ok substitutions
    | TUnknown, _ | _, TUnknown -> Ok substitutions
    | TMeta meta, ty | ty, TMeta meta -> bind_meta_tracked substitutions meta ty
    | TVar name, ty | ty, TVar name -> bind substitutions (Declared name) ty
    | ( TConstraint (Truthy_constraint left),
        TConstraint (Truthy_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Truthy_constraint value_ty), ty
    | ty, TConstraint (Truthy_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Nil_predicate_constraint left),
        TConstraint (Nil_predicate_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Nil_predicate_constraint value_ty), ty
    | ty, TConstraint (Nil_predicate_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Printable_constraint left),
        TConstraint (Printable_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Printable_constraint value_ty), ty
    | ty, TConstraint (Printable_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Exception_data_constraint left),
        TConstraint (Exception_data_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Exception_data_constraint value_ty), ty
    | ty, TConstraint (Exception_data_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Hashable_constraint left),
        TConstraint (Hashable_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Hashable_constraint value_ty), ty
    | ty, TConstraint (Hashable_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Comparable_constraint left),
        TConstraint (Comparable_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Comparable_constraint value_ty), ty
    | ty, TConstraint (Comparable_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Array_index_constraint left),
        TConstraint (Array_index_constraint right) ) ->
        unify substitutions left right
    | TConstraint (Array_index_constraint value_ty), ty
    | ty, TConstraint (Array_index_constraint value_ty) ->
        unify substitutions value_ty ty
    | ( TConstraint (Symbol_predicate_constraint left),
        TConstraint (Symbol_predicate_constraint right) ) ->
        unify substitutions left right
    | TNullable left, TNullable right
    | TArray left, TArray right
    | TRef left, TRef right
    | TList left, TList right
    | TVector left, TVector right
    | TSet left, TSet right
    | TSeq left, TSeq right ->
        unify substitutions left right
    | TSeq left, TOcaml_app (name, [ right ])
    | TOcaml_app (name, [ left ]), TSeq right
      when name = "Seq.t" || name = "__lg_next_seq"
           || name = "__lg_reversible_next_seq" ->
        unify substitutions left right
    | TNullable left, TOcaml_app ("option", [ right ])
    | TOcaml_app ("option", [ left ]), TNullable right ->
        unify substitutions left right
    | ( TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ }),
        (( TList actual
         | TVector actual
         | TSet actual
         | TSeq actual
         | TArray actual ) as collection_ty) )
    | ( (( TList actual
         | TVector actual
         | TSet actual
         | TSeq actual
         | TArray actual ) as collection_ty),
        TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ })
      ) ->
        Result.bind (unify substitutions element_ty actual)
          (fun substitutions -> unify substitutions storage_ty collection_ty)
    | ( TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ }),
        TString )
    | ( TString,
        TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ })
      ) ->
        Result.bind (unify substitutions element_ty TChar) (fun substitutions ->
            unify substitutions storage_ty TString)
    | ( TConstraint
          (Seqable_constraint { element; storage; requirement }),
        (TOcaml_app ("Lg_runtime.Runtime_map.t", [ key; value ]) as map_ty) )
    | ( (TOcaml_app ("Lg_runtime.Runtime_map.t", [ key; value ]) as map_ty),
        TConstraint
          (Seqable_constraint { element; storage; requirement }) )
      when requirement <> Optional_sequential ->
        Result.bind (unify substitutions element (TTuple [ key; value ]))
          (fun substitutions -> unify substitutions storage map_ty)
    | ( TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ }),
        (TOcaml_app (("__lg_next_seq" | "__lg_reversible_next_seq"), [ actual ])
         as collection_ty) )
    | ( (TOcaml_app (("__lg_next_seq" | "__lg_reversible_next_seq"), [ actual ])
         as collection_ty),
        TConstraint
          (Seqable_constraint { element = element_ty; storage = storage_ty; _ })
      ) ->
        Result.bind (unify substitutions element_ty actual)
          (fun substitutions -> unify substitutions storage_ty collection_ty)
    | ( TConstraint
          (Seqable_constraint
             {
               requirement = left_requirement;
               element = left_element;
               storage = left_storage;
             }),
        TConstraint
          (Seqable_constraint
             {
               requirement = right_requirement;
               element = right_element;
               storage = right_storage;
             }) )
      when left_requirement = right_requirement ->
        unify_lists substitutions
          [ left_element; left_storage ]
          [ right_element; right_storage ]
    | ( TConstraint
          (Contains_constraint { key = left_key; storage = left_storage }),
        TConstraint
          (Contains_constraint { key = right_key; storage = right_storage }) )
      ->
        unify_lists substitutions [ left_key; left_storage ]
          [ right_key; right_storage ]
    | TConstraint (Contains_constraint { key; storage }),
      ((TSet actual_key | TOcaml_app ("Lg_runtime.Runtime_map.t", [actual_key; _])) as collection)
    | ((TSet actual_key | TOcaml_app ("Lg_runtime.Runtime_map.t", [actual_key; _])) as collection),
      TConstraint (Contains_constraint { key; storage }) ->
        Result.bind (unify substitutions key actual_key)
          (fun substitutions -> unify substitutions storage collection)
    | TConstraint (Contains_constraint { key; storage }), (TVector _ as collection)
    | (TVector _ as collection), TConstraint (Contains_constraint { key; storage }) ->
        Result.bind (unify substitutions key TInt)
          (fun substitutions -> unify substitutions storage collection)
    | TConstraint (Contains_constraint { key; storage }),
      ((TMap_keys | TRecord _ | TNamed_record _) as collection)
    | ((TMap_keys | TRecord _ | TNamed_record _) as collection),
      TConstraint (Contains_constraint { key; storage }) ->
        Result.bind (unify substitutions key TKeyword)
          (fun substitutions -> unify substitutions storage collection)
    | ( TConstraint (Open_boundary_constraint left),
        TConstraint (Open_boundary_constraint right) ) ->
        unify substitutions left right
    | ( TConstraint
          (Protocol_constraint
             {
               protocol_id = left_id;
               witness = left_witness;
               value = left_value;
               guarded = left_guarded;
             }),
        TConstraint
          (Protocol_constraint
             {
               protocol_id = right_id;
               witness = right_witness;
               value = right_value;
               guarded = right_guarded;
             }) )
      when Protocol_id.equal left_id right_id && left_guarded = right_guarded ->
        unify_lists substitutions
          [ left_witness; left_value ]
          [ right_witness; right_value ]
    | TOcaml_app (left_name, left_args), TOcaml_app (right_name, right_args)
      when left_name = right_name
           && List.length left_args = List.length right_args ->
        unify_lists substitutions left_args right_args
    | TTuple left_items, TTuple right_items
      when List.length left_items = List.length right_items ->
        unify_lists substitutions left_items right_items
    | TFn (left_params, left_return), TFn (right_params, right_return)
      when List.length left_params = List.length right_params ->
        Result.bind (unify_lists substitutions left_params right_params)
          (fun substitutions -> unify substitutions left_return right_return)
    | TOverloaded_fn left_arities, TOverloaded_fn right_arities
      when List.length left_arities = List.length right_arities ->
        List.fold_left2
          (fun result left_arity right_arity ->
            Result.bind result (fun substitutions ->
                unify_arities substitutions left_arity right_arity))
          (Ok substitutions) left_arities right_arities
    | TNamed_record left_record, TNamed_record right_record
      when Type_id.equal left_record.type_id right_record.type_id
           && List.length left_record.type_arguments
              = List.length right_record.type_arguments ->
        Result.bind
          (unify_lists substitutions left_record.type_arguments
             right_record.type_arguments) (fun substitutions ->
            let fields =
              matching_fields left_record.fields right_record.fields
            in
            List.fold_left
              (fun result (left, right) ->
                Result.bind result (fun substitutions ->
                    unify substitutions left right))
              (Ok substitutions) fields)
    | TNamed_record record, TOcaml name
    | TOcaml name, TNamed_record record
      when (record.type_name = name || Type_id.name record.type_id = name)
           && record.type_arguments = [] ->
        Ok substitutions
    | TNamed_record record, TOcaml_app (name, arguments)
    | TOcaml_app (name, arguments), TNamed_record record
      when (record.type_name = name || Type_id.name record.type_id = name)
           && List.length record.type_arguments = List.length arguments ->
        unify_lists substitutions record.type_arguments arguments
    | ( TOcaml_app ("Lg_runtime.Runtime_map.t", [ key_ty; value_ty ]),
        (TRecord fields | TNamed_record { fields; nominal = false; _ }) )
    | ( (TRecord fields | TNamed_record { fields; nominal = false; _ }),
        TOcaml_app ("Lg_runtime.Runtime_map.t", [ key_ty; value_ty ]) ) ->
        Result.bind (unify substitutions key_ty TKeyword) (fun substitutions ->
            List.fold_left
              (fun result (field : field) ->
                Result.bind result (fun substitutions ->
                    unify substitutions value_ty field.ty))
              (Ok substitutions) fields)
    | ( (TRecord left_fields | TNamed_record { fields = left_fields; _ }),
        (TRecord right_fields | TNamed_record { fields = right_fields; _ }) ) ->
        let fields = matching_fields left_fields right_fields in
        List.fold_left
          (fun result (left, right) ->
            Result.bind result (fun substitutions ->
                unify substitutions left right))
          (Ok substitutions) fields
    | (TOcaml _ as alias), (TPoly_variant _ | TRecord _ | TNamed_record _)
    | (TPoly_variant _ | TRecord _ | TNamed_record _), (TOcaml _ as alias) -> (
        let other = if alias == left then right else left in
        let pair = (alias, other) in
        if List.mem pair !active_alias_pairs then Ok substitutions
        else
          match resolve_alias alias with
          | Some ((TPoly_variant _ | TRecord _ | TNamed_record _) as manifest) ->
              (* Recursive aliases are compared coinductively, but only along
                 the current path; sibling payloads still need unification. *)
              let previous = !active_alias_pairs in
              active_alias_pairs := pair :: previous;
              Fun.protect
                ~finally:(fun () -> active_alias_pairs := previous)
                (fun () ->
                  if alias == left then unify substitutions manifest right
                  else unify substitutions left manifest)
          | _ -> Error { left; right })
    | _ -> Error { left; right }

and unify_lists substitutions left right =
  List.fold_left2
    (fun result left right ->
      Result.bind result (fun substitutions -> unify substitutions left right))
    (Ok substitutions) left right

and unify_arities substitutions left right =
  if List.length left.fixed_params <> List.length right.fixed_params then
    Error { left = TOverloaded_fn [ left ]; right = TOverloaded_fn [ right ] }
  else
    Result.bind (unify_lists substitutions left.fixed_params right.fixed_params)
      (fun substitutions ->
        let rest =
          match (left.rest_param, right.rest_param) with
          | None, None -> Ok substitutions
          | Some left, Some right -> unify substitutions left right
          | _ ->
              Error
                {
                  left = TOverloaded_fn [ left ];
                  right = TOverloaded_fn [ right ];
                }
        in
        Result.bind rest (fun substitutions ->
            unify substitutions left.return_ty right.return_ty))
 in
 match unify substitutions left right with
 | Ok substitutions ->
     List.iter
       (fun (meta, ty) ->
         (* Only ground solutions are committed: meta-to-meta links stay in
            the returned substitution, so probing unifications that merely
            relate open variables cannot pin them globally. *)
         if committing && not (is_open ty) then (
           if Sys.getenv_opt "LG_DEBUG_COMMIT" = Some "1" then
             Printf.eprintf "[commit] g%d%s <- %s\n%!" meta.id
               (match meta.location with
               | Some _ -> "@loc"
               | None -> "")
               (match ty with
               | TInt -> "int" | TFloat -> "float" | TBool -> "bool"
               | TString -> "string" | TKeyword -> "keyword"
               | TSymbol -> "symbol" | TUnit -> "unit" | TNil -> "nil"
               | TChar -> "char" | TRegex -> "regex" | TMap_keys -> "map_keys"
               | TMeta { id = rid; _ } -> "g" ^ string_of_int rid
               | TVar n -> "'" ^ n | TOcaml n -> n
               | TOcaml_app (n, _) -> n ^ " _" | TFn _ -> "fn"
               | TTuple _ -> "tuple" | TList _ -> "list"
               | TVector _ -> "vector" | TSet _ -> "set" | TSeq _ -> "seq"
               | TArray _ -> "array" | TRef _ -> "ref" | TNullable _ -> "opt"
               | TRecord _ -> "record" | TNamed_record r ->
                   "named:" ^ Type_id.name r.type_id
               | TPoly_variant _ -> "polyvariant" | TConstraint _ -> "constr"
               | TOverloaded_fn _ -> "overloaded"
               | TUnknown -> "?");
           Hashtbl.replace meta_solutions meta.id ty))
       !pending_commits;
     Ok substitutions
 | Error _ as error -> error

let unify_lists substitutions left right =
  List.fold_left2
    (fun result left right ->
      Result.bind result (fun substitutions -> unify substitutions left right))
    (Ok substitutions) left right

let infer substitutions ~template ~actual = unify substitutions template actual

let infer_all substitutions ~templates ~actuals =
  if List.length templates <> List.length actuals then Ok substitutions
  else unify_lists substitutions templates actuals

let rec freshen_unknowns = function
  | TPoly_variant _ as ty -> Semantic_type.map_children freshen_unknowns ty
  | TUnknown -> fresh ()
  | TNullable ty -> TNullable (freshen_unknowns ty)
  | TArray ty -> TArray (freshen_unknowns ty)
  | TRef ty -> TRef (freshen_unknowns ty)
  | TList ty -> TList (freshen_unknowns ty)
  | TVector ty -> TVector (freshen_unknowns ty)
  | TSet ty -> TSet (freshen_unknowns ty)
  | TSeq ty -> TSeq (freshen_unknowns ty)
  | TOcaml_app (name, arguments) ->
      TOcaml_app (name, List.map freshen_unknowns arguments)
  | TConstraint constraint_ ->
      TConstraint (map_constraint freshen_unknowns constraint_)
  | TTuple arguments -> TTuple (List.map freshen_unknowns arguments)
  | TFn (parameters, return_ty) ->
      TFn (List.map freshen_unknowns parameters, freshen_unknowns return_ty)
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             {
               fixed_params = List.map freshen_unknowns arity.fixed_params;
               rest_param = Option.map freshen_unknowns arity.rest_param;
               return_ty = freshen_unknowns arity.return_ty;
             })
           arities)
  | TRecord fields ->
      TRecord
        (List.map
           (fun (field : field) ->
             { field with ty = freshen_unknowns field.ty })
           fields)
  | TNamed_record record ->
      TNamed_record
        {
          record with
          type_arguments = List.map freshen_unknowns record.type_arguments;
        }
  | ( TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
    | TBool | TUnit | TNil | TMeta _ | TVar _ | TOcaml _ ) as ty ->
      ty

let generalize ty =
  let declared_names =
    variables ty
    |> List.filter_map (function
      | Declared name -> Some name
      | Metavariable _ -> None)
  in
  let inferred_name id =
    let rec available suffix =
      let name =
        "g" ^ string_of_int id
        ^ if suffix = 0 then "" else "_" ^ string_of_int suffix
      in
      if List.mem name declared_names then available (suffix + 1) else name
    in
    available 0
  in
  let quantified, substitutions =
    variables ty
    |> List.fold_left
         (fun (quantified, substitutions) -> function
           | Declared name ->
               (Declared_variable name :: quantified, substitutions)
           | Metavariable id when Hashtbl.mem meta_solutions id ->
               (* Already solved globally: keep the meta so `apply` expands
                  its solution instead of quantifying a pinned variable. *)
               (quantified, substitutions)
           | Metavariable id ->
               let name = inferred_name id in
               ( Inferred_variable { metavariable_id = id; name } :: quantified,
                 add (Metavariable id) (TVar name) substitutions ))
         ([], empty)
  in
  let quantified = List.rev quantified in
  { quantified; body = apply substitutions ty }

let instantiate scheme =
  let substitutions =
    List.fold_left
      (fun substitutions -> function
        | Declared_variable name -> add (Declared name) (fresh ()) substitutions
        | Inferred_variable { name; _ } ->
            add (Declared name) (fresh ()) substitutions)
      empty scheme.quantified
  in
  apply substitutions scheme.body

let canonical_scheme_body scheme =
  let variable_name = function
    | Declared_variable name -> ("declared", name)
    | Inferred_variable { name; _ } -> ("inferred", name)
  in
  let substitutions =
    List.fold_left
      (fun (index, substitutions) variable ->
        let category, name = variable_name variable in
        ( index + 1,
          add (Declared name)
            (TVar ("__lg_scheme_" ^ category ^ "_" ^ string_of_int index))
            substitutions ))
      (0, empty) scheme.quantified
    |> snd
  in
  apply substitutions scheme.body

let canonical ty =
  let substitutions =
    variables ty
    |> List.mapi (fun index variable ->
        (variable, TMeta { id = -index - 1; location = None }))
    |> of_list
  in
  apply substitutions ty
