let rec pattern = function
  | Semantic_ir.PLocated (node_id, location, value) ->
      Ocaml_ir.PLocated (node_id, location, pattern value)
  | Semantic_ir.PVar name -> Ocaml_ir.PVar name
  | PAny -> PAny
  | PUnit -> PUnit
  | PInt value -> PInt value
  | PInt64 value -> PInt64 value
  | PString value -> PString value
  | PBool value -> PBool value
  | PPolyTag (name, payload) -> PPolyTag (name, Option.map pattern payload)
  | PConstructor (name, payload) ->
      PConstructor (name, Option.map pattern payload)
  | PTuple patterns -> PTuple (List.map pattern patterns)
  | PList patterns -> PList (List.map pattern patterns)
  | PCons (head, tail) -> PCons (pattern head, pattern tail)
  | PRecord fields ->
      PRecord (List.map (fun (name, value) -> (name, pattern value)) fields)
  | PAlias (value, name) -> PAlias (pattern value, name)
  | POr (left, right) -> POr (pattern left, pattern right)
  | PConstraint (value, type_name) ->
      PConstraint
        (pattern value, Types.ocaml_record_type_name type_name)
  | PTyped (value, ty) ->
      (match ty with
      | Semantic_type.TNamed_record record ->
          PConstraint
            ( pattern value,
              Structural_map.record_type_application record )
      | Semantic_type.TRecord _ -> pattern value
      | _ -> PConstraint (pattern value, Types.ocaml_name ty))

(* A `let` nested in an application argument prints as a wrapped
   `(let ... in ...)` argument, costing an extra line. Lifting the bindings
   in front of the call keeps output flat and is a legal refinement of
   OCaml's unspecified argument evaluation order. It is only safe when no
   bound name can capture a free variable in a sibling expression, so we
   require every bound name to be a compiler-generated `__lg_*` temporary
   and pairwise distinct across the lifted groups. *)
let rec strip_lets = function
  | Ocaml_ir.Let (bindings, value) ->
      let rest, value = strip_lets value in
      (bindings @ rest, value)
  | value -> ([], value)

let rec pattern_bound_names = function
  | Ocaml_ir.PVar name -> [ name ]
  | PAlias (pat, name) -> name :: pattern_bound_names pat
  | PTuple pats | PList pats -> List.concat_map pattern_bound_names pats
  | PCons (head, tail) -> pattern_bound_names head @ pattern_bound_names tail
  | PRecord fields ->
      List.concat_map (fun (_, pat) -> pattern_bound_names pat) fields
  | POr (left, right) -> pattern_bound_names left @ pattern_bound_names right
  | PConstructor (_, pat) | PPolyTag (_, pat) ->
      Option.fold ~none:[] ~some:pattern_bound_names pat
  | PConstraint (pat, _) | PLocated (_, _, pat) -> pattern_bound_names pat
  | _ -> []

let liftable_bindings bindings =
  let names = List.concat_map (fun (pat, _) -> pattern_bound_names pat) bindings in
  List.for_all
    (fun name -> String.length name >= 4 && String.sub name 0 4 = "__lg")
    names
  && List.sort_uniq String.compare names = List.sort String.compare names

(* `let __lg_x = e in __lg_x` carries no meaning beyond evaluation order,
   which is unspecified in argument/scrutinee position anyway — collapse it
   to `e`. Restricted to generated names so user bindings keep their
   source-level references for the language service. *)
let rec bound_pattern_name = function
  | Ocaml_ir.PVar name -> Some (name, None)
  | PLocated (_, _, pattern) -> bound_pattern_name pattern
  | PConstraint (pattern, ty) -> (
      match bound_pattern_name pattern with
      | Some (name, None) -> Some (name, Some ty)
      | other -> other)
  | _ -> None

let is_generated_temp name =
  String.length name >= 4 && String.sub name 0 4 = "__lg"

let rec collapse_identity_lets = function
  | Ocaml_ir.Let ([ (pattern, bound) ], body) -> (
      let rec body_name = function
        | Ocaml_ir.Ident name -> Some name
        | Located (_, _, expr) -> body_name expr
        | _ -> None
      in
      match
        (bound_pattern_name pattern, body_name (collapse_identity_lets body))
      with
      | Some (name, ty), Some name'
        when name = name'
             && String.length name >= 4
             && String.sub name 0 4 = "__lg" -> (
          (* The pattern annotation pins the result type, so it moves onto
             the bound expression. *)
          match ty with
          | Some ty ->
              collapse_identity_lets (Ocaml_ir.Constraint (bound, ty))
          | None -> collapse_identity_lets bound)
      | _ ->
          Ocaml_ir.Let ([ (pattern, bound) ], collapse_identity_lets body))
  | expr -> expr

let rec ocaml_stable = function
  | Ocaml_ir.(Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit
             | Ident _) ->
      true
  | Ocaml_ir.(GadtScope e | Located (_, _, e) | Constraint (e, _)
             | Prefix (_, e) | Field (e, _)) ->
      ocaml_stable e
  | Ocaml_ir.(Tuple es | List es | Array es) -> List.for_all ocaml_stable es
  | Ocaml_ir.(PolyTag (_, e) | Constructor (_, e)) ->
      Option.fold ~none:true ~some:ocaml_stable e
  | Ocaml_ir.Record (fields, _) ->
      List.for_all (fun (_, value) -> ocaml_stable value) fields
  | _ -> false

let rec count_uses name expression =
  let count = count_uses name in
  let rebound_in patterns =
    List.exists
      (fun pattern -> List.mem name (pattern_bound_names pattern))
      patterns
  in
  match expression with
  | Ocaml_ir.Ident other -> if String.equal other name then 1 else 0
  | Ocaml_ir.(Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit
             | PackModule _) ->
      0
  | Ocaml_ir.(GadtScope e | Located (_, _, e) | Constraint (e, _)
             | Prefix (_, e) | Field (e, _)) ->
      count e
  | Ocaml_ir.SetField (target, _, value) -> count target + count value
  | Ocaml_ir.(Tuple es | List es | Array es | Sequence es) ->
      List.fold_left (fun sum e -> sum + count e) 0 es
  | Ocaml_ir.(PolyTag (_, e) | Constructor (_, e)) ->
      Option.fold ~none:0 ~some:count e
  | Ocaml_ir.(Apply (fn, args) | Uncurried_apply (fn, args)) ->
      List.fold_left (fun sum e -> sum + count e) (count fn) args
  | Ocaml_ir.Labelled_apply (fn, args) ->
      List.fold_left (fun sum (_, e) -> sum + count e) (count fn) args
  | Ocaml_ir.If (c, then_e, else_e) -> count c + count then_e + count else_e
  | Ocaml_ir.(Infix (_, left, right) | Cons (left, right)
             | UnpackModule (_, _, left, right)) ->
      count left + count right
  | Ocaml_ir.Fun (patterns, body) ->
      if rebound_in patterns then 0 else count body
  | Ocaml_ir.Labelled_fun (patterns, body) ->
      if rebound_in (List.map snd patterns) then 0 else count body
  | Ocaml_ir.Let (bindings, body) ->
      let rec sum_bindings shadowed = function
        | [] -> if shadowed then 0 else count body
        | (pattern, value) :: rest ->
            (if shadowed then 0 else count value)
            + sum_bindings
                (shadowed
                || List.mem name (pattern_bound_names pattern))
                rest
      in
      sum_bindings false bindings
  | Ocaml_ir.LetRec (fn_name, patterns, body, args) ->
      if String.equal fn_name name || rebound_in patterns then
        List.fold_left (fun sum e -> sum + count e) 0 args
      else
        count body
        + List.fold_left (fun sum e -> sum + count e) 0 args
  | Ocaml_ir.LetRecIn (fn_name, patterns, body, next) ->
      if String.equal fn_name name || rebound_in patterns then 0
      else count body + count next
  | Ocaml_ir.LetRecGroup (bindings, body) ->
      let bound =
        List.concat_map (fun (pattern, _) -> pattern_bound_names pattern)
          bindings
      in
      if List.mem name bound then 0
      else
        List.fold_left
          (fun sum (_, value) -> sum + count value)
          (count body) bindings
  | Ocaml_ir.Match (target, cases) ->
      count target
      + List.fold_left
          (fun sum (pat, body) ->
            sum + (if rebound_in [ pat ] then 0 else count body))
          0 cases
  | Ocaml_ir.Match_guarded (target, cases)
  | Ocaml_ir.Try (target, cases) ->
      count target
      + List.fold_left
          (fun sum (pat, guard, body) ->
            sum
            + Option.fold ~none:0 ~some:count guard
            + (if rebound_in [ pat ] then 0 else count body))
          0 cases
  | Ocaml_ir.Record (fields, _) ->
      List.fold_left (fun sum (_, e) -> sum + count e) 0 fields
  | Ocaml_ir.RecordUpdate (record, fields) ->
      count record
      + List.fold_left (fun sum (_, e) -> sum + count e) 0 fields

let rec subst_ident name replacement expression =
  let open Ocaml_ir in
  let subst = subst_ident name replacement in
  let rebound_in patterns =
    List.exists
      (fun pattern -> List.mem name (pattern_bound_names pattern))
      patterns
  in
  match expression with
  | Ocaml_ir.Ident other when String.equal other name -> replacement
  | Ocaml_ir.(GadtScope e) -> GadtScope (subst e)
  | Ocaml_ir.Located (node_id, location, e) ->
      Located (node_id, location, subst e)
  | Ocaml_ir.(PolyTag (n, e)) -> PolyTag (n, Option.map subst e)
  | Ocaml_ir.Constructor (n, e) -> Constructor (n, Option.map subst e)
  | Ocaml_ir.Tuple es -> Tuple (List.map subst es)
  | Ocaml_ir.List es -> List (List.map subst es)
  | Ocaml_ir.Array es -> Array (List.map subst es)
  | Ocaml_ir.Apply (fn, args) -> Apply (subst fn, List.map subst args)
  | Ocaml_ir.Uncurried_apply (fn, args) ->
      Uncurried_apply (subst fn, List.map subst args)
  | Ocaml_ir.Labelled_apply (fn, args) ->
      Labelled_apply (subst fn, List.map (fun (l, e) -> (l, subst e)) args)
  | Ocaml_ir.If (c, then_e, else_e) -> If (subst c, subst then_e, subst else_e)
  | Ocaml_ir.Fun (patterns, body) ->
      if rebound_in patterns then expression else Fun (patterns, subst body)
  | Ocaml_ir.Labelled_fun (patterns, body) ->
      if rebound_in (List.map snd patterns) then expression
      else Labelled_fun (patterns, subst body)
  | Ocaml_ir.Sequence es -> Sequence (List.map subst es)
  | Ocaml_ir.Let (bindings, body) ->
      let rec rebuild shadowed = function
        | [] -> ([], if shadowed then body else subst body)
        | (pattern, value) :: rest ->
            let value = if shadowed then value else subst value in
            let rest, body =
              rebuild
                (shadowed
                || List.mem name (pattern_bound_names pattern))
                rest
            in
            ((pattern, value) :: rest, body)
      in
      let bindings, body = rebuild false bindings in
      Let (bindings, body)
  | Ocaml_ir.LetRec (fn_name, patterns, body, args) ->
      if String.equal fn_name name || rebound_in patterns then
        LetRec (fn_name, patterns, body, List.map subst args)
      else LetRec (fn_name, patterns, subst body, List.map subst args)
  | Ocaml_ir.LetRecIn (fn_name, patterns, body, next) ->
      if String.equal fn_name name || rebound_in patterns then expression
      else LetRecIn (fn_name, patterns, subst body, subst next)
  | Ocaml_ir.LetRecGroup (bindings, body) ->
      let bound =
        List.concat_map (fun (pattern, _) -> pattern_bound_names pattern)
          bindings
      in
      if List.mem name bound then expression
      else
        LetRecGroup
          ( List.map (fun (pattern, value) -> (pattern, subst value)) bindings,
            subst body )
  | Ocaml_ir.Match (target, cases) ->
      Match
        ( subst target,
          List.map
            (fun (pat, body) ->
              (pat, if rebound_in [ pat ] then body else subst body))
            cases )
  | Ocaml_ir.Match_guarded (target, cases) ->
      Match_guarded
        ( subst target,
          List.map
            (fun (pat, guard, body) ->
              if rebound_in [ pat ] then (pat, guard, body)
              else (pat, Option.map subst guard, subst body))
            cases )
  | Ocaml_ir.Try (target, cases) ->
      Try
        ( subst target,
          List.map
            (fun (pat, guard, body) ->
              if rebound_in [ pat ] then (pat, guard, body)
              else (pat, Option.map subst guard, subst body))
            cases )
  | Ocaml_ir.Infix (op, left, right) -> Infix (op, subst left, subst right)
  | Ocaml_ir.Prefix (op, e) -> Prefix (op, subst e)
  | Ocaml_ir.Constraint (e, ty) -> Constraint (subst e, ty)
  | Ocaml_ir.Field (e, n) -> Field (subst e, n)
  | Ocaml_ir.SetField (target, n, value) -> SetField (subst target, n, subst value)
  | Ocaml_ir.Cons (head, tail) -> Cons (subst head, subst tail)
  | Ocaml_ir.Record (fields, ty) ->
      Record (List.map (fun (n, e) -> (n, subst e)) fields, ty)
  | Ocaml_ir.RecordUpdate (record, fields) ->
      RecordUpdate
        (subst record, List.map (fun (n, e) -> (n, subst e)) fields)
  | Ocaml_ir.UnpackModule (a, b, value, body) ->
      UnpackModule (a, b, subst value, subst body)
  | leaf -> leaf

(* `let __lg_x = stable in ... __lg_x ...` with a single use folds into the
   use site; an unused stable binding drops entirely. The pattern's type
   annotation moves onto the substituted expression so pins survive. *)
let rec simplify_temp_lets = function
  | Ocaml_ir.Let ((pattern, bound) :: rest, body) -> (
      let body = simplify_temp_lets (Ocaml_ir.Let (rest, body)) in
      match bound_pattern_name pattern with
      | Some (name, ty)
        when is_generated_temp name && ocaml_stable bound -> (
          match count_uses name body with
          | 0 -> body
          | 1 ->
              let bound =
                match ty with
                | Some ty -> Ocaml_ir.Constraint (bound, ty)
                | None -> bound
              in
              simplify_temp_lets (subst_ident name bound body)
          | _ -> Ocaml_ir.Let ([ (pattern, bound) ], body))
      | _ -> Ocaml_ir.Let ([ (pattern, bound) ], body))
  | Ocaml_ir.Let ([], body) -> simplify_temp_lets body
  | expression -> expression

let rewrap bindings value =
  List.fold_right
    (fun binding body -> Ocaml_ir.Let ([ binding ], body))
    bindings value

let lift_lets fn args =
  let fn = collapse_identity_lets fn in
  let fn_bindings, fn = strip_lets fn in
  let per_arg =
    List.map (fun arg -> strip_lets (collapse_identity_lets arg)) args
  in
  let lifted = fn_bindings @ List.concat_map fst per_arg in
  if lifted <> [] && liftable_bindings lifted then
    (lifted, fn, List.map snd per_arg)
  else
    ( [],
      rewrap fn_bindings fn,
      List.map (fun (bindings, value) -> rewrap bindings value) per_arg )

let lifted_expression bindings expr =
  match bindings with [] -> expr | _ -> Ocaml_ir.Let (bindings, expr)

let rec lower_node = function
  | Semantic_ir.Typed (_, value) -> expression value
  | Semantic_ir.GadtScope value -> Ocaml_ir.GadtScope (expression value)
  | Semantic_ir.Located (node_id, location, value) ->
      Ocaml_ir.Located (node_id, location, expression value)
  | Int value -> Int value
  | Int64 value -> Int64 value
  | Float value -> Float value
  | String value -> String value
  | Char value -> Char value
  | Bool value -> Bool value
  | Unit -> Unit
  | PolyTag (name, payload) -> PolyTag (name, Option.map expression payload)
  | Constructor (name, payload) ->
      Constructor (name, Option.map expression payload)
  | Tuple values -> Tuple (List.map expression values)
  | Ident name -> Ident name
  | List values ->
      let stable = Semantic_ir.is_stable in
      let rec binding_pattern name = function
        | Semantic_ir.Located (_, _, value) | GadtScope value -> binding_pattern name value
        | Typed (ty, _) -> pattern (Semantic_ir.PTyped (Semantic_ir.PVar name, ty))
        | _ -> Ocaml_ir.PVar name in
      let non_stable =
        List.filter (fun value -> not (stable value)) values
      in
      (* With a single effectful element the unspecified element order is
         unobservable, so it can be inlined without a temporary. *)
      let inline_sole = List.length non_stable <= 1 in
      let bindings, values =
        List.mapi (fun index value ->
          if stable value || inline_sole then None, expression value
          else
            let name = "__lg_list_value'" ^ string_of_int index in
            Some (binding_pattern name value, expression value), Ocaml_ir.Ident name) values
        |> List.split in
      (match List.filter_map Fun.id bindings with
      | [] -> List values
      | bindings -> Let (bindings, List values))
  | Array values -> Array (List.map expression values)
  | Apply (fn, args) -> (
      match Semantic_ir.scoped_application fn args with
      | Some scoped -> expression scoped
      | None -> (
          let fn = expression fn in
          let args = List.map expression args in
          let bindings, fn, args = lift_lets fn args in
          lifted_expression bindings (Apply (fn, args))))
  | Uncurried_apply (fn, args) ->
      let fn = expression fn in
      let args = List.map expression args in
      let bindings, fn, args = lift_lets fn args in
      lifted_expression bindings (Uncurried_apply (fn, args))
  | Labelled_apply (fn, args) ->
      let fn = expression fn in
      let labels, args = List.split args in
      let args = List.map expression args in
      let bindings, fn, args = lift_lets fn args in
      lifted_expression bindings (Labelled_apply (fn, List.combine labels args))
  | If (condition, then_expr, else_expr) -> (
      match collapse_identity_lets (expression condition) with
      | Let (bindings, condition) when liftable_bindings bindings ->
          Let
            ( bindings,
              If (condition, expression then_expr, expression else_expr) )
      | condition -> If (condition, expression then_expr, expression else_expr))
  | Fun (patterns, body) -> Fun (List.map pattern patterns, expression body)
  | Labelled_fun (patterns, body) ->
      Labelled_fun (List.map (fun (label, value) -> label, pattern value) patterns,
                    expression body)
  | Sequence values -> Sequence (List.map expression values)
  | Let (bindings, body) -> (
      match Semantic_ir.scoped_let bindings body with
      | Some scoped -> expression scoped
      | None ->
          collapse_identity_lets
            (Let
               ( List.map
                   (fun (pat, value) -> (pattern pat, expression value))
                   bindings,
                 expression body )))
  | EvaluateOnce (name, value, body) ->
      Let
        ( [
            ( PConstraint
                (PVar name, "Lg_runtime.Runtime_dynamic.t"),
              expression value );
          ],
          expression body )
  | LetRec (name, params, body, args) ->
      LetRec
        (name, List.map pattern params, expression body, List.map expression args)
  | LetRecIn (name, params, body, next) ->
      LetRecIn
        (name, List.map pattern params, expression body, expression next)
  | LetRecGroup (bindings, body) ->
      LetRecGroup
        (List.map (fun (pat, value) -> (pattern pat, expression value)) bindings,
         expression body)
  | PackModule (name, signature) -> PackModule (name, signature)
  | UnpackModule (name, signature, value, body) ->
      UnpackModule (name, signature, expression value, expression body)
  | Match (target, cases) -> (
      let cases =
        List.map (fun (pat, body) -> (pattern pat, expression body)) cases
      in
      match collapse_identity_lets (expression target) with
      | Let (bindings, target) when liftable_bindings bindings ->
          Let (bindings, Match (target, cases))
      | target -> Match (target, cases))
  | Match_guarded (target, cases) -> (
      let cases =
        List.map
          (fun (pat, guard, body) ->
            (pattern pat, Option.map expression guard, expression body))
          cases
      in
      match collapse_identity_lets (expression target) with
      | Let (bindings, target) when liftable_bindings bindings ->
          Let (bindings, Match_guarded (target, cases))
      | target -> Match_guarded (target, cases))
  | Try (body, cases) ->
      Try
        ( expression body,
          List.map
            (fun (pat, guard, handler) ->
              (pattern pat, Option.map expression guard, expression handler))
            cases )
  | Infix (operator, left, right) ->
      Infix (operator, expression left, expression right)
  | Prefix (operator, value) -> Prefix (operator, expression value)
  | Constraint (value, type_name) -> Constraint (expression value, type_name)
  | Field (target, name) -> Field (expression target, name)
  | SetField (target, name, value) ->
      SetField (expression target, name, expression value)
  | Cons (head, tail) -> Cons (expression head, expression tail)
  | Record (fields, type_name) ->
      Record
        (List.map (fun (name, value) -> (name, expression value)) fields, type_name)
  | RecordUpdate (record, fields) ->
      RecordUpdate
        ( expression record,
          List.map (fun (name, value) -> (name, expression value)) fields )
  | SharedValue (_, value) -> expression value
  | PackDynamic { conversion; _ }
  | UnpackDynamic { conversion; _ }
  | NullableToSeq { conversion; _ } ->
      expression conversion

(* `collapse_identity_lets` runs on every lowered subexpression so identity
   temporaries fold regardless of which construct produced them. *)
and expression value =
  collapse_identity_lets (simplify_temp_lets (lower_node value))
