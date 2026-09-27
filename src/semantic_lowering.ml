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

(* Globally unique names for list-element temporaries, so bindings lifted
   out of sibling arguments can never capture each other. *)
let list_value_counter = ref 0

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

let lift_lets fn args =
  let fn_bindings, fn = strip_lets fn in
  let arg_bindings, args =
    List.fold_right
      (fun arg (bindings, args) ->
        let lifted, arg = strip_lets arg in
        (lifted @ bindings, arg :: args))
      args ([], [])
  in
  let bindings = fn_bindings @ arg_bindings in
  if bindings <> [] && liftable_bindings bindings then
    Some (bindings, fn, args)
  else None

let rec expression = function
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
      let bindings, values =
        List.mapi (fun index value ->
          if stable value then None, expression value
          else
            let name =
              incr list_value_counter;
              "__lg_list_value'" ^ string_of_int index ^ "_"
              ^ string_of_int !list_value_counter
            in
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
          match lift_lets fn args with
          | Some (bindings, fn, args) -> Let (bindings, Apply (fn, args))
          | None -> Apply (fn, args)))
  | Uncurried_apply (fn, args) -> (
      let fn = expression fn in
      let args = List.map expression args in
      match lift_lets fn args with
      | Some (bindings, fn, args) ->
          Let (bindings, Uncurried_apply (fn, args))
      | None -> Uncurried_apply (fn, args))
  | Labelled_apply (fn, args) -> (
      let fn = expression fn in
      let labels, args = List.split args in
      let args = List.map expression args in
      match lift_lets fn args with
      | Some (bindings, fn, args) ->
          Let (bindings, Labelled_apply (fn, List.combine labels args))
      | None -> Labelled_apply (fn, List.combine labels args))
  | If (condition, then_expr, else_expr) -> (
      match expression condition with
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
          Let
            ( List.map
                (fun (pat, value) -> (pattern pat, expression value))
                bindings,
              expression body ))
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
      match expression target with
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
      match expression target with
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
