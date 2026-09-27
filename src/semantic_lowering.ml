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
      | None -> Apply (expression fn, List.map expression args))
  | Uncurried_apply (fn, args) ->
      Uncurried_apply (expression fn, List.map expression args)
  | Labelled_apply (fn, args) ->
      Labelled_apply
        (expression fn, List.map (fun (label, arg) -> (label, expression arg)) args)
  | If (condition, then_expr, else_expr) ->
      If (expression condition, expression then_expr, expression else_expr)
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
  | Match (target, cases) ->
      Match
        ( expression target,
          List.map (fun (pat, body) -> (pattern pat, expression body)) cases )
  | Match_guarded (target, cases) ->
      Match_guarded
        ( expression target,
          List.map
            (fun (pat, guard, body) ->
              (pattern pat, Option.map expression guard, expression body))
            cases )
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
