type pattern =
  | PLocated of Source_node_id.t * Location.t * pattern
  | PVar of string
  | PAny
  | PUnit
  | PInt of int
  | PInt64 of int64
  | PString of string
  | PBool of bool
  | PPolyTag of string * pattern option
  | PConstructor of string * pattern option
  | PTuple of pattern list
  | PList of pattern list
  | PCons of pattern * pattern
  | PRecord of (string * pattern) list
  | PAlias of pattern * string
  | POr of pattern * pattern
  | PConstraint of pattern * string
  | PTyped of pattern * Semantic_type.ty

type t =
  | GadtScope of t
  | Typed of Semantic_type.ty * t
  | Located of Source_node_id.t * Location.t * t
  | Int of int
  | Int64 of int64
  | Float of string
  | String of string
  | Char of char
  | Bool of bool
  | Unit
  | PolyTag of string * t option
  | Constructor of string * t option
  | Tuple of t list
  | Ident of string
  | List of t list
  | Array of t list
  | Apply of t * t list
  | Uncurried_apply of t * t list
  | Labelled_apply of t * (string option * t) list
  | If of t * t * t
  | Fun of pattern list * t
  | Labelled_fun of (Asttypes.arg_label * pattern) list * t
  | Sequence of t list
  | Let of (pattern * t) list * t
  | EvaluateOnce of string * t * t
  | LetRec of string * pattern list * t * t list
  | LetRecIn of string * pattern list * t * t
  | LetRecGroup of (pattern * t) list * t
  | PackModule of string * string
  | UnpackModule of string * string * t * t
  | Match of t * (pattern * t) list
  | Match_guarded of t * (pattern * t option * t) list
  | Try of t * (pattern * t option * t) list
  | Infix of string * t * t
  | Prefix of string * t
  | Constraint of t * string
  | Field of t * string
  | SetField of t * string * t
  | Cons of t * t
  | Record of (string * t) list * string option
  | RecordUpdate of t * (string * t) list
  | SharedValue of string * t
  | PackDynamic of {
      source_ty : Semantic_type.ty;
      target_ty : Semantic_type.ty;
      conversion : t;
    }
  | UnpackDynamic of {
      source_ty : Semantic_type.ty;
      target_ty : Semantic_type.ty;
      conversion : t;
    }
  | NullableToSeq of {
      source_ty : Semantic_type.ty;
      element_ty : Semantic_type.ty;
      conversion : t;
    }

let rec continue_inside_conversion conversion continue =
  match conversion with
  | Located (node_id, location, value) ->
      Located
        (node_id, location, continue_inside_conversion value continue)
  | Typed (_, value) -> continue_inside_conversion value continue
  | Match (target, cases) ->
      Match
        ( target,
          List.map
            (fun (pattern, body) -> (pattern, continue body))
            cases )
  | value -> continue value

let scoped_application fn arguments =
  let rec build prefix = function
    | [] -> None
    | UnpackDynamic
        { target_ty = Semantic_type.TNamed_record _; conversion; _ }
      :: rest ->
        Some
          (continue_inside_conversion conversion (fun unpacked ->
               let arguments = List.rev_append prefix (unpacked :: rest) in
               match build [] arguments with
               | Some scoped -> scoped
               | None -> Apply (fn, arguments)))
    | argument :: rest -> build (argument :: prefix) rest
  in
  build [] arguments

let scoped_let bindings body =
  let rec scoped_value = function
    | Located (node_id, location, value) ->
        Option.map
          (fun value -> Located (node_id, location, value))
          (scoped_value value)
    | Typed (_, value) -> scoped_value value
    | UnpackDynamic
        { target_ty = Semantic_type.TNamed_record _; conversion; _ } ->
        Some conversion
    | Apply (fn, arguments) -> scoped_application fn arguments
    | _ -> None
  in
  let rec build prefix = function
    | [] -> None
    | (pattern, value) :: rest -> (
        match scoped_value value with
        | None -> build ((pattern, value) :: prefix) rest
        | Some scoped ->
            let inner =
              continue_inside_conversion scoped (fun value ->
                  Let ((pattern, value) :: rest, body))
            in
            Some
              (match List.rev prefix with
              | [] -> inner
              | bindings -> Let (bindings, inner)))
  in
  build [] bindings

let rec unlocated = function
  | Typed (_, expression) -> unlocated expression
  | Located (_, _, expression) -> unlocated expression
  | PackDynamic { conversion; _ }
  | UnpackDynamic { conversion; _ }
  | NullableToSeq { conversion; _ } ->
      unlocated conversion
  | expression -> expression

let rec evaluate_for_effect expression =
  match unlocated expression with
  | Record (fields, _) ->
      Sequence
        (List.map
           (fun (_, value) -> evaluate_for_effect value)
           fields
        @ [ Unit ])
  | _ -> expression

let rec never_returns = function
  | Typed (_, expression)
  | GadtScope expression
  | Located (_, _, expression)
  | Constraint (expression, _)
  | SharedValue (_, expression)
  | PackDynamic { conversion = expression; _ }
  | UnpackDynamic { conversion = expression; _ }
  | NullableToSeq { conversion = expression; _ } ->
      never_returns expression
  | Apply (fn, [ _ ]) -> (
      match unlocated fn with
      | Ident "raise" | Ident "Lg_runtime.Runtime_exception.throw" -> true
      | _ -> false)
  | Labelled_apply (Ident "Fun.protect", arguments) ->
      List.exists
        (function
          | None, Fun ([ PUnit ], body) -> never_returns body
          | _ -> false)
        arguments
  | Sequence expressions -> List.exists never_returns expressions
  | Match (value, cases) ->
      never_returns value
      || (cases <> [] && List.for_all (fun (_, body) -> never_returns body) cases)
  | Match_guarded (value, cases) ->
      never_returns value
      || (cases <> [] && List.for_all (fun (_, _, body) -> never_returns body) cases)
  | Try (body, handlers) ->
      never_returns body
      && List.for_all (fun (_, _, handler) -> never_returns handler) handlers
  | Let (bindings, body) ->
      List.exists (fun (_, value) -> never_returns value) bindings
      || never_returns body
  | EvaluateOnce (_, value, body) ->
      never_returns value || never_returns body
  | LetRecIn (_, _, _, body) | LetRecGroup (_, body) -> never_returns body
  | UnpackModule (_, _, value, body) -> never_returns value || never_returns body
  | _ -> false

(* Pure by construction: safe to duplicate, reorder, or drop without an
   evaluation-order binding. Conservatively rejects anything not listed. *)
let rec is_stable = function
  | Located (_, _, value) | Typed (_, value) | GadtScope value -> is_stable value
  | Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit | Ident _ ->
      true
  | PolyTag (_, value) | Constructor (_, value) ->
      Option.fold ~none:true ~some:is_stable value
  | Tuple values | List values | Array values -> List.for_all is_stable values
  | Record (fields, _) ->
      List.for_all (fun (_, value) -> is_stable value) fields
  | Field (value, _) | Constraint (value, _) | Prefix (_, value) ->
      is_stable value
  | Fun _ | Labelled_fun _ -> true
  | _ -> false

let annotate ty = function
  | Typed (_, expression) -> Typed (ty, expression)
  | expression -> Typed (ty, expression)

let rec type_annotations expression =
  let children = function
    | GadtScope value | Typed (_, value) | Located (_, _, value) | SharedValue (_, value) ->
        [ value ]
    | PolyTag (_, value) | Constructor (_, value) -> Option.to_list value
    | Tuple values | List values | Array values | Sequence values -> values
    | Apply (fn, args) | Uncurried_apply (fn, args) -> fn :: args
    | Labelled_apply (fn, args) -> fn :: List.map snd args
    | If (condition, then_expr, else_expr) -> [ condition; then_expr; else_expr ]
    | Fun (_, body) | Labelled_fun (_, body) -> [ body ]
    | Let (bindings, body) | LetRecGroup (bindings, body) ->
        List.map snd bindings @ [ body ]
    | EvaluateOnce (_, value, body) -> [ value; body; value ]
    | LetRec (_, _, body, args) -> body :: args
    | LetRecIn (_, _, body, next) -> [ body; next ]
    | UnpackModule (_, _, value, body) -> [value; body]
    | PackModule _ -> []
    | Match (target, cases) -> target :: List.map snd cases
    | Match_guarded (target, cases) ->
        target
        :: List.concat_map
             (fun (_, guard, body) -> Option.to_list guard @ [ body ])
             cases
    | Try (body, cases) ->
        body
        :: List.concat_map
             (fun (_, guard, handler) -> Option.to_list guard @ [ handler ])
             cases
    | Infix (_, left, right) | Cons (left, right) -> [ left; right ]
    | Prefix (_, value) | Constraint (value, _) | Field (value, _)
    | PackDynamic { conversion = value; _ }
    | UnpackDynamic { conversion = value; _ }
    | NullableToSeq { conversion = value; _ } ->
        [ value ]
    | SetField (target, _, value) -> [ target; value ]
    | Record (fields, _) -> List.map snd fields
    | RecordUpdate (record, fields) -> record :: List.map snd fields
    | Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit | Ident _ -> []
  in
  let own =
    match expression with
    | Typed (ty, _) -> [ ty ]
    | PackDynamic { source_ty; target_ty; _ }
    | UnpackDynamic { source_ty; target_ty; _ } ->
        [ source_ty; target_ty ]
    | NullableToSeq { source_ty; element_ty; _ } ->
        [ source_ty; Semantic_type.TSeq element_ty ]
    | _ -> []
  in
  own @ List.concat_map type_annotations (children expression)

let rec rewrite fn expression =
  let rewrite_pattern_case (pattern, body) = (pattern, rewrite fn body) in
  let rewrite_guarded_case (pattern, guard, body) =
    (pattern, Option.map (rewrite fn) guard, rewrite fn body)
  in
  let expression =
    match expression with
    | Typed (ty, value) -> Typed (ty, rewrite fn value)
    | GadtScope value -> GadtScope (rewrite fn value)
    | Located (node_id, location, value) ->
        Located (node_id, location, rewrite fn value)
    | PolyTag (name, value) -> PolyTag (name, Option.map (rewrite fn) value)
    | Constructor (name, value) ->
        Constructor (name, Option.map (rewrite fn) value)
    | Tuple values -> Tuple (List.map (rewrite fn) values)
    | List values -> List (List.map (rewrite fn) values)
    | Array values -> Array (List.map (rewrite fn) values)
    | Apply (callee, arguments) ->
        Apply (rewrite fn callee, List.map (rewrite fn) arguments)
    | Uncurried_apply (callee, arguments) ->
        Uncurried_apply (rewrite fn callee, List.map (rewrite fn) arguments)
    | Labelled_apply (callee, arguments) ->
        Labelled_apply
          ( rewrite fn callee,
            List.map (fun (label, value) -> (label, rewrite fn value)) arguments )
    | If (condition, then_expr, else_expr) ->
        If
          ( rewrite fn condition,
            rewrite fn then_expr,
            rewrite fn else_expr )
    | Fun (patterns, body) -> Fun (patterns, rewrite fn body)
    | Labelled_fun (patterns, body) -> Labelled_fun (patterns, rewrite fn body)
    | Sequence values -> Sequence (List.map (rewrite fn) values)
    | Let (bindings, body) ->
        Let
          ( List.map
              (fun (pattern, value) -> (pattern, rewrite fn value))
              bindings,
            rewrite fn body )
    | EvaluateOnce (name, value, body) ->
        EvaluateOnce (name, rewrite fn value, rewrite fn body)
    | LetRec (name, patterns, body, arguments) ->
        LetRec
          ( name,
            patterns,
            rewrite fn body,
            List.map (rewrite fn) arguments )
    | LetRecIn (name, patterns, body, next) ->
        LetRecIn (name, patterns, rewrite fn body, rewrite fn next)
    | LetRecGroup (bindings, body) ->
        LetRecGroup
          (List.map (fun (pattern, value) -> (pattern, rewrite fn value)) bindings,
           rewrite fn body)
    | PackModule _ as expression -> expression
    | UnpackModule (name, signature, value, body) ->
        UnpackModule (name, signature, rewrite fn value, rewrite fn body)
    | Match (target, cases) ->
        Match (rewrite fn target, List.map rewrite_pattern_case cases)
    | Match_guarded (target, cases) ->
        Match_guarded
          (rewrite fn target, List.map rewrite_guarded_case cases)
    | Try (body, cases) ->
        Try (rewrite fn body, List.map rewrite_guarded_case cases)
    | Infix (operator, left, right) ->
        Infix (operator, rewrite fn left, rewrite fn right)
    | Prefix (operator, value) -> Prefix (operator, rewrite fn value)
    | Constraint (value, type_name) ->
        Constraint (rewrite fn value, type_name)
    | Field (value, field) -> Field (rewrite fn value, field)
    | SetField (target, field, value) ->
        SetField (rewrite fn target, field, rewrite fn value)
    | Cons (head, tail) -> Cons (rewrite fn head, rewrite fn tail)
    | Record (fields, type_name) ->
        Record
          ( List.map (fun (name, value) -> (name, rewrite fn value)) fields,
            type_name )
    | RecordUpdate (record, fields) ->
        RecordUpdate
          ( rewrite fn record,
            List.map (fun (name, value) -> (name, rewrite fn value)) fields )
    | SharedValue (name, value) -> SharedValue (name, rewrite fn value)
    | PackDynamic conversion ->
        PackDynamic
          { conversion with conversion = rewrite fn conversion.conversion }
    | UnpackDynamic conversion ->
        UnpackDynamic
          { conversion with conversion = rewrite fn conversion.conversion }
    | NullableToSeq conversion ->
        NullableToSeq
          { conversion with conversion = rewrite fn conversion.conversion }
    | (Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit | Ident _) as value ->
        value
  in
  fn expression

let rec exists_identifier predicate expression =
  let children =
    match expression with
    | GadtScope value | Typed (_, value) | Located (_, _, value) | SharedValue (_, value) ->
        [ value ]
    | PolyTag (_, value) | Constructor (_, value) -> Option.to_list value
    | Tuple values | List values | Array values | Sequence values -> values
    | Apply (fn, args) | Uncurried_apply (fn, args) -> fn :: args
    | Labelled_apply (fn, args) -> fn :: List.map snd args
    | If (condition, then_expr, else_expr) ->
        [ condition; then_expr; else_expr ]
    | Fun (_, body) | Labelled_fun (_, body) -> [ body ]
    | Let (bindings, body) | LetRecGroup (bindings, body) ->
        List.map snd bindings @ [ body ]
    | EvaluateOnce (_, value, body) -> [ value; body; value ]
    | LetRec (_, _, body, args) -> body :: args
    | LetRecIn (_, _, body, next) -> [ body; next ]
    | UnpackModule (_, _, value, body) -> [value; body]
    | PackModule _ -> []
    | Match (target, cases) -> target :: List.map snd cases
    | Match_guarded (target, cases) ->
        target
        :: List.concat_map
             (fun (_, guard, body) -> Option.to_list guard @ [ body ])
             cases
    | Try (body, cases) ->
        body
        :: List.concat_map
             (fun (_, guard, handler) -> Option.to_list guard @ [ handler ])
             cases
    | Infix (_, left, right) | Cons (left, right) -> [ left; right ]
    | Prefix (_, value) | Constraint (value, _) | Field (value, _)
    | PackDynamic { conversion = value; _ }
    | UnpackDynamic { conversion = value; _ }
    | NullableToSeq { conversion = value; _ } ->
        [ value ]
    | SetField (target, _, value) -> [ target; value ]
    | Record (fields, _) -> List.map snd fields
    | RecordUpdate (record, fields) -> record :: List.map snd fields
    | Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit | Ident _ -> []
  in
  match expression with
  | Ident name when predicate name -> true
  | _ -> List.exists (exists_identifier predicate) children
