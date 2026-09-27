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

type t =
  | GadtScope of t
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

let rec unlocated = function
  | Located (_, _, expression) -> unlocated expression
  | expression -> expression

let rec pattern_to_source = function
  | PLocated (_, _, pattern) -> pattern_to_source pattern
  | PVar name -> name
  | PAny -> "_"
  | PUnit -> "()"
  | PInt value -> string_of_int value
  | PInt64 value -> Int64.to_string value ^ "L"
  | PString value -> Printf.sprintf "%S" value
  | PBool value -> string_of_bool value
  | PPolyTag (name, None) -> "`" ^ name
  | PPolyTag (name, Some value) -> "`" ^ name ^ " (" ^ pattern_to_source value ^ ")"
  | PConstructor (name, None) -> name
  | PConstructor (name, Some pattern) -> name ^ " " ^ pattern_to_source pattern
  | PTuple patterns ->
      "(" ^ (patterns |> List.map pattern_to_source |> String.concat ", ") ^ ")"
  | PList patterns ->
      "[" ^ (patterns |> List.map pattern_to_source |> String.concat "; ") ^ "]"
  | PCons (head, tail) -> pattern_to_source head ^ " :: " ^ pattern_to_source tail
  | PRecord fields ->
      "{"
      ^ (fields
        |> List.map (fun (name, pattern) -> name ^ " = " ^ pattern_to_source pattern)
        |> String.concat "; ")
      ^ "; _}"
  | PAlias (pattern, name) -> "(" ^ pattern_to_source pattern ^ " as " ^ name ^ ")"
  | POr (left, right) -> "(" ^ pattern_to_source left ^ " | " ^ pattern_to_source right ^ ")"
  | PConstraint (pattern, type_name) ->
      "(" ^ pattern_to_source pattern ^ " : " ^ type_name ^ ")"

let rec to_source = function
  | GadtScope expression | Located (_, _, expression) -> to_source expression
  | Int value -> string_of_int value
  | Int64 value -> Int64.to_string value ^ "L"
  | Float value -> value
  | String value -> Printf.sprintf "%S" value
  | Char value -> Printf.sprintf "%C" value
  | Bool value -> string_of_bool value
  | Unit -> "()"
  | PolyTag (name, None) -> "`" ^ name
  | PolyTag (name, Some value) -> "`" ^ name ^ " (" ^ to_source value ^ ")"
  | Constructor (name, None) -> name
  | Constructor (name, Some value) -> name ^ " (" ^ to_source value ^ ")"
  | Tuple values ->
      "(" ^ (values |> List.map to_source |> String.concat ", ") ^ ")"
  | Ident name -> name
  | List values ->
      "[" ^ (values |> List.map to_source |> String.concat "; ") ^ "]"
  | Array values ->
      "[|" ^ (values |> List.map to_source |> String.concat "; ") ^ "|]"
  | Apply (fn, args) ->
      let args = match args with [] -> [ Unit ] | _ -> args in
      "("
      ^ to_source fn
      ^ " "
      ^ (args |> List.map (fun arg -> "(" ^ to_source arg ^ ")") |> String.concat " ")
      ^ ")"
  | Uncurried_apply (fn, args) ->
      "(("
      ^ to_source fn
      ^ " "
      ^ (args |> List.map (fun arg -> "(" ^ to_source arg ^ ")") |> String.concat " ")
      ^ ")[@u])"
  | Labelled_apply (fn, args) ->
      let argument_source = function
        | None, argument -> "(" ^ to_source argument ^ ")"
        | Some label, argument -> "~" ^ label ^ ":(" ^ to_source argument ^ ")"
      in
      "(" ^ to_source fn ^ " "
      ^ (args |> List.map argument_source |> String.concat " ")
      ^ ")"
  | If (condition, then_expr, else_expr) ->
      "(if " ^ to_source condition ^ " then " ^ to_source then_expr ^ " else "
      ^ to_source else_expr ^ ")"
  | Fun (patterns, body) ->
      let patterns = match patterns with [] -> [ PUnit ] | _ -> patterns in
      "(fun "
      ^ (patterns |> List.map pattern_to_source |> String.concat " ")
      ^ " -> " ^ to_source body ^ ")"
  | Labelled_fun (patterns, body) ->
      let parameter (label, pattern) =
        let prefix = match label with
          | Asttypes.Nolabel -> ""
          | Labelled name -> "~" ^ name ^ ":"
          | Optional name -> "?" ^ name ^ ":" in
        prefix ^ pattern_to_source pattern in
      "(fun " ^ String.concat " " (List.map parameter patterns)
      ^ " -> " ^ to_source body ^ ")"
  | Sequence expressions -> (
      match expressions with
      | [] -> "()"
      | [ expression ] -> to_source expression
      | expression :: rest ->
          "(let __lg_discarded_value = " ^ to_source expression
          ^ " in let _ = Stdlib.ignore __lg_discarded_value in "
          ^ to_source (Sequence rest) ^ ")")
  | Let (bindings, body) ->
      List.fold_right
        (fun (pattern, value) acc ->
          "(let " ^ pattern_to_source pattern ^ " = " ^ to_source value
          ^ " in " ^ acc ^ ")")
        bindings (to_source body)
  | LetRec (name, params, body, args) ->
      let params = match params with [] -> [ PUnit ] | _ -> params in
      "(let rec " ^ name ^ " "
      ^ (params |> List.map pattern_to_source |> String.concat " ")
      ^ " = " ^ to_source body ^ " in "
      ^ to_source (Apply (Ident name, args)) ^ ")"
  | LetRecIn (name, params, body, next) ->
      let params = match params with [] -> [ PUnit ] | _ -> params in
      "(let rec " ^ name ^ " "
      ^ (params |> List.map pattern_to_source |> String.concat " ")
      ^ " = " ^ to_source body ^ " in " ^ to_source next ^ ")"
  | LetRecGroup (bindings, body) ->
      "(let rec "
      ^ String.concat " and "
          (List.map (fun (pattern, value) ->
             pattern_to_source pattern ^ " = " ^ to_source value) bindings)
      ^ " in " ^ to_source body ^ ")"
  | PackModule (name, signature) -> "(module " ^ name ^ " : " ^ signature ^ ")"
  | UnpackModule (name, signature, value, body) ->
      "(let module " ^ name ^ " = (val " ^ to_source value ^ " : " ^ signature
      ^ ") in " ^ to_source body ^ ")"
  | Match (target, cases) ->
      "(match " ^ to_source target ^ " with "
      ^ (cases
        |> List.map (fun (pattern, body) ->
               "| " ^ pattern_to_source pattern ^ " -> " ^ to_source body)
        |> String.concat " ")
      ^ ")"
  | Match_guarded (target, cases) ->
      "(match " ^ to_source target ^ " with "
      ^ (cases
        |> List.map (fun (pattern, guard, body) ->
               "| " ^ pattern_to_source pattern
               ^ (match guard with None -> "" | Some guard -> " when " ^ to_source guard)
               ^ " -> " ^ to_source body)
        |> String.concat " ")
      ^ ")"
  | Try (body, cases) ->
      "(try " ^ to_source body ^ " with "
      ^ (cases
        |> List.map (fun (pattern, guard, handler) ->
               "| " ^ pattern_to_source pattern
               ^ (match guard with None -> "" | Some guard -> " when " ^ to_source guard)
               ^ " -> " ^ to_source handler)
        |> String.concat " ")
      ^ ")"
  | Infix (operator, left, right) ->
      "(" ^ to_source left ^ " " ^ operator ^ " " ^ to_source right ^ ")"
  | Prefix (operator, expression) ->
      "(" ^ operator ^ " " ^ to_source expression ^ ")"
  | Constraint (expression, type_name) ->
      "(" ^ to_source expression ^ " : " ^ type_name ^ ")"
  | Field (target, field_name) -> to_source target ^ "." ^ field_name
  | SetField (target, field_name, value) ->
      "(" ^ to_source target ^ "." ^ field_name ^ " <- " ^ to_source value
      ^ ")"
  | Cons (head, tail) -> "(" ^ to_source head ^ " :: " ^ to_source tail ^ ")"
  | Record (fields, type_name) ->
      let fields =
        fields
        |> List.map (fun (name, value) -> name ^ " = " ^ to_source value)
        |> String.concat "; "
      in
      let value = "{" ^ fields ^ "}" in
      (match type_name with
      | None -> value
      | Some name ->
          "((fun (__lg_record_value : " ^ name
          ^ ") -> __lg_record_value) " ^ value ^ ")")
  | RecordUpdate (record, fields) ->
      let fields =
        fields
        |> List.map (fun (name, value) -> name ^ " = " ^ to_source value)
        |> String.concat "; "
      in
      "{" ^ to_source record ^ " with " ^ fields ^ "}"

let loc = Location.none

let rec compact_longident = function
  | Longident.Lident name -> Longident.Lident (Names.compact_generated_name name)
  | Longident.Ldot (path, name) ->
      Longident.Ldot
        ( { path with txt = compact_longident path.txt },
          { name with txt = Names.compact_generated_name name.txt } )
  | Longident.Lapply (fn, argument) ->
      Longident.Lapply
        ( { fn with txt = compact_longident fn.txt },
          { argument with txt = compact_longident argument.txt } )

let lid value = Location.mkloc (compact_longident value) loc
let str value = Location.mkloc (Names.compact_generated_name value) loc

let longident_of_string name =
  let name = Names.compact_runtime_path name in
  match String.split_on_char '.' name with
  | [] -> Longident.Lident name
  | first :: rest ->
      List.fold_left
        (fun path segment ->
          Longident.Ldot (lid path, str segment))
        (Longident.Lident first) rest

let core_type_of_source source =
  let source =
    source |> Names.compact_runtime_source |> Names.compact_generated_source
  in
  let lexbuf = Lexing.from_string source in
  Location.init lexbuf ("generated type " ^ source);
  try Parse.core_type lexbuf
  with _ -> Ast_helper.Typ.constr ~loc (lid (longident_of_string source)) []

let string_attribute name value =
  let payload =
    Parsetree.PStr
      [ Ast_helper.Str.eval
          (Ast_helper.Exp.constant (Ast_helper.Const.string value)) ]
  in
  Ast_helper.Attr.mk (str name) payload

let source_attributes node_id =
  string_attribute "lg.node_id" (Source_node_id.to_string node_id)
  :: (Source_node_id.origins node_id
     |> List.map (fun origin ->
            string_attribute "lg.origin"
              (Source_node_id.origin_to_string origin)))

let rec pattern_node_ids = function
  | PLocated (node_id, _, pattern) -> node_id :: pattern_node_ids pattern
  | PPolyTag (_, payload) | PConstructor (_, payload) ->
      Option.fold ~none:[] ~some:pattern_node_ids payload
  | PTuple patterns | PList patterns -> List.concat_map pattern_node_ids patterns
  | PCons (head, tail) | POr (head, tail) ->
      pattern_node_ids head @ pattern_node_ids tail
  | PRecord fields ->
      fields |> List.concat_map (fun (_, pattern) -> pattern_node_ids pattern)
  | PAlias (pattern, _) | PConstraint (pattern, _) -> pattern_node_ids pattern
  | PVar _ | PAny | PUnit | PInt _ | PInt64 _ | PString _ | PBool _ -> []

let add_pattern_node_ids patterns (expression : Parsetree.expression) =
  let attributes =
    patterns |> List.concat_map pattern_node_ids |> List.concat_map source_attributes
  in
  { expression with pexp_attributes = attributes @ expression.pexp_attributes }

let rec pattern_to_parsetree = function
  | PLocated (node_id, location, pattern) ->
      let pattern : Parsetree.pattern = pattern_to_parsetree pattern in
      {
        pattern with
        ppat_loc = location;
        ppat_attributes = source_attributes node_id @ pattern.ppat_attributes;
      }
  | PVar name -> Ast_helper.Pat.var ~loc (str name)
  | PAny -> Ast_helper.Pat.any ~loc ()
  | PUnit -> Ast_helper.Pat.construct ~loc (lid (Longident.Lident "()")) None
  | PInt value -> Ast_helper.Pat.constant ~loc (Ast_helper.Const.int ~loc value)
  | PInt64 value ->
      Ast_helper.Pat.constant ~loc
        (Ast_helper.Const.int64 ~loc value)
  | PString value ->
      Ast_helper.Pat.constant ~loc (Ast_helper.Const.string ~loc value)
  | PBool value ->
      Ast_helper.Pat.construct ~loc
        (lid (Longident.Lident (string_of_bool value)))
        None
  | PPolyTag (name, payload) -> Ast_helper.Pat.variant ~loc name (Option.map pattern_to_parsetree payload)
  | PConstructor (name, None) ->
      Ast_helper.Pat.construct ~loc (lid (longident_of_string name)) None
  | PConstructor (name, Some pattern) ->
      Ast_helper.Pat.construct ~loc (lid (longident_of_string name))
        (Some ([], pattern_to_parsetree pattern))
  | PTuple patterns ->
      Ast_helper.Pat.tuple ~loc
        (List.map (fun pattern -> (None, pattern_to_parsetree pattern)) patterns)
        Closed
  | PList patterns -> pattern_list_to_parsetree patterns
  | PCons (head, tail) ->
      let pair =
        Ast_helper.Pat.tuple ~loc
          [ (None, pattern_to_parsetree head); (None, pattern_to_parsetree tail) ]
          Closed
      in
      Ast_helper.Pat.construct ~loc (lid (Longident.Lident "::")) (Some ([], pair))
  | PRecord fields ->
      Ast_helper.Pat.record ~loc
        (List.map
           (fun (name, pattern) ->
             (lid (longident_of_string name), pattern_to_parsetree pattern))
           fields)
        Asttypes.Open
  | PAlias (pattern, name) ->
      Ast_helper.Pat.alias ~loc (pattern_to_parsetree pattern) (str name)
  | POr (left, right) ->
      Ast_helper.Pat.or_ ~loc (pattern_to_parsetree left) (pattern_to_parsetree right)
  | PConstraint (pattern, type_name) ->
      Ast_helper.Pat.constraint_ ~loc (pattern_to_parsetree pattern)
        (core_type_of_source type_name)

and pattern_list_to_parsetree = function
  | [] -> Ast_helper.Pat.construct ~loc (lid (Longident.Lident "[]")) None
  | pattern :: rest ->
      let pair =
        Ast_helper.Pat.tuple ~loc
          [ (None, pattern_to_parsetree pattern); (None, pattern_list_to_parsetree rest) ]
          Closed
      in
      Ast_helper.Pat.construct ~loc (lid (Longident.Lident "::")) (Some ([], pair))

let function_parameter pattern =
  {
    Parsetree.pparam_loc = loc;
    pparam_desc = Pparam_val (Asttypes.Nolabel, None, pattern_to_parsetree pattern);
  }

let rec list_to_parsetree ~context = function
  | [] ->
      Ok
        (Ast_helper.Exp.construct ~loc (lid (Longident.Lident "[]")) None)
  | value :: rest -> (
      match (to_parsetree ~context value, list_to_parsetree ~context rest) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok value, Ok rest ->
          let pair = Ast_helper.Exp.tuple ~loc [ (None, value); (None, rest) ] in
          Ok
            (Ast_helper.Exp.construct ~loc
               (lid (Longident.Lident "::"))
               (Some pair)))

and expressions_to_parsetree ~context expressions =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | expression :: rest -> (
        match to_parsetree ~context expression with
        | Error _ as err -> err
        | Ok expression -> loop (expression :: acc) rest)
  in
  loop [] expressions

and guarded_cases_to_parsetree ~context cases =
  let rec build_cases acc = function
    | [] -> Ok (List.rev acc)
    | (pattern, guard, body) :: rest -> (
        match
          ( Option.fold ~none:(Ok None)
              ~some:(fun guard ->
                to_parsetree ~context guard |> Result.map Option.some)
              guard,
            to_parsetree ~context body )
        with
        | (Error _ as err), _ -> err
        | _, (Error _ as err) -> err
        | Ok guard, Ok body ->
            build_cases
              (Ast_helper.Exp.case (pattern_to_parsetree pattern) ?guard body :: acc)
              rest)
  in
  build_cases [] cases

and to_parsetree ~context = function
  | GadtScope expression ->
      Result.map (fun expression ->
        {expression with Parsetree.pexp_attributes =
          Ast_helper.Attr.mk (Location.mknoloc "lg.gadt_scope") (Parsetree.PStr [])
          :: expression.Parsetree.pexp_attributes}) (to_parsetree ~context expression)
  | Located (node_id, location, expression) ->
      to_parsetree ~context expression
      |> Result.map (fun (expression : Parsetree.expression) ->
             let rec locate (expression : Parsetree.expression) =
               let pexp_desc =
                 match expression.pexp_desc with
                 | Parsetree.Pexp_constraint (inner, ty) when inner.pexp_loc = Location.none ->
                     Parsetree.Pexp_constraint (locate inner, ty)
                 | desc -> desc
               in
               { expression with pexp_desc; pexp_loc = location }
             in
             let expression = locate expression in
             {
               expression with
               pexp_attributes =
                 source_attributes node_id @ expression.pexp_attributes;
             })
  | Int value ->
      Ok (Ast_helper.Exp.constant ~loc (Ast_helper.Const.int ~loc value))
  | Int64 value ->
      Ok (Ast_helper.Exp.constant ~loc (Ast_helper.Const.int64 ~loc value))
  | Float value ->
      Ok (Ast_helper.Exp.constant ~loc (Ast_helper.Const.float ~loc value))
  | String value ->
      Ok (Ast_helper.Exp.constant ~loc (Ast_helper.Const.string ~loc value))
  | Char value ->
      Ok (Ast_helper.Exp.constant ~loc (Ast_helper.Const.char ~loc value))
  | Bool value ->
      Ok
        (Ast_helper.Exp.construct ~loc
           (lid (Longident.Lident (string_of_bool value)))
           None)
  | Unit ->
      Ok
        (Ast_helper.Exp.construct ~loc (lid (Longident.Lident "()")) None)
  | PolyTag (name, None) -> Ok (Ast_helper.Exp.variant ~loc name None)
  | PolyTag (name, Some payload) -> Result.map (fun payload -> Ast_helper.Exp.variant ~loc name (Some payload)) (to_parsetree ~context payload)
  | Constructor (name, None) ->
      Ok (Ast_helper.Exp.construct ~loc (lid (longident_of_string name)) None)
  | Constructor (name, Some value) -> (
      match to_parsetree ~context value with
      | Error _ as err -> err
      | Ok value ->
          Ok
            (Ast_helper.Exp.construct ~loc (lid (longident_of_string name))
               (Some value)))
  | Tuple values -> (
      match expressions_to_parsetree ~context values with
      | Error _ as err -> err
      | Ok values ->
          Ok
            (Ast_helper.Exp.tuple ~loc
               (List.map (fun value -> (None, value)) values)))
  | Ident name ->
      Ok (Ast_helper.Exp.ident ~loc (lid (longident_of_string name)))
  | List values -> list_to_parsetree ~context values
  | Array values -> (
      match expressions_to_parsetree ~context values with
      | Error _ as err -> err
      | Ok values -> Ok (Ast_helper.Exp.array ~loc values))
  | Apply (fn, args) -> (
      let args = match args with [] -> [ Unit ] | _ -> args in
      match (to_parsetree ~context fn, expressions_to_parsetree ~context args) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok fn, Ok args ->
          Ok
            (Ast_helper.Exp.apply ~loc fn
               (List.map (fun arg -> (Asttypes.Nolabel, arg)) args)))
  | Uncurried_apply (fn, args) -> (
      match (to_parsetree ~context fn, expressions_to_parsetree ~context args) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok fn, Ok args ->
          let type_var name = Ast_helper.Typ.var ~loc name in
          let function_type =
            Ast_helper.Typ.arrow ~loc Asttypes.Nolabel (type_var "left")
              (Ast_helper.Typ.arrow ~loc Asttypes.Nolabel (type_var "right")
                 (type_var "result"))
          in
          let uncurried_type =
            { function_type with
              ptyp_attributes =
                Ast_helper.Attr.mk (str "u") (PStr [])
                :: function_type.ptyp_attributes }
          in
          let fn =
            Ast_helper.Exp.constraint_ ~loc fn uncurried_type
          in
          let application =
            Ast_helper.Exp.apply ~loc fn
              (List.map (fun arg -> (Asttypes.Nolabel, arg)) args)
          in
          let attribute = Ast_helper.Attr.mk (str "u") (PStr []) in
          let application =
            { application with
              pexp_attributes = attribute :: application.pexp_attributes }
          in
          Ok application)
  | Labelled_apply (fn, args) -> (
      let rec arguments_to_parsetree acc = function
        | [] -> Ok (List.rev acc)
        | (label, argument) :: rest -> (
            match to_parsetree ~context argument with
            | Error _ as err -> err
            | Ok argument ->
                let label =
                  match label with
                  | None -> Asttypes.Nolabel
                  | Some label -> Asttypes.Labelled label
                in
                arguments_to_parsetree ((label, argument) :: acc) rest)
      in
      match (to_parsetree ~context fn, arguments_to_parsetree [] args) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok fn, Ok args -> Ok (Ast_helper.Exp.apply ~loc fn args))
  | If (condition, then_expr, else_expr) -> (
      match
        ( to_parsetree ~context condition,
          to_parsetree ~context then_expr,
          to_parsetree ~context else_expr )
      with
      | (Error _ as err), _, _ -> err
      | _, (Error _ as err), _ -> err
      | _, _, (Error _ as err) -> err
      | Ok condition, Ok then_expr, Ok else_expr ->
          Ok (Ast_helper.Exp.ifthenelse ~loc condition then_expr (Some else_expr)))
  | Fun (patterns, body) -> (
      let patterns = match patterns with [] -> [ PUnit ] | _ -> patterns in
      match to_parsetree ~context body with
      | Error _ as err -> err
      | Ok body ->
          Ok
            (add_pattern_node_ids patterns
               (Ast_helper.Exp.function_ ~loc
                  (List.map function_parameter patterns)
                  None (Pfunction_body body))))
  | Labelled_fun (patterns, body) -> (
      match to_parsetree ~context body with
      | Error _ as err -> err
      | Ok body ->
          let parameters = List.map (fun (label, pattern) ->
            { (function_parameter pattern) with
              pparam_desc = Pparam_val (label, None, pattern_to_parsetree pattern) }) patterns in
          Ok (add_pattern_node_ids (List.map snd patterns)
            (Ast_helper.Exp.function_ ~loc parameters None (Pfunction_body body))))
  | Sequence expressions -> (
      let rec discardable = function
        | GadtScope expression | Located (_, _, expression) | Constraint (expression, _) ->
            discardable expression
        | Int _ | Int64 _ | Float _ | String _ | Char _ | Bool _ | Unit
        | Ident _ | PolyTag (_, None) | Constructor (_, None) ->
            true
        | PolyTag (_, Some value) | Constructor (_, Some value) -> discardable value
        | Tuple values | List values | Array values ->
            List.for_all discardable values
        | Field (inner, _) -> discardable inner
        | Record (fields, _) ->
            List.for_all (fun (_, value) -> discardable value) fields
        | Fun _ | Labelled_fun _ -> true
        | Apply _ | Uncurried_apply _ | Labelled_apply _ | If _
        | Sequence _ | Let _ | LetRec _ | LetRecIn _ | LetRecGroup _ | PackModule _ | UnpackModule _ | Match _
        | Match_guarded _ | Try _ | Infix _ | Prefix _ | SetField _
        | Cons _
        | RecordUpdate _ ->
            false
      in
      let rec elide_discarded_pure_values = function
        | [] | [ _ ] as expressions -> expressions
        | expression :: rest when discardable expression ->
            elide_discarded_pure_values rest
        | expression :: rest ->
            expression :: elide_discarded_pure_values rest
      in
      let expressions = elide_discarded_pure_values expressions in
      let rec build = function
        | [] -> Ok (Ast_helper.Exp.construct ~loc (lid (Longident.Lident "()")) None)
        | [ expression ] -> to_parsetree ~context expression
        | expression :: rest -> (
            match (to_parsetree ~context expression, build rest) with
            | (Error _ as err), _ -> err
            | _, (Error _ as err) -> err
            | Ok expression, Ok body ->
                (* keep `ignore`: it suppresses warning 5 on discarded
                   partial applications *)
                let ignored =
                  Ast_helper.Exp.apply ~loc
                    (Ast_helper.Exp.ident ~loc
                       (lid (longident_of_string "Stdlib.ignore")))
                    [ (Asttypes.Nolabel, expression) ]
                in
                Ok (Ast_helper.Exp.sequence ~loc ignored body))
      in
      build expressions)
  | Let (bindings, body) -> (
      match to_parsetree ~context body with
      | Error _ as err -> err
      | Ok body ->
          let rec build = function
            | [] -> Ok body
            | (pattern, value) :: rest -> (
                match (to_parsetree ~context value, build rest) with
                | (Error _ as err), _ -> err
                | _, (Error _ as err) -> err
                | Ok value, Ok body ->
                    let binding =
                      Ast_helper.Vb.mk ~loc (pattern_to_parsetree pattern) value
                    in
                    Ok
                      (add_pattern_node_ids [ pattern ]
                         (Ast_helper.Exp.let_ ~loc Asttypes.Nonrecursive [ binding ]
                            body)))
          in
          build bindings)
  | LetRec (name, params, body, args) -> (
      match
        ( to_parsetree ~context (Fun (params, body)),
          to_parsetree ~context (Apply (Ident name, args)) )
      with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok fn, Ok call ->
          let binding =
            Ast_helper.Vb.mk ~loc (Ast_helper.Pat.var ~loc (str name)) fn
          in
          Ok (Ast_helper.Exp.let_ ~loc Asttypes.Recursive [ binding ] call))
  | LetRecIn (name, params, body, next) -> (
      match (to_parsetree ~context (Fun (params, body)), to_parsetree ~context next) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok fn, Ok next ->
          let binding =
            Ast_helper.Vb.mk ~loc (Ast_helper.Pat.var ~loc (str name)) fn
          in
          Ok (Ast_helper.Exp.let_ ~loc Asttypes.Recursive [ binding ] next))
  | LetRecGroup (bindings, body) ->
      let rec compile_bindings acc = function
        | [] ->
            Result.map
              (fun body -> Ast_helper.Exp.let_ ~loc Asttypes.Recursive
                 (List.rev acc) body)
              (to_parsetree ~context body)
        | (pattern, value) :: rest ->
            Result.bind (to_parsetree ~context value) (fun value ->
                let binding =
                  Ast_helper.Vb.mk ~loc (pattern_to_parsetree pattern) value
                in
                compile_bindings (binding :: acc) rest)
      in
      compile_bindings [] bindings
  | PackModule (name, signature) ->
      let module_ = Ast_helper.Mod.ident ~loc (lid (longident_of_string name)) in
      let ty = Ast_helper.Typ.package ~loc (Ast_helper.Typ.package_type ~loc (lid (longident_of_string signature)) []) in
      Ok (Ast_helper.Exp.constraint_ ~loc (Ast_helper.Exp.pack ~loc module_ None) ty)
  | UnpackModule (name, signature, value, body) ->
      Result.bind (to_parsetree ~context value) (fun value ->
        Result.map (fun body ->
          let ty = Ast_helper.Typ.package ~loc (Ast_helper.Typ.package_type ~loc (lid (longident_of_string signature)) []) in
          let module_ = Ast_helper.Mod.unpack ~loc (Ast_helper.Exp.constraint_ ~loc value ty) in
          Ast_helper.Exp.struct_item ~loc (Ast_helper.Str.module_ ~loc (Ast_helper.Mb.mk ~loc (Location.mkloc (Some name) loc) module_)) body)
          (to_parsetree ~context body))
  | Match (target, cases) -> (
      let case_patterns = List.map fst cases in
      match to_parsetree ~context target with
      | Error _ as err -> err
      | Ok target ->
          let rec build_cases acc = function
            | [] -> Ok (List.rev acc)
            | (pattern, body) :: rest -> (
                match to_parsetree ~context body with
                | Error _ as err -> err
                | Ok body ->
                    build_cases
                      (Ast_helper.Exp.case (pattern_to_parsetree pattern) body :: acc)
                      rest)
          in
          match build_cases [] cases with
          | Error _ as err -> err
          | Ok cases ->
              Ok
                (add_pattern_node_ids case_patterns
                   (Ast_helper.Exp.match_ ~loc target cases)))
  | Match_guarded (target, cases) -> (
      let case_patterns = List.map (fun (pattern, _, _) -> pattern) cases in
      match to_parsetree ~context target with
      | Error _ as err -> err
      | Ok target ->
          match guarded_cases_to_parsetree ~context cases with
          | Error _ as err -> err
          | Ok cases ->
              Ok
                (add_pattern_node_ids case_patterns
                   (Ast_helper.Exp.match_ ~loc target cases)))
  | Try (body, cases) -> (
      let case_patterns = List.map (fun (pattern, _, _) -> pattern) cases in
      match to_parsetree ~context body with
      | Error _ as err -> err
      | Ok body ->
          match guarded_cases_to_parsetree ~context cases with
          | Error _ as err -> err
          | Ok cases ->
              Ok
                (add_pattern_node_ids case_patterns
                   (Ast_helper.Exp.try_ ~loc body cases)))
  | Infix (operator, left, right) -> (
      match (to_parsetree ~context left, to_parsetree ~context right) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok left, Ok right ->
          Ok
            (Ast_helper.Exp.apply ~loc
               (Ast_helper.Exp.ident ~loc (lid (Longident.Lident operator)))
               [ (Asttypes.Nolabel, left); (Asttypes.Nolabel, right) ]))
  | Prefix (operator, expression) -> (
      match to_parsetree ~context expression with
      | Error _ as err -> err
      | Ok expression ->
          Ok
            (Ast_helper.Exp.apply ~loc
               (Ast_helper.Exp.ident ~loc (lid (Longident.Lident operator)))
               [ (Asttypes.Nolabel, expression) ]))
  | Constraint (expression, type_name) ->
      Result.map
        (fun expression ->
          Ast_helper.Exp.constraint_ ~loc expression
            (core_type_of_source type_name))
        (to_parsetree ~context expression)
  | Field (target, field_name) -> (
      match to_parsetree ~context target with
      | Error _ as err -> err
      | Ok target ->
          Ok
            (Ast_helper.Exp.field ~loc target
               (lid (longident_of_string field_name))))
  | SetField (target, field_name, value) -> (
      match (to_parsetree ~context target, to_parsetree ~context value) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok target, Ok value ->
          Ok
            (Ast_helper.Exp.setfield ~loc target
               (lid (longident_of_string field_name)) value))
  | Cons (head, tail) -> (
      match (to_parsetree ~context head, to_parsetree ~context tail) with
      | (Error _ as err), _ -> err
      | _, (Error _ as err) -> err
      | Ok head, Ok tail ->
          let pair = Ast_helper.Exp.tuple ~loc [ (None, head); (None, tail) ] in
          Ok
            (Ast_helper.Exp.construct ~loc (lid (Longident.Lident "::"))
               (Some pair)))
  | Record (fields, type_name) ->
      let rec build_fields acc = function
        | [] -> Ok (List.rev acc)
        | (name, value) :: rest -> (
            match to_parsetree ~context value with
            | Error _ as err -> err
            | Ok value ->
                build_fields
                  ((lid (longident_of_string name), value) :: acc)
                  rest)
      in
      build_fields [] fields
      |> Result.map (fun fields ->
             let expression = Ast_helper.Exp.record ~loc fields None in
             match type_name with
             | None -> expression
             | Some name ->
                 let argument = "__lg_record_value" in
                 let pattern = PConstraint (PVar argument, name) in
                 let body =
                   Ast_helper.Exp.ident ~loc
                     { txt = Longident.Lident argument; loc }
                 in
                 let function_ =
                   Ast_helper.Exp.function_ ~loc
                     [ function_parameter pattern ]
                     None (Pfunction_body body)
                 in
                 Ast_helper.Exp.apply ~loc
                   function_ [ (Nolabel, expression) ])
  | RecordUpdate (record, fields) -> (
      match to_parsetree ~context record with
      | Error _ as err -> err
      | Ok record ->
          let rec build_fields acc = function
            | [] -> Ok (List.rev acc)
            | (name, value) :: rest -> (
                match to_parsetree ~context value with
                | Error _ as err -> err
                | Ok value ->
                    build_fields
                      ((lid (longident_of_string name), value) :: acc)
                      rest)
          in
          Result.map
            (fun fields -> Ast_helper.Exp.record ~loc fields (Some record))
            (build_fields [] fields))
