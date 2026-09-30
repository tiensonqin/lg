open Types

let rec accepts_float ty =
  match ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) -> accepts_float inner
  | ty -> Types.equal ty TFloat

let rec accepts_mixed_numeric ty =
  match ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      accepts_mixed_numeric inner
  | TInt | TFloat -> true
  | _ -> false

let bind_arguments prefix args build =
  let rec bind index bound = function
    | [] -> build (List.rev bound)
    | arg :: rest ->
        let name = prefix ^ string_of_int index in
        Semantic_ir.Let
          ( [ (Semantic_ir.PVar name, arg.semantic_expr) ],
            bind (index + 1)
              ({ arg with semantic_expr = Semantic_ir.Ident name } :: bound)
              rest )
  in
  bind 0 [] args

let expect_float_args args =
  List.for_all (fun arg -> accepts_float arg.ty) args

let rec float_expression arg =
  match arg.ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      float_expression
        {
          arg with
          ty = inner;
          semantic_expr =
            Semantic_ir.Apply
              (Semantic_ir.Ident "Option.get", [ arg.semantic_expr ]);
        }
  | _ -> arg.semantic_expr

(* Mixed int/float arithmetic widens integers to floats, matching Clojure's
   numeric coercion semantics. *)
let widen_to_float arg =
  if accepts_float arg.ty then
    { arg with ty = TFloat; semantic_expr = float_expression arg }
  else
    typed_ir TFloat
      (Semantic_ir.Apply
         (Semantic_ir.Ident "float_of_int", [ Core_int.int_expression arg ]))

let fold_infix operator first rest =
  List.fold_left
    (fun expression arg ->
      Semantic_ir.Infix (operator, expression, float_expression arg))
    (float_expression first) rest

let compile_operator name args =
  match (name, args) with
  | "/", [] -> Error.error ~code:Error_code.Arity "/ expects at least 1 arguments"
  | _, [] -> Error.error ~code:Error_code.Arity (name ^ " expects at least 1 arguments")
  | _, [ arg ] when name = "-" ->
      Ok (typed_ir TFloat (Semantic_ir.Prefix ("~-.", float_expression arg)))
  | _, [ arg ] when name = "/" ->
      Ok
        (typed_ir TFloat
           (Semantic_ir.Infix
              ("/.", Semantic_ir.Float "1.", float_expression arg)))
  | _, [ arg ] -> Ok (typed_ir TFloat (float_expression arg))
  | _, first :: rest ->
      let operator =
        match name with
        | "+" -> "+."
        | "-" -> "-."
        | "*" -> "*."
        | "/" -> "/."
        | _ -> assert false
      in
      Ok (typed_ir TFloat (fold_infix operator first rest))

let compile_min_max name args =
  let is_max = name = "max" || name = "__lg_max" in
  let display_name = if is_max then "max" else "min" in
  match args with
  | [] -> Error.error ~code:Error_code.Arity (display_name ^ " expects at least 1 arguments")
  | _ :: _ when not (List.for_all (fun arg -> accepts_float arg.ty) args) ->
      Error.error ~code:Error_code.Arity
        (display_name ^ " numeric arguments must all have the same type")
  | first :: rest ->
      let fn =
        if is_max then "Lg_runtime.Runtime_math_common.max_number"
        else "Lg_runtime.Runtime_math_common.min_number"
      in
      let expression =
        bind_arguments "__lg_float_extrema_argument_" (first :: rest)
          (function
            | [] -> assert false
            | first :: rest ->
                List.fold_left
                  (fun expression arg ->
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident fn,
                        [ expression; float_expression arg ] ))
                  (float_expression first) rest)
      in
      Ok (typed_ir TFloat expression)
