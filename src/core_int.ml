open Types

let rec accepts_int ty =
  match ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) -> accepts_int inner
  | TOcaml "int" -> true
  | ty -> Types.assignable ~policy:Host_boundary ~expected:TInt ~actual:ty

let int value = Semantic_ir.Int value

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)

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

let rec int_expression arg =
  match arg.ty with
  | TNullable inner | TOcaml_app ("option", [ inner ]) ->
      int_expression
        {
          arg with
          ty = inner;
          semantic_expr =
            Semantic_ir.Apply
              (Semantic_ir.Ident "Option.get", [ arg.semantic_expr ]);
        }
  | ty when Types.is_dynamic ty ->
      Semantic_ir.Apply
        ( Semantic_ir.Ident "Lg_runtime.Runtime_dynamic.as_int",
          [ arg.semantic_expr ] )
  | _ -> arg.semantic_expr

let fold_infix operator first rest =
  List.fold_left
    (fun expression arg ->
      Semantic_ir.Infix (operator, expression, int_expression arg))
    (int_expression first) rest

let fold_function function_name first rest =
  List.fold_left
    (fun expression arg ->
      apply function_name [ expression; int_expression arg ])
    (int_expression first) rest

let expect_int_args name args =
  if List.for_all (fun arg -> accepts_int arg.ty) args then Ok ()
  else Error.error ~code:Error_code.Arity ("expected int arguments for " ^ name)

let compile_operator ~target name args =
  match (name, args) with
  | "+", [] -> Ok (typed_ir TInt (int 0))
  | "*", [] -> Ok (typed_ir TInt (int 1))
  | "/", [] -> Error.error ~code:Error_code.Arity "/ expects at least 1 arguments"
  | _, [] -> Error.error ~code:Error_code.Arity (name ^ " expects at least 1 arguments")
  | _, [ arg ] when name = "-" && target = Target.Melange ->
      Ok
        (typed_ir TInt
           (apply "Lg_runtime.Runtime_int_melange.negate"
              [ int_expression arg ]))
  | _, [ arg ] when name = "-" ->
      Ok (typed_ir TInt (Semantic_ir.Prefix ("~-", int_expression arg)))
  | _, [ arg ] when name = "/" ->
      Ok
        (typed_ir TInt
           (Semantic_ir.Infix ("/", Semantic_ir.Int 1, int_expression arg)))
  | _, [ arg ] -> Ok (typed_ir TInt (int_expression arg))
  | ("+" | "-" | "*"), first :: rest when target = Target.Melange ->
      let function_name =
        match name with
        | "+" -> "Lg_runtime.Runtime_int_melange.add"
        | "-" -> "Lg_runtime.Runtime_int_melange.subtract"
        | "*" -> "Lg_runtime.Runtime_int_melange.multiply"
        | _ -> assert false
      in
      Ok (typed_ir TInt (fold_function function_name first rest))
  | _, first :: rest ->
      let operator =
        match name with
        | "+" -> "+"
        | "-" -> "-"
        | "*" -> "*"
        | "/" -> "/"
        | _ -> assert false
      in
      Ok (typed_ir TInt (fold_infix operator first rest))

let compile_unary name args build_expr =
  match args with
  | [ arg ] ->
      if accepts_int arg.ty then Ok (typed_ir TInt (build_expr (int_expression arg)))
      else Error.error ~code:Error_code.Arity ("expected int arguments for " ^ name)
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 1 arguments")

let compile_binary name args =
  match args with
  | [ left; right ] ->
      if accepts_int left.ty && accepts_int right.ty then
        let expression =
          match name with
          | "quot" ->
              Semantic_ir.Infix
                ("/", int_expression left, int_expression right)
          | "rem" ->
              Semantic_ir.Infix
                ("mod", int_expression left, int_expression right)
          | "mod" ->
              apply "Lg_runtime.Runtime_int.clojure_mod"
                [ int_expression left; int_expression right ]
          | "bit-shift-left" ->
              Semantic_ir.Infix
                ("lsl", int_expression left, int_expression right)
          | "bit-shift-right" ->
              Semantic_ir.Infix
                ("asr", int_expression left, int_expression right)
          | _ -> int_expression left
        in
        Ok (typed_ir TInt expression)
      else Error.error ~code:Error_code.Arity ("expected int arguments for " ^ name)
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 2 arguments")

let compile_min_max name args =
  let is_max = name = "max" || name = "__lg_max" in
  let display_name = if is_max then "max" else "min" in
  match args with
  | [] -> Error.error ~code:Error_code.Arity (display_name ^ " expects at least 1 arguments")
  | _ ->
      if List.for_all (fun arg -> accepts_int arg.ty) args then
        let fn =
          if is_max then "Lg_runtime.Runtime_int.int_max"
          else "Lg_runtime.Runtime_int.int_min"
        in
        let expression =
          bind_arguments "__lg_int_extrema_argument_" args (function
            | [] -> assert false
            | first :: rest ->
                List.fold_left
                  (fun expression arg ->
                    Semantic_ir.Apply
                      ( Semantic_ir.Ident fn,
                        [ expression; int_expression arg ] ))
                  (int_expression first) rest)
        in
        Ok (typed_ir TInt expression)
      else Error.error ~code:Error_code.Arity ("expected int arguments for " ^ display_name)
