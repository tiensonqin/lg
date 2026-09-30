open Types

let accepts_int ty =
  Types.assignable ~policy:Host_boundary ~expected:TInt ~actual:ty

let expect_int_args name args =
  if List.for_all (fun arg -> accepts_int arg.ty) args then Ok ()
  else Error.error ~code:Error_code.Arity ("expected int arguments for " ^ name)

let one_arg name args =
  match args with
  | [ arg ] -> Ok arg
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 1 arguments")

let two_args name args =
  match args with
  | [ left; right ] -> Ok (left, right)
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 2 arguments")

let int_unary name args build_code =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg -> (
      match expect_int_args name [ arg ] with
      | Error _ as err -> err
      | Ok () -> Ok (typed_ir TInt (build_code arg.semantic_expr)))

let int_binary name args build_code =
  match two_args name args with
  | Error _ as err -> err
  | Ok (left, right) -> (
      match expect_int_args name [ left; right ] with
      | Error _ as err -> err
      | Ok () -> Ok (build_code left.semantic_expr right.semantic_expr))

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)
let string_length expr = apply "String.length" [ expr ]
let string_get expr index = apply "String.get" [ expr; index ]
let string_sub expr start length = apply "String.sub" [ expr; start; length ]

let string_rindex_opt expr needle =
  apply "String.rindex_opt" [ expr; Semantic_ir.Char needle ]

let string_concat left right = Semantic_ir.Infix ("^", left, right)

let string_nonempty expr =
  Semantic_ir.Infix (">", string_length expr, Semantic_ir.Int 0)

let starts_with_colon expr =
  Semantic_ir.Infix
    ("=", string_get expr (Semantic_ir.Int 0), Semantic_ir.Char ':')

let drop_first_char expr =
  string_sub expr (Semantic_ir.Int 1)
    (Semantic_ir.Infix ("-", string_length expr, Semantic_ir.Int 1))

let string_and left right = Semantic_ir.Infix ("&&", left, right)
let identifier_body_expr name arg =
  let normalize expression =
      let value = Semantic_ir.Ident "value" in
    Semantic_ir.Let
      ( [ (Semantic_ir.PVar "value", expression) ],
             Semantic_ir.If
               ( string_and (string_nonempty value) (starts_with_colon value),
                 drop_first_char value,
            value ) )
  in
  match arg.ty with
  | TString | TSymbol | TKeyword | TUnknown -> Ok (normalize arg.semantic_expr)
  | TNullable TString | TOcaml_app ("option", [ TString ]) ->
      Ok
        (Semantic_ir.Match
           ( arg.semantic_expr,
             [
               (Semantic_ir.PConstructor ("None", None), Semantic_ir.String "");
               ( Semantic_ir.PConstructor
                   ("Some", Some (Semantic_ir.PVar "value")),
                 normalize (Semantic_ir.Ident "value") );
             ] ))
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects string, keyword, or symbol")

let substring_after_last_slash body =
  string_sub (Semantic_ir.Ident body)
    (Semantic_ir.Infix ("+", Semantic_ir.Ident "index", Semantic_ir.Int 1))
    (Semantic_ir.Infix
       ( "-",
         Semantic_ir.Infix
           ( "-",
             string_length (Semantic_ir.Ident body),
             Semantic_ir.Ident "index" ),
         Semantic_ir.Int 1 ))

let identifier_name_expr arg =
  Semantic_ir.Let
    ( [ (Semantic_ir.PVar "body", arg) ],
      Semantic_ir.Match
        ( string_rindex_opt (Semantic_ir.Ident "body") '/',
          [
            (Semantic_ir.PConstructor ("None", None), Semantic_ir.Ident "body");
            ( Semantic_ir.PConstructor ("Some", Some (Semantic_ir.PVar "index")),
              substring_after_last_slash "body" );
          ] ) )

let identifier_namespace_expr arg =
  Semantic_ir.Let
    ( [ (Semantic_ir.PVar "body", arg) ],
      Semantic_ir.Match
        ( string_rindex_opt (Semantic_ir.Ident "body") '/',
          [
            ( Semantic_ir.PConstructor ("None", None),
              Semantic_ir.Constructor ("None", None) );
            ( Semantic_ir.PConstructor ("Some", Some (Semantic_ir.PVar "index")),
              Semantic_ir.Constructor
                ( "Some",
                  Some
                    (string_sub (Semantic_ir.Ident "body") (Semantic_ir.Int 0)
                       (Semantic_ir.Ident "index")) ) );
          ] ) )

let keyword_one_arg_expr arg =
  let value = Semantic_ir.Ident "value" in
  Semantic_ir.Let
    ( [ (Semantic_ir.PVar "value", arg) ],
      Semantic_ir.If
        ( string_and (string_nonempty value) (starts_with_colon value),
          value,
          string_concat (Semantic_ir.String ":") value ) )

let optional_identifier_expr ~prefix namespace name =
  let absent =
    if prefix = "" then Semantic_ir.Ident "name"
    else string_concat (Semantic_ir.String prefix) (Semantic_ir.Ident "name")
  in
  let present =
    string_concat
      (string_concat
         (string_concat (Semantic_ir.String prefix) (Semantic_ir.Ident "namespace"))
         (Semantic_ir.String "/"))
      (Semantic_ir.Ident "name")
  in
  Semantic_ir.Let
    ( [ (Semantic_ir.PVar "name", name) ],
      Semantic_ir.Match
        ( namespace,
          [
            (Semantic_ir.PConstructor ("None", None), absent);
            ( Semantic_ir.PConstructor
                ("Some", Some (Semantic_ir.PVar "namespace")),
              present );
          ] ) )

let compile_name target name args =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg -> (
      match arg.ty with
      | TString -> Ok (typed_ir TString arg.semantic_expr)
      | ty when Types.is_dynamic ty -> (
          let identifier =
            apply "Lg_runtime.Runtime_dynamic.as_identifier"
              [ arg.semantic_expr ]
          in
          match
            identifier_body_expr name
              { arg with semantic_expr = identifier; ty = TSymbol }
          with
          | Error _ as error -> error
          | Ok body -> Ok (typed_ir TString (identifier_name_expr body)))
      | TKeyword when target = Target.Melange ->
          Ok
            (typed_ir TString
               (apply "Lg_runtime.Runtime_keyword.cljs_name"
                  [ arg.semantic_expr ]))
      | TKeyword | TSymbol -> (
          match identifier_body_expr name arg with
          | Error _ as err -> err
          | Ok body -> Ok (typed_ir TString (identifier_name_expr body)))
      | _ -> Error.error ~code:Error_code.Arity "name expects keyword, string, or symbol")

let compile_keyword _name args =
  match args with
  | [ arg ] -> (
      match arg.ty with
      | TKeyword -> Ok (typed_ir TKeyword arg.semantic_expr)
      | ty when Types.is_dynamic ty ->
          Ok
            (typed_ir TKeyword
               (keyword_one_arg_expr
                  (apply "Lg_runtime.Runtime_dynamic.as_identifier"
                     [ arg.semantic_expr ])))
      | TString | TSymbol | TUnknown ->
          Ok (typed_ir TKeyword (keyword_one_arg_expr arg.semantic_expr))
      | _ -> Error.error ~code:Error_code.Arity "keyword expects keyword, string, or symbol")
  | _ -> Error.error ~code:Error_code.Arity "keyword expects 1 argument"

let compile_namespace target name args =
  match one_arg name args with
  | Error _ as err -> err
  | Ok arg -> (
      match arg.ty with
      | ty when Types.is_dynamic ty ->
          let identifier =
            apply "Lg_runtime.Runtime_dynamic.as_named_identifier"
              [ arg.semantic_expr ]
          in
          Result.map
            (fun body ->
              typed_ir
                (TOcaml_app ("option", [ TString ]))
                (identifier_namespace_expr body))
            (identifier_body_expr name
               { arg with semantic_expr = identifier; ty = TKeyword })
      | TKeyword when target = Target.Melange ->
          Ok
            (typed_ir (TOcaml_app ("option", [ TString ]))
               (apply "Lg_runtime.Runtime_keyword.cljs_namespace"
                  [ arg.semantic_expr ]))
      | TKeyword | TSymbol | TUnknown ->
          Result.map
            (fun body ->
              typed_ir
                (TOcaml_app ("option", [ TString ]))
                (identifier_namespace_expr body))
            (identifier_body_expr name arg)
      | _ -> Error.error ~code:Error_code.Arity "namespace expects keyword or symbol")

let compile_symbol name args =
  match args with
  | [ arg ] -> (
      match identifier_body_expr name arg with
      | Error _ -> Error.error ~code:Error_code.Arity "symbol expects string, keyword, or symbol"
      | Ok expr -> Ok (typed_ir TSymbol expr))
  | _ -> Error.error ~code:Error_code.Arity "symbol expects 1 argument"

let compile_identifier_parts name return_ty prefix args =
  match args with
  | [ namespace_arg; name_arg ]
    when (match Types.constraint_value_type namespace_arg.ty with
         | TNullable TString | TOcaml_app ("option", [ TString ]) -> true
         | _ -> false)
         && Types.equal name_arg.ty TString ->
      Ok
        (typed_ir return_ty
           (optional_identifier_expr ~prefix namespace_arg.semantic_expr
              name_arg.semantic_expr))
  | [ _; _ ] ->
      Error.error ~code:Error_code.Arity
        (name ^ " expects an optional string namespace and string name")
  | _ -> Error.error ~code:Error_code.Arity (name ^ " expects 2 arguments")

let compile ~target builtin args =
  let name = Builtin_id.scalar_source_name builtin in
  match builtin with
  | Builtin_id.Name -> compile_name target name args
  | Builtin_id.Namespace -> compile_namespace target name args
  | Builtin_id.Keyword -> (
      match args with
      | [ _ ] -> compile_keyword "keyword" args
      | _ -> compile_identifier_parts name TKeyword ":" args)
  | Builtin_id.Symbol -> (
      match args with
      | [ _ ] -> compile_symbol "symbol" args
      | _ -> compile_identifier_parts name TSymbol "" args)
