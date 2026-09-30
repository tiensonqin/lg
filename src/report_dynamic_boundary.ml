open Ast
open Types

module Env = Compiler_environment

let dynamic_ty = Types.dynamic_constraint TUnknown

let apply name args = Semantic_ir.Apply (Semantic_ir.Ident name, args)
let runtime name = "Lg_runtime.Runtime_test_report." ^ name

let typed_dynamic expression = typed_ir dynamic_ty expression

let rec convert_typed_value value =
  let mapper_for_type ty =
    let value_name = "__lg_report_dynamic_value" in
    Result.map
      (fun body -> Semantic_ir.Fun ([ Semantic_ir.PVar value_name ], body))
      (convert_type ty (Semantic_ir.Ident value_name))
  in
  if Types.is_dynamic value.ty then Ok value.semantic_expr
  else
  match Types.constraint_value_type value.ty with
  | TNil -> Ok (apply (runtime "dynamic_nil") [ Semantic_ir.Unit ])
  | TInt | TOcaml "int" -> Ok (apply (runtime "dynamic_int") [ value.semantic_expr ])
  | TFloat -> Ok (apply (runtime "dynamic_float") [ value.semantic_expr ])
  | TChar -> Ok (apply (runtime "dynamic_char") [ value.semantic_expr ])
  | TString -> Ok (apply (runtime "dynamic_string") [ value.semantic_expr ])
  | TKeyword -> Ok (apply (runtime "dynamic_keyword") [ value.semantic_expr ])
  | TSymbol -> Ok (apply (runtime "dynamic_symbol") [ value.semantic_expr ])
  | TBool -> Ok (apply (runtime "dynamic_bool") [ value.semantic_expr ])
  | TRegex -> Ok (apply (runtime "dynamic_regex") [ value.semantic_expr ])
  | TVector element_ty -> (
      match mapper_for_type element_ty with
      | Error _ as error -> error
      | Ok mapper ->
          Ok
            (apply (runtime "dynamic_vector")
               [
                 apply "List.map"
                   [
                     mapper;
                     apply "Rrbvec.to_list" [ value.semantic_expr ];
                   ];
               ]))
  | TList element_ty -> (
      match mapper_for_type element_ty with
      | Error _ as error -> error
      | Ok mapper ->
          Ok
            (apply (runtime "dynamic_list")
               [ apply "List.map" [ mapper; value.semantic_expr ] ]))
  | map_ty when Option.is_some (Types.dynamic_map_types map_ty) -> (
      let key_ty, value_ty = Option.get (Types.dynamic_map_types map_ty) in
      match (mapper_for_type key_ty, mapper_for_type value_ty) with
      | (Error _ as error), _ | _, (Error _ as error) -> error
      | Ok key_mapper, Ok value_mapper ->
          Ok
            (apply (runtime "dynamic_map_of_runtime_map")
               [ key_mapper; value_mapper; value.semantic_expr ]))
  | ty ->
      Error.error ~code:Error_code.Semantic
        ("cljs.test/report dynamic boundary does not support "
        ^ Types.source_name ty)

and convert_type ty expression =
  convert_typed_value (typed_ir ty expression)

let rec compile_form ~compile_expr scope env form =
  match form with
  | FKeyword keyword -> Ok (typed_dynamic (apply (runtime "dynamic_keyword") [ Semantic_ir.String keyword ]))
  | FString value -> Ok (typed_dynamic (apply (runtime "dynamic_string") [ Semantic_ir.String value ]))
  | FInt value -> Ok (typed_dynamic (apply (runtime "dynamic_int") [ Semantic_ir.Int value ]))
  | FFloat value -> Ok (typed_dynamic (apply (runtime "dynamic_float") [ Semantic_ir.Float value ]))
  | FDecimal _ ->
      Error.error ~code:Error_code.Semantic "static decimal values cannot cross the report dynamic boundary"
  | FChar value -> Ok (typed_dynamic (apply (runtime "dynamic_char") [ Semantic_ir.Char value ]))
  | FBool value -> Ok (typed_dynamic (apply (runtime "dynamic_bool") [ Semantic_ir.Bool value ]))
  | FRegex value -> Ok (typed_dynamic (apply (runtime "dynamic_regex") [ Semantic_ir.String value ]))
  | FSymbol "nil" -> Ok (typed_dynamic (apply (runtime "dynamic_nil") [ Semantic_ir.Unit ]))
  | FVector values ->
      compile_sequence ~compile_expr scope env values (runtime "dynamic_vector")
  | FMap entries ->
      let rec compile_entries acc = function
        | [] -> Ok (List.rev acc)
        | (key, value) :: rest -> (
            match
              ( compile_form ~compile_expr scope env key,
                compile_form ~compile_expr scope env value )
            with
            | Ok key, Ok value ->
                compile_entries
                  (Semantic_ir.Tuple [ key.semantic_expr; value.semantic_expr ]
                  :: acc)
                  rest
            | (Error _ as error), _ | _, (Error _ as error) -> error)
      in
      Result.map
        (fun entries ->
          typed_dynamic
            (apply (runtime "dynamic_map") [ Semantic_ir.List entries ]))
        (compile_entries [] entries)
  | FList _ | FSymbol _ | FCoreSymbol _ -> (
      match compile_expr scope env form with
      | Error _ as error -> error
      | Ok value ->
          Result.map typed_dynamic (convert_typed_value value))

and compile_sequence ~compile_expr scope env values constructor =
  let rec compile_values acc = function
    | [] -> Ok (List.rev acc)
    | value :: rest -> (
        match compile_form ~compile_expr scope env value with
        | Error _ as error -> error
        | Ok value -> compile_values (value.semantic_expr :: acc) rest)
  in
  Result.map
    (fun values -> typed_dynamic (apply constructor [ Semantic_ir.List values ]))
    (compile_values [] values)
