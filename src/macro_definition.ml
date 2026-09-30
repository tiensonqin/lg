open Ast

type arity = {
  params : form list;
  body : form list;
}

type t = {
  namespace : string;
  name : string;
  arities : arity list;
  provenance : Source_context.provenance;
  template_location : Location.t option;
}

let drop_docstring = function FString _ :: rest -> rest | forms -> forms

let parse_arity = function
  | FList (FVector params :: body) -> Ok { params; body }
  | _ -> Error.error ~code:Error_code.Macro "macro arity expects a parameter vector and body"

let create ~namespace ~name forms =
  let provenance = Source_context.capture forms in
  let finish arities =
    let template_location =
      arities
      |> List.find_map (fun arity ->
             arity.body |> List.find_map Source_context.find)
    in
    Ok { namespace; name; arities; provenance; template_location }
  in
  match drop_docstring forms with
  | FVector params :: body -> finish [ { params; body } ]
  | arity_forms ->
      let rec parse acc = function
        | [] when acc = [] -> Error.error ~code:Error_code.Arity "defmacro expects at least one arity"
        | [] -> finish (List.rev acc)
        | form :: rest -> (
            match parse_arity form with
            | Error _ as err -> err
            | Ok arity -> parse (arity :: acc) rest)
      in
      parse [] arity_forms
