open Ast

let parse = function
  | FVector [] -> Error.error ~code:Error_code.Arity "type parameter vector must not be empty"
  | FVector forms ->
      let rec loop parameters = function
        | [] -> Ok (List.rev parameters)
        | FSymbol parameter :: rest ->
            let parameter = Names.sanitize_name parameter in
            if List.mem parameter parameters then
              Error.error ~code:Error_code.Duplicate ("duplicate type parameter " ^ parameter)
            else loop (parameter :: parameters) rest
        | _ -> Error.error ~code:Error_code.Semantic "type parameters must be symbols"
      in
      loop [] forms
  | _ -> Error.error ~code:Error_code.Semantic "type parameters must be a vector"

