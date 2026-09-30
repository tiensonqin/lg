type node =
  | Atom of string
  | Comment of string
  | Collection of char * char * node list

let closing_for = function
  | '(' -> ')'
  | '[' -> ']'
  | '{' -> '}'
  | _ -> invalid_arg "opening delimiter"

let is_whitespace = function
  | ' ' | '\n' | '\r' | '\t' | ',' -> true
  | _ -> false

let is_delimiter = function
  | '(' | ')' | '[' | ']' | '{' | '}' -> true
  | _ -> false

let read_string source start =
  let rec loop index escaped =
    if index >= String.length source then Error.error ~code:Error_code.Semantic "unterminated string"
    else if escaped then loop (index + 1) false
    else
      match source.[index] with
      | '\\' -> loop (index + 1) true
      | '"' -> Ok (String.sub source start (index - start + 1), index + 1)
      | _ -> loop (index + 1) false
  in
  loop (start + 1) false

let read_regex source start =
  let rec loop index escaped =
    if index >= String.length source then Error.error ~code:Error_code.Semantic "unterminated regex"
    else if escaped then loop (index + 1) false
    else
      match source.[index] with
      | '\\' -> loop (index + 1) true
      | '"' -> Ok (String.sub source start (index - start + 1), index + 1)
      | _ -> loop (index + 1) false
  in
  loop (start + 2) false

let read_comment source start =
  let rec loop index =
    if index >= String.length source || source.[index] = '\n' then index
    else loop (index + 1)
  in
  let finish = loop start in
  (String.sub source start (finish - start) |> String.trim, finish)

let read_atom source start =
  let rec loop index =
    if index >= String.length source then index
    else
      let ch = source.[index] in
      if is_whitespace ch || is_delimiter ch || ch = ';' then index
      else loop (index + 1)
  in
  let finish = loop start in
  (String.sub source start (finish - start), finish)

let parse source =
  let rec nodes closing acc index =
    if index >= String.length source then
      match closing with
      | None -> Ok (List.rev acc, index)
      | Some expected ->
          Error.error ~code:Error_code.Semantic
            ("unterminated delimiter "
            ^ String.make 1
                (match expected with ')' -> '(' | ']' -> '[' | '}' -> '{' | _ -> expected))
    else
      let ch = source.[index] in
      if is_whitespace ch then nodes closing acc (index + 1)
      else if ch = ';' then
        let comment, next = read_comment source index in
        nodes closing (Comment comment :: acc) next
      else
        match ch with
        | '(' | '[' | '{' ->
            let expected = closing_for ch in
            (match nodes (Some expected) [] (index + 1) with
            | Error _ as err -> err
            | Ok (children, next) ->
                nodes closing (Collection (ch, expected, children) :: acc) next)
        | ')' | ']' | '}' -> (
            match closing with
            | Some expected when ch = expected -> Ok (List.rev acc, index + 1)
            | _ -> Error.error ~code:Error_code.Type_mismatch ("mismatched closing delimiter " ^ String.make 1 ch))
        | '#' when index + 1 < String.length source && source.[index + 1] = '"'
          -> (
            match read_regex source index with
            | Error _ as err -> err
            | Ok (value, next) -> nodes closing (Atom value :: acc) next)
        | '"' -> (
            match read_string source index with
            | Error _ as err -> err
            | Ok (value, next) -> nodes closing (Atom value :: acc) next)
        | _ ->
            let atom, next = read_atom source index in
            if atom = "" then Error.error ~code:Error_code.Invalid_form "invalid formatter token"
            else nodes closing (Atom atom :: acc) next
  in
  nodes None [] 0 |> Result.map fst

let rec flat = function
  | Atom value -> Some value
  | Comment _ -> None
  | Collection (opening, closing, children) ->
      let rec child_values acc = function
        | [] -> Some (List.rev acc)
        | child :: rest -> (
            match flat child with
            | None -> None
            | Some value -> child_values (value :: acc) rest)
      in
      child_values [] children
      |> Option.map (fun values ->
             String.make 1 opening ^ String.concat " " values
             ^ String.make 1 closing)

let spaces count = String.make count ' '

let line_is_comment line =
  let trimmed = String.trim line in
  String.length trimmed > 0 && trimmed.[0] = ';'

let append_closing indent closing lines =
  match List.rev lines with
  | [] -> [ spaces indent ^ String.make 1 closing ]
  | last :: _rest when line_is_comment last ->
      lines @ [ spaces indent ^ String.make 1 closing ]
  | last :: rest ->
      List.rev ((last ^ String.make 1 closing) :: rest)

let rec render ~width ~indent node =
  match flat node with
  | Some value when indent + String.length value <= width ->
      [ spaces indent ^ value ]
  | _ -> (
      match node with
      | Atom value -> [ spaces indent ^ value ]
      | Comment value -> [ spaces indent ^ value ]
      | Collection (opening, closing, children) -> (
          match children with
          | [] -> [ spaces indent ^ String.make 1 opening ^ String.make 1 closing ]
          | first :: rest ->
              let first_lines =
                match flat first with
                | Some value -> [ spaces indent ^ String.make 1 opening ^ value ]
                | None ->
                    (spaces indent ^ String.make 1 opening)
                    :: render ~width ~indent:(indent + 2) first
              in
              let remaining =
                rest
                |> List.concat_map (render ~width ~indent:(indent + 2))
              in
              append_closing indent closing (first_lines @ remaining)))

let format source =
  match parse source with
  | Error _ as err -> err
  | Ok nodes ->
      let lines = nodes |> List.concat_map (render ~width:80 ~indent:0) in
      if lines = [] then Ok "" else Ok (String.concat "\n" lines ^ "\n")
