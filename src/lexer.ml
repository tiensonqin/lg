open Ast

let is_space = function ' ' | '\n' | '\r' | '\t' | ',' -> true | _ -> false

let is_delimiter ch =
  is_space ch
  ||
  match ch with
  | '(' | ')' | '[' | ']' | '{' | '}' -> true
  | _ -> false

let location start_offset end_offset =
  let position pos_cnum =
    { Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum }
  in
  {
    Location.loc_start = position start_offset;
    loc_end = position end_offset;
    loc_ghost = false;
  }

let unfinished_literal_error ~source ~opening_offset ~name ~closing =
  let eof = String.length source in
  Error.error ~code:Error_code.Lexing ~phase:`Lexing
    ~title:("UNFINISHED " ^ String.uppercase_ascii name)
    ~location:(location eof eof)
    ~related:
      [
        {
          Error.location = location opening_offset (opening_offset + 1);
          message = Printf.sprintf "This %s starts here." name;
        };
      ]
    ~hints:
      [ Printf.sprintf "Add %c to close this %s." closing name ]
    (Printf.sprintf
       "I reached the end of input while looking for %c to close this %s."
       closing name)

let rec skip_ignored source i =
  if i >= String.length source then i
  else if is_space source.[i] then skip_ignored source (i + 1)
  else if source.[i] = ';' then
    let rec skip_comment j =
      if j >= String.length source || source.[j] = '\n' then j
      else skip_comment (j + 1)
    in
    skip_ignored source (skip_comment i)
  else i

let read_string source start =
  let buffer = Buffer.create 16 in
  let rec loop i =
    if i >= String.length source then
      unfinished_literal_error ~source ~opening_offset:(start - 1) ~name:"string"
        ~closing:'"'
    else
      match source.[i] with
      | '"' -> Ok (Buffer.contents buffer, i + 1)
      | '\\' when i + 1 < String.length source -> (
          match source.[i + 1] with
          | '"' ->
              Buffer.add_char buffer '"';
              loop (i + 2)
          | '\\' ->
              Buffer.add_char buffer '\\';
              loop (i + 2)
          | 'n' ->
              Buffer.add_char buffer '\n';
              loop (i + 2)
          | 'r' ->
              Buffer.add_char buffer '\r';
              loop (i + 2)
          | 't' ->
              Buffer.add_char buffer '\t';
              loop (i + 2)
          | 'b' ->
              Buffer.add_char buffer '\b';
              loop (i + 2)
          | 'f' ->
              Buffer.add_char buffer '\012';
              loop (i + 2)
          | ch ->
              Buffer.add_char buffer ch;
              loop (i + 2))
      | ch ->
          Buffer.add_char buffer ch;
          loop (i + 1)
  in
  loop start

let read_regex source start =
  let buffer = Buffer.create 16 in
  let rec loop i =
    if i >= String.length source then
      unfinished_literal_error ~source ~opening_offset:(start - 1) ~name:"regex"
        ~closing:'"'
    else
      match source.[i] with
      | '"' -> Ok (Buffer.contents buffer, i + 1)
      | '\\' when i + 1 < String.length source ->
          Buffer.add_char buffer '\\';
          Buffer.add_char buffer source.[i + 1];
          loop (i + 2)
      | ch ->
          Buffer.add_char buffer ch;
          loop (i + 1)
  in
  loop start

let read_atom source start =
  let rec loop i =
    if i >= String.length source || is_delimiter source.[i] then i
    else loop (i + 1)
  in
  (* A character's first byte is data even when it is a reader delimiter. *)
  let first =
    if start + 1 < String.length source && source.[start] = '\\' then start + 2
    else start
  in
  let finish = loop first in
  (String.sub source start (finish - start), finish)

let utf8_scalar_of_string source =
  let length = String.length source in
  let byte index = Char.code source.[index] in
  if length = 1 then Some (byte 0)
  else if length = 2 then
    let b0 = byte 0 and b1 = byte 1 in
    if b0 land 0xE0 = 0xC0 && b0 >= 0xC2 && b1 land 0xC0 = 0x80 then
      Some (((b0 land 0x1F) lsl 6) lor (b1 land 0x3F))
    else None
  else if length = 3 then
    let b0 = byte 0 and b1 = byte 1 and b2 = byte 2 in
    if
      b0 land 0xF0 = 0xE0
      && (b0 <> 0xE0 || b1 >= 0xA0)
      && (b0 <> 0xED || b1 < 0xA0)
      && b1 land 0xC0 = 0x80
      && b2 land 0xC0 = 0x80
    then
      Some
        (((b0 land 0x0F) lsl 12)
        lor ((b1 land 0x3F) lsl 6)
        lor (b2 land 0x3F))
    else None
  else if length = 4 then
    let b0 = byte 0 and b1 = byte 1 and b2 = byte 2 and b3 = byte 3 in
    if
      b0 land 0xF8 = 0xF0
      && b0 <= 0xF4
      && (b0 <> 0xF0 || b1 >= 0x90)
      && (b0 <> 0xF4 || b1 < 0x90)
      && b1 land 0xC0 = 0x80
      && b2 land 0xC0 = 0x80
      && b3 land 0xC0 = 0x80
    then
      Some
        (((b0 land 0x07) lsl 18)
        lor ((b1 land 0x3F) lsl 12)
        lor ((b2 land 0x3F) lsl 6)
        lor (b3 land 0x3F))
    else None
  else None

let char_of_atom atom =
  match atom with
  | "\\newline" -> Some '\n'
  | "\\space" -> Some ' '
  | "\\tab" -> Some '\t'
  | "\\backspace" -> Some '\b'
  | "\\formfeed" -> Some '\012'
  | "\\return" -> Some '\r'
  | atom when String.length atom = 2 && atom.[0] = '\\' -> Some atom.[1]
  | atom when String.length atom > 1 && atom.[0] = '\\' -> (
      let source = String.sub atom 1 (String.length atom - 1) in
      match utf8_scalar_of_string source with
      | Some scalar when scalar <= 255 -> Some (Char.chr scalar)
      | _ -> None)
  | _ -> None

let looks_like_float atom =
  String.contains atom '.' || String.contains atom 'e' || String.contains atom 'E'

let strip_numeric_suffix suffix atom =
  if String.length atom > 1 && atom.[String.length atom - 1] = suffix then
    Some (String.sub atom 0 (String.length atom - 1))
  else None

let valid_decimal_literal source =
  let length = String.length source in
  let index =
    if length > 0 && (source.[0] = '-' || source.[0] = '+') then 1 else 0
  in
  let rec digits index =
    if index < length then
      match source.[index] with '0' .. '9' -> digits (index + 1) | _ -> index
    else index
  in
  let integer_end = digits index in
  let fraction_end =
    if integer_end < length && source.[integer_end] = '.' then
      digits (integer_end + 1)
    else integer_end
  in
  let has_digit = integer_end > index || fraction_end > integer_end + 1 in
  if not has_digit then false
  else if fraction_end = length then true
  else if source.[fraction_end] = 'e' || source.[fraction_end] = 'E' then
    let exponent_start = fraction_end + 1 in
    let exponent_start =
      if
        exponent_start < length
        && (source.[exponent_start] = '-' || source.[exponent_start] = '+')
      then exponent_start + 1
      else exponent_start
    in
    exponent_start < length && digits exponent_start = length
  else false

let ratio_float_literal atom =
  match String.split_on_char '/' atom with
  | [ numerator; denominator ] -> (
      match (int_of_string_opt numerator, int_of_string_opt denominator) with
      | Some _, Some denominator when denominator <> 0 -> Some atom
      | _ -> None)
  | _ -> None

let radix_digit_value = function
  | '0' .. '9' as ch -> Some (Char.code ch - Char.code '0')
  | 'a' .. 'z' as ch -> Some (10 + Char.code ch - Char.code 'a')
  | 'A' .. 'Z' as ch -> Some (10 + Char.code ch - Char.code 'A')
  | _ -> None

let radix_marker_index atom start =
  let rec loop index =
    if index >= String.length atom then None
    else
      match atom.[index] with
      | 'r' | 'R' -> Some index
      | _ -> loop (index + 1)
  in
  loop start

let parse_radix_digits ~sign ~radix digits =
  let radix64 = Int64.of_int radix in
  let limit =
    if sign < 0 then Int64.add (Int64.of_int max_int) 1L
    else Int64.of_int max_int
  in
  let rec loop index acc =
    if index >= String.length digits then
      if sign < 0 then
        if Int64.equal acc limit then Some min_int
        else Some (-Int64.to_int acc)
      else Some (Int64.to_int acc)
    else
      match radix_digit_value digits.[index] with
      | Some digit when digit < radix ->
          let digit64 = Int64.of_int digit in
          if Int64.compare acc (Int64.div (Int64.sub limit digit64) radix64) > 0
          then None
          else loop (index + 1) Int64.(add (mul acc radix64) digit64)
      | _ -> None
  in
  if digits = "" then None else loop 0 0L

let radix_integer_literal atom =
  let length = String.length atom in
  let sign, start =
    if length > 0 && atom.[0] = '-' then (-1, 1)
    else if length > 0 && atom.[0] = '+' then (1, 1)
    else (1, 0)
  in
  match radix_marker_index atom start with
  | None -> None
  | Some marker when marker = start || marker + 1 >= length -> None
  | Some marker -> (
      let radix_source = String.sub atom start (marker - start) in
      match int_of_string_opt radix_source with
      | Some radix when radix >= 2 && radix <= 36 ->
          let digits = String.sub atom (marker + 1) (length - marker - 1) in
          parse_radix_digits ~sign ~radix digits
      | _ -> None)

let tokenize source =
  let token desc start_offset end_offset =
    { desc; span = { start_offset; end_offset } }
  in
  let rec loop i tokens =
    let i = skip_ignored source i in
    if i >= String.length source then Ok (List.rev tokens)
    else
      match source.[i] with
      | '(' -> loop (i + 1) (token Lparen i (i + 1) :: tokens)
      | '\'' -> loop (i + 1) (token Quote i (i + 1) :: tokens)
      | '`' -> loop (i + 1) (token Syntax_quote i (i + 1) :: tokens)
      | '~' when i + 1 < String.length source && source.[i + 1] = '@' ->
          loop (i + 2) (token Unquote_splicing i (i + 2) :: tokens)
      | '~' -> loop (i + 1) (token Unquote i (i + 1) :: tokens)
      | '@' -> loop (i + 1) (token Deref i (i + 1) :: tokens)
      | '#' when i + 1 < String.length source && source.[i + 1] = '_' ->
          loop (i + 2) (token (Symbol "#_") i (i + 2) :: tokens)
      | '#' when i + 1 < String.length source && source.[i + 1] = '\'' ->
          let value, next = read_atom source (i + 2) in
          if value = "" then
            Error.error ~code:Error_code.Lexing ~phase:`Lexing
              "var quote expects a symbol"
          else loop next (token (Var_quote value) i next :: tokens)
      | '#' when i + 1 < String.length source && source.[i + 1] = '(' ->
          loop (i + 2) (token Anon_lparen i (i + 2) :: tokens)
      | ')' -> loop (i + 1) (token Rparen i (i + 1) :: tokens)
      | '[' -> loop (i + 1) (token Lbracket i (i + 1) :: tokens)
      | ']' -> loop (i + 1) (token Rbracket i (i + 1) :: tokens)
      | '#' when i + 1 < String.length source && source.[i + 1] = '{' ->
          loop (i + 2) (token Set_lbrace i (i + 2) :: tokens)
      | '#' when i + 1 < String.length source && source.[i + 1] = '"' -> (
          match read_regex source (i + 2) with
          | Ok (value, next) -> loop next (token (Regex value) i next :: tokens)
          | Error _ as err -> err)
      | '{' -> loop (i + 1) (token Lbrace i (i + 1) :: tokens)
      | '}' -> loop (i + 1) (token Rbrace i (i + 1) :: tokens)
      | '"' -> (
          match read_string source (i + 1) with
          | Ok (value, next) -> loop next (token (String value) i next :: tokens)
          | Error _ as err -> err)
      | ':' ->
          let value, next = read_atom source i in
          loop next (token (Keyword value) i next :: tokens)
      | _ ->
          let atom, next = read_atom source i in
          let token_result =
            match (atom, int_of_string_opt atom) with
            | "true", _ -> Ok (Bool true)
            | "false", _ -> Ok (Bool false)
            | "nil", _ -> Ok (Symbol atom)
            | ("##Inf" | "##-Inf" | "##NaN"), _ -> Ok (Float atom)
            | _, Some value -> Ok (Int value)
            | _ -> (
                match radix_integer_literal atom with
                | Some value -> Ok (Int value)
                | None -> (
                match strip_numeric_suffix 'N' atom with
                | Some integer -> (
                    match int_of_string_opt integer with
                    | Some value -> Ok (Int value)
                    | None -> (
                        match float_of_string_opt integer with
                        | Some value -> Ok (Float (string_of_float value))
                        | None -> Ok (Symbol atom)))
                | None -> (
                match strip_numeric_suffix 'M' atom with
                | Some decimal when valid_decimal_literal decimal ->
                    Ok (Decimal decimal)
                | Some _ -> Ok (Symbol atom)
                | None -> (
                match ratio_float_literal atom with
                | Some value -> Ok (Float value)
                | None -> (
                match char_of_atom atom with
                | Some value -> Ok (Char value)
                | None when looks_like_float atom -> (
                    match float_of_string_opt atom with
                    | Some _ -> Ok (Float atom)
                    | None -> Ok (Symbol atom))
                | None -> Ok (Symbol atom))))))
          in
          (match token_result with
          | Error _ as err -> err
          | Ok desc -> loop next (token desc i next :: tokens))
  in
  loop 0 []
