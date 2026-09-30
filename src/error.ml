type phase =
  [ `Lexing
  | `Parsing
  | `Semantic
  | `Lowering
  | `Ocaml
  | `Infrastructure ]

type related = {
  location : Location.t;
  message : string;
}

type text_edit = {
  location : Location.t;
  replacement : string;
}

type fix = {
  title : string;
  edits : text_edit list;
}

type type_term =
  | Type_atom of string
  | Type_application of string * type_term list
  | Type_function of type_term list * type_term
  | Type_tuple of type_term list
  | Type_record of (string * type_term) list

type type_path_element =
  | Type_argument of int
  | Function_parameter of int
  | Function_return
  | Tuple_item of int
  | Record_field of string

type type_difference = {
  path : type_path_element list;
  expected : type_term;
  actual : type_term;
}

type type_context =
  | Conditional_branch
  | Record_property of {
      record_name : string;
      property_name : string;
    }
  | Call_argument of {
      callee : string;
      index : int;
    }
  | Protocol_argument of {
      protocol : string;
      method_name : string;
      index : int;
    }
  | Annotation
  | Host_boundary of {
      callee : string;
      index : int;
    }

type type_mismatch = {
  context : type_context;
  expected : type_term;
  actual : type_term;
  difference : type_difference;
}

let type_difference expected actual =
  let rec first path expected actual =
    if expected = actual then None
    else
      let descend indexed_path expected_items actual_items =
        if List.length expected_items <> List.length actual_items then None
        else
          List.mapi
            (fun index (expected, actual) ->
              first (indexed_path index :: path) expected actual)
            (List.combine expected_items actual_items)
          |> List.find_map Fun.id
      in
      match (expected, actual) with
      | Type_application (expected_name, expected_args),
        Type_application (actual_name, actual_args)
        when expected_name = actual_name ->
          descend (fun index -> Type_argument index) expected_args actual_args
      | Type_function (expected_params, expected_return),
        Type_function (actual_params, actual_return) -> (
          match
            descend
              (fun index -> Function_parameter index)
              expected_params actual_params
          with
          | Some _ as difference -> difference
          | None -> first (Function_return :: path) expected_return actual_return)
      | Type_tuple expected_items, Type_tuple actual_items ->
          descend (fun index -> Tuple_item index) expected_items actual_items
      | Type_record expected_fields, Type_record actual_fields ->
          expected_fields
          |> List.find_map (fun (name, expected) ->
                 match List.assoc_opt name actual_fields with
                 | Some actual -> first (Record_field name :: path) expected actual
                 | None -> None)
      | _ -> None
      |> function
      | Some _ as difference -> difference
      | None -> Some { path = List.rev path; expected; actual }
  in
  first [] expected actual
  |> Option.value ~default:{ path = []; expected; actual }

let type_mismatch ~context ~expected ~actual =
  { context; expected; actual; difference = type_difference expected actual }

type t = {
  code : string;
  phase : phase;
  title : string;
  message : string;
  location : Location.t option;
  related : related list;
  hints : string list;
  fixes : fix list;
  type_mismatch : type_mismatch option;
}

let default_title = function
  | `Lexing | `Parsing -> "SYNTAX PROBLEM"
  | `Semantic -> "COMPILATION ERROR"
  | `Lowering -> "LOWERING ERROR"
  | `Ocaml -> "OCAML ERROR"
  | `Infrastructure -> "INFRASTRUCTURE ERROR"

let error ?location ?(related = []) ?(hints = []) ?(fixes = []) ?type_mismatch
    ?title ?(code = Error_code.Semantic) ?(phase = `Semantic) message =
  let title = Option.value title ~default:(default_title phase) in
  Error
    {
      code = Error_code.code code;
      phase;
      title;
      message;
      location;
      related;
      hints;
      fixes;
      type_mismatch;
    }

let with_location_if_missing location error =
  match (error.location, location) with
  | None, Some location -> { error with location = Some location }
  | _ -> error

let source_line source line_number =
  let rec find current start index =
    if current = line_number then
      let finish =
        match String.index_from_opt source start '\n' with
        | Some finish -> finish
        | None -> String.length source
      in
      Some (String.sub source start (finish - start))
    else
      match String.index_from_opt source index '\n' with
      | Some newline -> find (current + 1) (newline + 1) (newline + 1)
      | None -> None
  in
  if line_number < 1 then None else find 1 0 0

let utf8_columns source start_offset end_offset =
  let start_offset = max 0 start_offset in
  let end_offset = min (String.length source) end_offset in
  let rec count columns offset =
    if offset >= end_offset then columns
    else
      let byte = Char.code source.[offset] in
      let columns = if byte land 0xC0 = 0x80 then columns else columns + 1 in
      count columns (offset + 1)
  in
  count 0 start_offset

let render_location source (location : Location.t) =
  let start = location.loc_start in
  let finish = location.loc_end in
  match source_line source start.pos_lnum with
  | None -> ""
  | Some line ->
      let line_number = string_of_int start.pos_lnum in
      let column = utf8_columns source start.pos_bol start.pos_cnum in
      let width =
        if finish.pos_lnum = start.pos_lnum then
          max 1 (utf8_columns source start.pos_cnum finish.pos_cnum)
        else 1
      in
      let caret_padding = String.make (String.length line_number + 2 + column) ' ' in
      Printf.sprintf "%s| %s\n%s%s" line_number line caret_padding
        (String.make width '^')

let render_location_coordinates (location : Location.t) =
  let start = location.loc_start in
  let finish = location.loc_end in
  let filename =
    if start.pos_fname = "" then "<unknown>" else start.pos_fname
  in
  let start_column = max 0 (start.pos_cnum - start.pos_bol) in
  let end_column = max start_column (finish.pos_cnum - finish.pos_bol) in
  if start.pos_lnum = finish.pos_lnum then
    Printf.sprintf "File %S, line %d, columns %d-%d" filename start.pos_lnum
      start_column end_column
  else
    Printf.sprintf "File %S, line %d, column %d to line %d, column %d" filename
      start.pos_lnum start_column finish.pos_lnum end_column

let render ~source error =
  let filename =
    match error.location with
    | Some location when location.loc_start.Lexing.pos_fname <> "" ->
        location.loc_start.Lexing.pos_fname
    | Some _ | None -> "<unknown>"
  in
  let primary =
    match error.location with
    | None -> ""
    | Some location -> "\n\n" ^ render_location source location
  in
  let related =
    error.related
    |> List.map (fun (related : related) ->
           let related_filename =
             related.location.Location.loc_start.Lexing.pos_fname
           in
           let rendered_location =
             if related_filename = "" || related_filename = filename then
               render_location source related.location
             else render_location_coordinates related.location
           in
           "\n\n" ^ related.message ^ "\n" ^ rendered_location)
    |> String.concat ""
  in
  let hints =
    error.hints
    |> List.map (fun hint -> "\n\nHint: " ^ hint)
    |> String.concat ""
  in
  Printf.sprintf "-- %s [%s] -- %s\n\n%s%s%s%s" error.title error.code
    filename error.message primary related hints
