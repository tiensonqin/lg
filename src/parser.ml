open Ast

let omitted_reader_form = "\000lg-reader-omitted"
let spliced_reader_form = "\000lg-reader-spliced"

let is_omitted_reader_form located =
  located.form = FSymbol omitted_reader_form

let spliced_reader_forms located =
  match located.form with
  | FList (FSymbol marker :: _) when marker = spliced_reader_form ->
      Some located.children
  | _ -> None

let located ?(children = []) form span = { form; span; children }

let eof_offset : int option Domain.DLS.key = Domain.DLS.new_key (fun () -> None)

let current_eof_offset open_span =
  Domain.DLS.get eof_offset |> Option.value ~default:open_span.end_offset

let with_eof_offset offset f =
  let previous = Domain.DLS.get eof_offset in
  Domain.DLS.set eof_offset (Some offset);
  Fun.protect ~finally:(fun () -> Domain.DLS.set eof_offset previous) f

let location_of_span span =
  let position offset =
    { Lexing.pos_fname = ""; pos_lnum = 1; pos_bol = 0; pos_cnum = offset }
  in
  {
    Location.loc_start = position span.start_offset;
    loc_end = position span.end_offset;
    loc_ghost = false;
  }

let error_at span message =
  Error.error
    ~code:Error_code.Parsing ~phase:`Parsing
    ~location:(location_of_span span)
    message

let delimiter_description closing description =
  match (closing, description) with
  | Rparen, "list; expected ')'" -> ("list", '(', ')')
  | Rparen, "anonymous function; expected ')'" ->
      ("anonymous function", '(', ')')
  | Rparen, "reader conditional; expected ')'" ->
      ("reader conditional", '(', ')')
  | Rparen, "splicing reader conditional; expected ')'" ->
      ("splicing reader conditional", '(', ')')
  | Rbracket, "vector; expected ']'" -> ("vector", '[', ']')
  | Rbrace, "map; expected '}'" -> ("map", '{', '}')
  | Rbrace, "set; expected '}'" -> ("set", '{', '}')
  | _ -> ("collection", '(', ')')

let closing_character = function
  | Rparen -> Some ')'
  | Rbracket -> Some ']'
  | Rbrace -> Some '}'
  | _ -> None

let unfinished_delimiter_error closing open_span description =
  let name, _, expected = delimiter_description closing description in
  let eof = current_eof_offset open_span in
  let eof_location = location_of_span { start_offset = eof; end_offset = eof } in
  Error.error ~code:Error_code.Parsing ~phase:`Parsing
    ~title:("UNFINISHED " ^ String.uppercase_ascii name)
    ~location:eof_location
    ~related:
      [
        {
          Error.location = location_of_span open_span;
          message = Printf.sprintf "This %s starts here." name;
        };
      ]
    ~hints:
      [
        Printf.sprintf "Try adding a %c to close this %s." expected name;
      ]
    ~fixes:
      [
        {
          Error.title = Printf.sprintf "Insert missing %c" expected;
          edits = [ { Error.location = eof_location; replacement = String.make 1 expected } ];
        };
      ]
    (Printf.sprintf
       "I reached the end of input while looking for '%c' to close this %s."
       expected name)

let mismatched_delimiter_error closing open_span description actual_span actual =
  let name, opening, expected = delimiter_description closing description in
  let actual_location = location_of_span actual_span in
  Error.error ~code:Error_code.Parsing ~phase:`Parsing ~title:"MISMATCHED DELIMITER"
    ~location:actual_location
    ~related:
      [
        {
          Error.location = location_of_span open_span;
          message = Printf.sprintf "This %s starts here." name;
        };
      ]
    ~hints:
      [
        Printf.sprintf "Replace %c with %c to close this %s." actual expected
          name;
      ]
    ~fixes:
      [
        {
          Error.title = Printf.sprintf "Replace %c with %c" actual expected;
          edits =
            [
              {
                Error.location = actual_location;
                replacement = String.make 1 expected;
              };
            ];
        };
      ]
    (Printf.sprintf "This %s starts with '%c' but closes with '%c'." name
       opening actual)

let missing_reader_form_error prefix_span name =
  let eof = current_eof_offset prefix_span in
  Error.error ~code:Error_code.Parsing ~phase:`Parsing ~title:"MISSING FORM"
    ~location:(location_of_span { start_offset = eof; end_offset = eof })
    ~related:
      [
        {
          Error.location = location_of_span prefix_span;
          message = Printf.sprintf "This %s prefix is here." name;
        };
      ]
    ~hints:[ Printf.sprintf "Add a form after the %s prefix." name ]
    (Printf.sprintf "This %s needs a form after it." name)

let rec parse_one ~target ~reader_features = function
  | { desc = Symbol "#_"; span = reader_span } :: rest -> (
      match parse_present ~target ~reader_features rest with
      | Error _ -> error_at reader_span "reader discard expects a form"
      | Ok (discarded, rest) ->
          Ok
            ( located (FSymbol omitted_reader_form)
                { start_offset = reader_span.start_offset;
                  end_offset = discarded.span.end_offset;
                },
              rest ))
  | { desc = Symbol "#?"; span = reader_span }
    :: { desc = Lparen; span = open_span }
    :: rest ->
      Result.bind
        (parse_until ~target ~reader_features Rparen open_span "reader conditional; expected ')'"
           [] rest) (fun (forms, close_span, rest) ->
          select_reader_conditional reader_features reader_span close_span forms
          |> Result.map (fun selected -> (selected, rest)))
  | { desc = Symbol "#?@"; span = reader_span }
    :: { desc = Lparen; span = open_span }
    :: rest ->
      Result.bind
        (parse_until ~target ~reader_features Rparen open_span
           "splicing reader conditional; expected ')'" [] rest)
        (fun (forms, close_span, rest) ->
          Result.bind
            (select_reader_conditional reader_features reader_span close_span forms)
            (fun selected ->
                 let forms =
                   match selected.form with
                   | FSymbol omitted when omitted = omitted_reader_form -> Ok []
                   | FSymbol "nil" -> Ok []
                   | FList _ | FVector _ -> Ok selected.children
                   | _ ->
                       error_at selected.span
                         "splicing reader conditional must select a list or vector"
                 in
                 Result.map
                   (fun forms ->
                     ( located ~children:forms
                         (FList
                            (FSymbol spliced_reader_form
                            :: List.map (fun form -> form.form) forms))
                         {
                           start_offset = reader_span.start_offset;
                           end_offset = close_span.end_offset;
                         },
                       rest ))
                   forms))
  | { desc = Quote; span } :: rest ->
      parse_reader_prefix ~target ~reader_features span "quote" rest
  | { desc = Syntax_quote; span } :: rest ->
      parse_reader_prefix ~target ~reader_features span "syntax-quote" rest
  | { desc = Unquote; span } :: rest ->
      parse_reader_prefix ~target ~reader_features span "unquote" rest
  | { desc = Unquote_splicing; span } :: rest ->
      parse_reader_prefix ~target ~reader_features span "unquote-splicing" rest
  | { desc = Deref; span } :: rest ->
      parse_reader_prefix ~target ~reader_features span "deref" rest
  | { desc = Var_quote value; span } :: rest ->
      let symbol = located (FSymbol value) span in
      let head = located (FSymbol "__lg-var-quote") span in
      let children = [ head; symbol ] in
      Ok
        ( located ~children
            (FList (List.map (fun child -> child.form) children))
            span,
          rest )
  | { desc = Symbol "#uuid"; span = prefix_span } :: rest -> (
      match parse_one ~target ~reader_features rest with
      | Error _ -> error_at prefix_span "#uuid literal expects a string"
      | Ok (value, rest) -> (
          match value.form with
          | FString _ ->
              let head = located (FSymbol "#uuid") prefix_span in
              let children = [ head; value ] in
              Ok
                ( located ~children
                    (FList (List.map (fun child -> child.form) children))
                    {
                      start_offset = prefix_span.start_offset;
                      end_offset = value.span.end_offset;
                    },
                  rest )
          | _ -> error_at value.span "#uuid literal expects a string"))
  | { desc = Symbol "#inst"; span = prefix_span } :: rest -> (
      match parse_one ~target ~reader_features rest with
      | Error _ -> error_at prefix_span "#inst literal expects a string"
      | Ok (value, rest) -> (
          match value.form with
          | FString _ ->
              let head = located (FSymbol "#inst") prefix_span in
              let children = [ head; value ] in
              Ok
                ( located ~children
                    (FList (List.map (fun child -> child.form) children))
                    {
                      start_offset = prefix_span.start_offset;
                      end_offset = value.span.end_offset;
                    },
                  rest )
          | _ -> error_at value.span "#inst literal expects a string"))
  | { desc = Symbol "#js"; span = prefix_span } :: rest -> (
      match parse_one ~target ~reader_features rest with
      | Error _ -> error_at prefix_span "#js literal expects a map or vector"
      | Ok (value, rest) -> (
          match value.form with
          | FMap _ | FVector _ ->
              Ok
                ( {
                    value with
                    span =
                      {
                        start_offset = prefix_span.start_offset;
                        end_offset = value.span.end_offset;
                      };
                  },
                  rest )
          | _ -> error_at value.span "#js literal expects a map or vector"))
  | { desc = Symbol value; span } :: rest ->
      Ok (located (FSymbol value) span, rest)
  | { desc = Keyword value; span } :: rest ->
      Ok (located (FKeyword value) span, rest)
  | { desc = String value; span } :: rest ->
      Ok (located (FString value) span, rest)
  | { desc = Regex value; span } :: rest ->
      Ok (located (FRegex value) span, rest)
  | { desc = Int value; span } :: rest -> Ok (located (FInt value) span, rest)
  | { desc = Float value; span } :: rest ->
      Ok (located (FFloat value) span, rest)
  | { desc = Decimal value; span } :: rest ->
      Ok (located (FDecimal value) span, rest)
  | { desc = Char value; span } :: rest -> Ok (located (FChar value) span, rest)
  | { desc = Bool value; span } :: rest -> Ok (located (FBool value) span, rest)
  | { desc = Lparen; span = open_span } :: rest ->
      parse_until ~target ~reader_features Rparen open_span "list; expected ')'" [] rest
      |> Result.map (fun (forms, close_span, rest) ->
          ( located ~children:forms
              (FList (List.map (fun form -> form.form) forms))
              {
                start_offset = open_span.start_offset;
                end_offset = close_span.end_offset;
              },
            rest ))
  | { desc = Anon_lparen; span = open_span } :: rest ->
      Result.bind
        (parse_until ~target ~reader_features Rparen open_span
           "anonymous function; expected ')'" [] rest)
        (fun (forms, close_span, rest) ->
          anonymous_function open_span close_span forms
          |> Result.map (fun form -> (form, rest)))
  | { desc = Lbracket; span = open_span } :: rest ->
      parse_until ~target ~reader_features Rbracket open_span "vector; expected ']'" [] rest
      |> Result.map (fun (forms, close_span, rest) ->
          ( located ~children:forms
              (FVector (List.map (fun form -> form.form) forms))
              {
                start_offset = open_span.start_offset;
                end_offset = close_span.end_offset;
              },
            rest ))
  | { desc = Lbrace; span = open_span } :: rest ->
      Result.bind
        (parse_until ~target ~reader_features Rbrace open_span "map; expected '}'" [] rest)
        (fun (forms, close_span, rest) ->
          map_of_forms open_span close_span forms
          |> Result.map (fun form -> (form, rest)))
  | { desc = Set_lbrace; span = open_span } :: rest ->
      parse_until ~target ~reader_features Rbrace open_span "set; expected '}'" [] rest
      |> Result.map (fun (forms, close_span, rest) ->
          let head = located (FSymbol "__lg_hash-set") open_span in
          let children = head :: forms in
          ( located ~children
              (FList (List.map (fun form -> form.form) children))
              {
                start_offset = open_span.start_offset;
                end_offset = close_span.end_offset;
              },
            rest ))
  | [] -> Error.error ~code:Error_code.Parsing ~phase:`Parsing "expected form"
  | { desc = Rparen; span } :: _ -> error_at span "unexpected ')'"
  | { desc = Rbracket; span } :: _ -> error_at span "unexpected ']'"
  | { desc = Rbrace; span } :: _ -> error_at span "unexpected '}'"

and parse_reader_prefix ~target ~reader_features prefix_span name tokens =
  match tokens with
  | [] -> missing_reader_form_error prefix_span name
  | _ -> (
      match parse_one ~target ~reader_features tokens with
  | Error _ as err -> err
  | Ok (value, rest) ->
      let head = located (FSymbol name) prefix_span in
      let children = [ head; value ] in
      let span =
        {
          start_offset = prefix_span.start_offset;
          end_offset = value.span.end_offset;
        }
      in
      Ok
        ( located ~children
            (FList (List.map (fun child -> child.form) children))
            span,
          rest ))

and anonymous_function open_span close_span forms =
  let span =
    {
      start_offset = open_span.start_offset;
      end_offset = close_span.end_offset;
    }
  in
  let rec highest_parameter acc (form : located_form) =
    let own =
      match form.form with
      | FSymbol "%" -> max acc 1
      | FSymbol name
        when String.length name > 1 && name.[0] = '%' -> (
          match
            int_of_string_opt (String.sub name 1 (String.length name - 1))
          with
          | Some index when index > 0 -> max acc index
          | _ -> acc)
      | _ -> acc
    in
    List.fold_left highest_parameter own form.children
  in
  let parameter_count = List.fold_left highest_parameter 0 forms in
  let rec parameters index acc =
    if index = 0 then acc
    else parameters (index - 1) (FSymbol ("%" ^ string_of_int index) :: acc)
  in
  let rewrite_symbol = function
    | FSymbol "%" -> FSymbol "%1"
    | form -> form
  in
  let rec rewrite (form : located_form) =
    let children = List.map rewrite form.children in
    let rec map_pairs pairs = function
      | key :: value :: rest ->
          map_pairs ((key.form, value.form) :: pairs) rest
      | [] -> Some (List.rev pairs)
      | [ _ ] -> None
    in
    let rewritten_form =
      match rewrite_symbol form.form with
      | FList _ -> FList (List.map (fun child -> child.form) children)
      | FVector _ -> FVector (List.map (fun child -> child.form) children)
      | FMap entries -> (
          match map_pairs [] children with
          | Some entries -> FMap entries
          | None -> FMap entries)
      | rewritten -> rewritten
    in
    { form with form = rewritten_form; children }
  in
  let forms = List.map rewrite forms in
  let body = located ~children:forms (FList (List.map (fun form -> form.form) forms)) span in
  let params = located (FVector (parameters parameter_count [])) span in
  let head = located (FSymbol "fn") open_span in
  let children = [ head; params; body ] in
  Ok (located ~children (FList (List.map (fun form -> form.form) children)) span)

and parse_until ~target ~reader_features closing open_span description acc = function
  | [] -> unfinished_delimiter_error closing open_span description
  | { desc; span } :: rest when desc = closing -> Ok (List.rev acc, span, rest)
  | ({ desc; span } :: _ as tokens) -> (
      match closing_character desc with
      | Some actual ->
          mismatched_delimiter_error closing open_span description span actual
      | None -> (
          match parse_one ~target ~reader_features tokens with
          | Ok (form, rest) when is_omitted_reader_form form ->
              parse_until ~target ~reader_features closing open_span description acc rest
          | Ok (form, rest) -> (
              match spliced_reader_forms form with
              | Some forms ->
                  parse_until ~target ~reader_features closing open_span description
                    (List.rev_append forms acc) rest
              | None ->
                  parse_until ~target ~reader_features closing open_span description
                    (form :: acc) rest)
          | Error _ as err -> err))

and map_of_forms open_span close_span forms =
  let rec remove_metadata acc = function
    | { form = FSymbol "^"; span = metadata_span; _ } :: _metadata :: form
      :: rest ->
        let form =
          {
            form with
            span =
              {
                start_offset = metadata_span.start_offset;
                end_offset = form.span.end_offset;
              };
          }
        in
        remove_metadata (form :: acc) rest
    | { form = FSymbol "^"; span = metadata_span; _ } :: _ ->
        error_at metadata_span "metadata expects a form"
    | { form = FSymbol metadata; span = metadata_span; _ } :: form :: rest
      when String.starts_with ~prefix:"^" metadata ->
        let form =
          {
            form with
            span =
              {
                start_offset = metadata_span.start_offset;
                end_offset = form.span.end_offset;
              };
          }
        in
        remove_metadata (form :: acc) rest
    | form :: rest -> remove_metadata (form :: acc) rest
    | [] -> Ok (List.rev acc)
  in
  let rec pairs acc = function
    | [] -> Ok (List.rev acc)
    | key :: value :: rest -> pairs ((key, value) :: acc) rest
    | [ key ] ->
        Error.error ~code:Error_code.Parsing ~phase:`Parsing ~title:"INCOMPLETE MAP"
          ~location:(location_of_span key.span)
          ~related:
            [
              {
                Error.location = location_of_span open_span;
                message = "This map starts here.";
              };
            ]
          ~hints:[ "Add a value after this key, or remove the key." ]
          "This map has a key with no value."
  in
  Result.bind (remove_metadata [] forms) (fun forms ->
      Result.map
        (fun pairs ->
          located
            ~children:
              (pairs |> List.concat_map (fun (key, value) -> [ key; value ]))
            (FMap
               (pairs |> List.map (fun (key, value) -> (key.form, value.form))))
            {
              start_offset = open_span.start_offset;
              end_offset = close_span.end_offset;
            })
        (pairs [] forms))

and parse_present ~target ~reader_features tokens =
  match parse_one ~target ~reader_features tokens with
  | Ok (form, rest) when is_omitted_reader_form form ->
      parse_present ~target ~reader_features rest
  | result -> result

and select_reader_conditional reader_features reader_span close_span forms =
  let conditional_span =
    {
      start_offset = reader_span.start_offset;
      end_offset = close_span.end_offset;
    }
  in
  let metadata_annotation metadata =
    match metadata.form with
    | FMap entries -> (
        match List.assoc_opt (FKeyword ":tag") entries with
        | Some (FString tag | FSymbol tag | FKeyword tag) ->
            Some (located (FSymbol ("^" ^ tag)) metadata.span)
        | Some _ | None -> None)
    | _ -> None
  in
  let branch_value value rest =
    match (value.form, rest) with
    | FSymbol "^", metadata :: actual :: rest ->
        let forms =
          match metadata_annotation metadata with
          | Some annotation -> [ annotation; actual ]
          | None -> [ actual ]
        in
        Ok (forms, rest)
    | FSymbol metadata, actual :: rest
      when String.starts_with ~prefix:"^" metadata ->
        Ok ([ value; actual ], rest)
    | FSymbol "^", _ ->
        error_at value.span "reader conditional metadata expects a form"
    | _ -> Ok ([ value ], rest)
  in
  let rec collect seen branches = function
    | [] -> Ok (List.rev branches)
    | [ feature ] -> (
        match feature.form with
        | FKeyword name ->
            Error.error ~code:Error_code.Parsing ~phase:`Parsing
              ~title:"INCOMPLETE READER CONDITIONAL"
              ~location:(location_of_span feature.span)
              ~related:
                [
                  {
                    Error.location = location_of_span reader_span;
                    message = "This reader conditional starts here.";
                  };
                ]
              ~hints:[ "Add a form after this feature, or remove the feature." ]
              (Printf.sprintf
                 "The %s feature in this reader conditional has no form." name)
        | _ ->
            error_at feature.span
              "reader conditional feature must be a keyword")
    | feature :: value :: rest -> (
        match feature.form with
        | FKeyword name when List.mem name seen ->
            error_at feature.span
              ("duplicate reader conditional feature " ^ name)
        | FKeyword name ->
            Result.bind (branch_value value rest) (fun (value, rest) ->
                collect (name :: seen) ((name, value) :: branches) rest)
        | _ ->
            error_at feature.span "reader conditional feature must be a keyword"
        )
  in
  Result.bind (collect [] [] forms) (fun branches ->
      let selected_form = function
        | [ selected ] -> Ok selected
        | selected ->
            Ok
              (located ~children:selected
                 (FList
                    (FSymbol spliced_reader_form
                    :: List.map (fun form -> form.form) selected))
                 conditional_span)
      in
      let selected =
        List.find_map
          (fun feature -> List.assoc_opt feature branches)
          reader_features
      in
      match selected with
      | Some selected -> selected_form selected
      | None -> (
          match List.assoc_opt ":default" branches with
          | Some selected -> selected_form selected
          | None -> Ok (located (FSymbol omitted_reader_form) conditional_span)))

let parse_located ?(target = Target.default) ?reader_features ?eof_offset
    (tokens : token list) =
  let reader_features =
    Option.value reader_features ~default:(Target.reader_features target)
  in
  let rec loop forms = function
    | [] -> Ok (List.rev forms)
    | tokens -> (
        match parse_one ~target ~reader_features tokens with
        | Ok (form, rest) when is_omitted_reader_form form -> loop forms rest
        | Ok (form, rest) -> loop (form :: forms) rest
        | Error _ as err -> err)
  in
  let eof_offset =
    Option.value eof_offset
      ~default:
        (match List.rev tokens with
        | token :: _ -> token.span.end_offset
        | [] -> 0)
  in
  with_eof_offset eof_offset (fun () -> loop [] tokens)

let parse_located_recovering ?(target = Target.default) ?reader_features
    ?eof_offset (tokens : token list) =
  let reader_features =
    Option.value reader_features ~default:(Target.reader_features target)
  in
  let rec loop forms = function
    | [] -> (List.rev forms, None)
    | tokens -> (
        match parse_one ~target ~reader_features tokens with
        | Ok (form, rest) when is_omitted_reader_form form -> loop forms rest
        | Ok (form, rest) -> loop (form :: forms) rest
        | Error error -> (List.rev forms, Some error))
  in
  let eof_offset =
    Option.value eof_offset
      ~default:
        (match List.rev tokens with
        | token :: _ -> token.span.end_offset
        | [] -> 0)
  in
  with_eof_offset eof_offset (fun () -> loop [] tokens)

let parse ?(target = Target.default) ?reader_features ?eof_offset tokens =
  parse_located ~target ?reader_features ?eof_offset tokens
  |> Result.map (List.map (fun located -> located.form))
