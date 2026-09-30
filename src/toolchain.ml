type parser_result = {
  target : Target.t;
  source_unit : string;
  ast : Ast.form list;
  locations : Location.t list;
  form_locations : Source_context.entry list;
  filename : string;
  parsed_as : [ `Lg | `Mli of Parsetree.signature ];
}

type prepared_source = {
  parsed : parser_result;
  required_packages : string list;
}

type typed_result = {
  ast : Ast.form list;
  items : Lowered.compiled_item list;
  locations : Location.t list;
  typecheck_state : Typecheck.state;
}

type parsetree_result = {
  ast : Ast.form list;
  items : Lowered.compiled_item list;
  structure : Parsetree.structure;
}

type diagnostic_severity = [ `Warning ]

type diagnostic = {
  code : string;
  phase : Error.phase;
  message : string;
  severity : diagnostic_severity;
  location : Location.t option;
}

type compilation = { ocaml_source : string; diagnostics : diagnostic list }

type repl_form_kind =
  | Repl_value
  | Repl_definition of {
      name : string;
      type_name : string;
    }
  | Repl_namespace of string
  | Repl_summary of string

type repl_compilation = {
  structure : Parsetree.structure;
  kind : repl_form_kind;
}

type language_analysis = {
  typed_structure : Typedtree.structure;
  compiler_env : Env.t;
  typecheck_state : Typecheck.state;
  diagnostics : diagnostic list;
  info_tree : Info_tree.entry list;
}

type state = {
  typecheck_state : Typecheck.state;
  located_items : (Location.t * Lowered.compiled_item) list;
  requested_set_modules : string list;
  ocaml_env : Env.t option;
  pending_interfaces : (string * Parsetree.signature) list;
}

let state_environment state =
  state.ocaml_env
  |> Option.value ~default:Env.empty

module String_set = Set.Make (String)
let compiled_interface_cache = Hashtbl.create 32

module type FRONTEND = sig
  val implementation :
    ?target:Target.t ->
    ?reader_features:string list ->
    ?filename:string ->
    string ->
    (parser_result, Error.t) result
end

module Lg_frontend : FRONTEND = struct
  let line_starts source =
    let starts = ref [ 0 ] in
    String.iteri
      (fun index char ->
        if char = '\n' then starts := (index + 1) :: !starts)
      source;
    Array.of_list (List.rev !starts)

  let position filename line_starts offset =
    let rec search low high =
      if low > high then high
      else
        let middle = low + ((high - low) / 2) in
        if line_starts.(middle) <= offset then search (middle + 1) high
        else search low (middle - 1)
    in
    let line_index = search 0 (Array.length line_starts - 1) in
    {
      Lexing.pos_fname = filename;
      pos_lnum = line_index + 1;
      pos_bol = line_starts.(line_index);
      pos_cnum = offset;
    }

  let location filename line_starts (span : Ast.source_span) =
    {
      Location.loc_start = position filename line_starts span.start_offset;
      loc_end = position filename line_starts span.end_offset;
      loc_ghost = false;
    }

  let normalize_error_location filename line_starts (error : Error.t) =
    let normalize (location : Location.t) =
      {
        location with
        Location.loc_start =
          position filename line_starts location.loc_start.Lexing.pos_cnum;
        loc_end =
          position filename line_starts location.loc_end.Lexing.pos_cnum;
      }
    in
    {
      error with
      location = Option.map normalize error.location;
      related =
        List.map
          (fun (related : Error.related) ->
            { related with location = normalize related.location })
          error.related;
    }

  let namespace_scope_form span namespace_name =
    {
      Ast.form =
        Ast.FList [ Ast.FSymbol "namespace-scope"; Ast.FSymbol namespace_name ];
      span;
      children = [];
    }

  let metadata_symbol name = String.starts_with ~prefix:"^" name

  let host_type_hint name =
    metadata_symbol name && not (String.starts_with ~prefix:"^:" name)

  let definition_type_hint name =
    host_type_hint name
    || (String.contains name '<' && String.ends_with ~suffix:">" name)
    || List.mem name
         [
           "^:int";
           "^:ordering";
           "^:float";
           "^:char";
           "^:string";
           "^:symbol";
           "^:keyword";
           "^:bool";
           "^:unit";
           "^:buffer";
         ]

  let supported_type_hint name =
    if not (host_type_hint name) then false
    else
      let type_name = String.sub name 1 (String.length name - 1) in
      let qualified_record_hint =
        match String.rindex_opt type_name '/' with
        | Some separator when separator < String.length type_name - 1 ->
            let local_name =
              String.sub type_name (separator + 1)
                (String.length type_name - separator - 1)
            in
            not (String.contains local_name '.')
        | Some _ | None -> false
      in
      Option.is_some (Host_interop.type_annotation type_name)
      || qualified_record_hint
      || (not (String.contains type_name '.'))
         && not (String.contains type_name '/')

  let metadata_map_annotations entries =
    entries
    |> List.filter_map (function
         | Ast.FKeyword ":tag", (Ast.FString tag | Ast.FSymbol tag) ->
             Some (Ast.FSymbol ("^" ^ tag))
         | Ast.FKeyword ":tag", Ast.FKeyword tag ->
             Some (Ast.FSymbol ("^" ^ tag))
         | Ast.FKeyword ":dynamic", Ast.FBool true ->
             Some (Ast.FSymbol "^:dynamic")
         | _ -> None)

  let keyword_metadata_value metadata form =
    if
      String.starts_with ~prefix:"^:" metadata
      && match form with Ast.FVector _ | Ast.FMap _ -> true | _ -> false
    then
      let keyword = String.sub metadata 1 (String.length metadata - 1) in
      Some
        (Ast.FList
           [
             Ast.FSymbol "with-meta";
             form;
             Ast.FMap [ (Ast.FKeyword keyword, Ast.FBool true) ];
           ])
    else None

  let rec drop_definition_metadata = function
    | Ast.FSymbol "^" :: Ast.FMap _ :: rest ->
        drop_definition_metadata rest
    | Ast.FSymbol metadata :: rest when metadata_symbol metadata ->
        drop_definition_metadata rest
    | forms -> forms

  let dynamic_definition_forms forms =
    match forms with
    | Ast.FSymbol "^" :: Ast.FMap entries :: rest
      when List.mem (Ast.FKeyword ":dynamic", Ast.FBool true) entries ->
        Ast.FSymbol "^:dynamic" :: drop_definition_metadata rest
    | Ast.FSymbol "^:dynamic" :: rest ->
        Ast.FSymbol "^:dynamic" :: drop_definition_metadata rest
    | forms -> drop_definition_metadata forms

  let rec normalize_metadata = function
    | Ast.FList
        (Ast.FSymbol (("def" | "defonce") as head) :: forms) ->
        (match forms with
        | Ast.FSymbol "^:dynamic"
          :: Ast.FSymbol annotation
          :: name :: [ value ]
          when definition_type_hint annotation ->
            Ast.FList
              [
                Ast.FSymbol head;
                Ast.FSymbol "^:dynamic";
                normalize_metadata name;
                Ast.FList
                  [
                    Ast.FSymbol "__type-hint";
                    Ast.FSymbol annotation;
                    normalize_metadata value;
                  ];
              ]
        | Ast.FSymbol metadata
          :: Ast.FSymbol annotation
          :: name :: [ value ]
          when metadata_symbol metadata && definition_type_hint annotation ->
            Ast.FList
              [
                Ast.FSymbol head;
                normalize_metadata name;
                Ast.FList
                  [
                    Ast.FSymbol "__type-hint";
                    Ast.FSymbol annotation;
                    normalize_metadata value;
                  ];
              ]
        | Ast.FSymbol annotation :: name :: [ value ]
          when definition_type_hint annotation ->
            Ast.FList
              [
                Ast.FSymbol head;
                normalize_metadata name;
                Ast.FList
                  [
                    Ast.FSymbol "__type-hint";
                    Ast.FSymbol annotation;
                    normalize_metadata value;
                  ];
              ]
        | forms ->
            let forms = dynamic_definition_forms forms in
            let forms =
              match forms with
              | Ast.FSymbol "^:dynamic" :: rest ->
                  Ast.FSymbol "^:dynamic" :: normalize_metadata_sequence rest
              | forms -> normalize_metadata_sequence forms
            in
            Ast.FList (Ast.FSymbol head :: forms))
    | Ast.FList
        (Ast.FSymbol (("defn" | "defn-") as head) :: forms)
      ->
        (match forms with
        | Ast.FSymbol "^:dynamic" :: name :: rest ->
            Ast.FList
              (Ast.FSymbol head :: Ast.FSymbol "^:dynamic"
              :: normalize_metadata name
              :: normalize_metadata_sequence rest)
        | Ast.FSymbol annotation :: name :: rest
          when definition_type_hint annotation ->
            Ast.FList
              (Ast.FSymbol head :: normalize_metadata name
              :: Ast.FSymbol annotation
              :: normalize_metadata_sequence rest)
        | forms ->
            Ast.FList
              (Ast.FSymbol head
              :: normalize_metadata_sequence
                   (drop_definition_metadata forms)))
    | Ast.FList forms -> Ast.FList (normalize_metadata_sequence forms)
    | Ast.FVector forms ->
        Ast.FVector (normalize_vector_metadata_sequence forms)
    | Ast.FMap entries ->
        let forms =
          entries
          |> List.concat_map (fun (key, value) -> [ key; value ])
          |> normalize_metadata_sequence
        in
        let rec pairs acc = function
          | key :: value :: rest -> pairs ((key, value) :: acc) rest
          | [] -> Some (List.rev acc)
          | [ _ ] -> None
        in
        (match pairs [] forms with
        | Some entries -> Ast.FMap entries
        | None -> Ast.FMap entries)
    | form -> form

  and normalize_metadata_sequence = function
    | Ast.FSymbol "^" :: Ast.FMap entries :: form :: rest ->
        normalize_metadata_sequence
          (metadata_map_annotations entries @ (form :: rest))
    | Ast.FSymbol metadata :: form :: rest -> (
        match keyword_metadata_value metadata form with
        | Some annotated ->
            normalize_metadata annotated :: normalize_metadata_sequence rest
        | None when supported_type_hint metadata ->
            Ast.FList
              [
                Ast.FSymbol "__type-hint";
                Ast.FSymbol metadata;
                normalize_metadata form;
              ]
            :: normalize_metadata_sequence rest
        | None when host_type_hint metadata || metadata_symbol metadata ->
            normalize_metadata_sequence (form :: rest)
        | None ->
            normalize_metadata (Ast.FSymbol metadata)
            :: normalize_metadata_sequence (form :: rest))
    | form :: rest ->
        normalize_metadata form :: normalize_metadata_sequence rest
    | [] -> []

  and normalize_vector_metadata_sequence = function
    | Ast.FSymbol "^" :: Ast.FMap entries :: form :: rest ->
        normalize_vector_metadata_sequence
          (metadata_map_annotations entries @ (form :: rest))
    | Ast.FSymbol metadata :: form :: rest -> (
        match keyword_metadata_value metadata form with
        | Some annotated ->
            normalize_metadata annotated
            :: normalize_vector_metadata_sequence rest
        | None when supported_type_hint metadata ->
            Ast.FSymbol metadata
            :: normalize_vector_metadata_sequence (form :: rest)
        | None when host_type_hint metadata ->
            normalize_vector_metadata_sequence (form :: rest)
        | None ->
            normalize_metadata (Ast.FSymbol metadata)
            :: normalize_vector_metadata_sequence (form :: rest))
    | form :: rest ->
        normalize_metadata form :: normalize_vector_metadata_sequence rest
    | [] -> []

  let normalize_located_metadata located =
    { located with Ast.form = normalize_metadata located.Ast.form }

  let extract_compile_time_helpers located_ast =
    let source_core =
      List.exists
        (fun located ->
          match located.Ast.form with
          | Ast.FList (Ast.FSymbol "ns" :: Ast.FSymbol "clojure.core" :: _) ->
              true
          | Ast.FList
              [ Ast.FSymbol "namespace-scope"; Ast.FSymbol "clojure.core" ] ->
              true
          | _ -> false)
        located_ast
    in
    let add_reference refs name =
      if source_core && Macro_expander.is_compile_time_primitive name then refs
      else String_set.add name refs
    in
    let binding_names names pattern =
      Destructure.pattern_names pattern
      |> List.fold_left
           (fun names name ->
             if name = "&" then names else String_set.add name names)
           names
    in
    let rec quoted_refs bound refs = function
      | Ast.FList [ Ast.FSymbol ("unquote" | "unquote-splicing"); expression ]
        ->
          form_refs bound refs expression
      | Ast.FList forms | Ast.FVector forms ->
          List.fold_left (quoted_refs bound) refs forms
      | Ast.FMap entries ->
          List.fold_left
            (fun refs (key, value) ->
              quoted_refs bound (quoted_refs bound refs key) value)
            refs entries
      | _ -> refs
    and binding_refs bound refs bindings body =
      let rec pairs bound refs = function
        | pattern :: value :: rest ->
            let refs = form_refs bound refs value in
            pairs (binding_names bound pattern) refs rest
        | _ ->
            List.fold_left (form_refs bound) refs body
      in
      pairs bound refs bindings
    and function_refs bound refs forms =
      let arity_refs bound refs = function
        | Ast.FVector parameters :: body ->
            let bound = List.fold_left binding_names bound parameters in
            List.fold_left (form_refs bound) refs body
        | forms -> List.fold_left (form_refs bound) refs forms
      in
      match forms with
      | Ast.FSymbol name :: rest ->
          function_refs (String_set.add name bound) refs rest
      | Ast.FVector _ :: _ -> arity_refs bound refs forms
      | clauses ->
          List.fold_left
            (fun refs -> function
              | Ast.FList clause -> arity_refs bound refs clause
              | form -> form_refs bound refs form)
            refs clauses
    and form_refs bound refs = function
      | Ast.FList [ Ast.FSymbol "syntax-quote"; quoted ] ->
          quoted_refs bound refs quoted
      | Ast.FList [ Ast.FSymbol ("quote" | "var"); _ ] -> refs
      | Ast.FList
          (Ast.FSymbol ("let" | "loop" | "binding")
          :: Ast.FVector bindings :: body) ->
          binding_refs bound refs bindings body
      | Ast.FList
          (Ast.FSymbol ("if-let" | "when-let" | "if-some" | "when-some")
          :: Ast.FVector bindings :: body) ->
          binding_refs bound refs bindings body
      | Ast.FList (Ast.FSymbol "fn" :: forms) ->
          function_refs bound refs forms
      | Ast.FList
          (Ast.FSymbol "catch" :: _exception_type :: Ast.FSymbol name :: body)
        ->
          List.fold_left (form_refs (String_set.add name bound)) refs body
      | Ast.FList (Ast.FSymbol name :: forms) ->
          let refs =
            if String_set.mem name bound then refs else add_reference refs name
          in
          List.fold_left (form_refs bound) refs forms
      | Ast.FList forms | Ast.FVector forms ->
          List.fold_left (form_refs bound) refs forms
      | Ast.FMap entries ->
          List.fold_left
            (fun refs (key, value) ->
              form_refs bound (form_refs bound refs key) value)
            refs entries
      | Ast.FSymbol name ->
          if String_set.mem name bound then refs else add_reference refs name
      | _ -> refs
    in
    let definition_arities forms =
      let rec drop_prefix = function
        | (Ast.FString _ | Ast.FMap _) :: rest -> drop_prefix rest
        | Ast.FSymbol annotation :: rest
          when String.starts_with ~prefix:"^" annotation ->
            drop_prefix rest
        | forms -> forms
      in
      let forms = drop_prefix forms in
      let parameter_names parameters =
        parameters
        |> List.filter_map (function
             | Ast.FSymbol name when name <> "&" -> Some name
             | _ -> None)
        |> String_set.of_list
      in
      match forms with
      | Ast.FVector parameters :: body ->
          [ (parameter_names parameters, body) ]
      | clauses ->
          clauses
          |> List.filter_map (function
               | Ast.FList (Ast.FVector parameters :: body) ->
                   Some (parameter_names parameters, body)
               | _ -> None)
    in
    let scan_definition refs forms =
      definition_arities forms
      |> List.fold_left
           (fun refs (parameters, body) ->
             let body_refs =
               List.fold_left (form_refs parameters) String_set.empty body
             in
             String_set.union refs body_refs)
           refs
    in
    let definitions =
      located_ast
      |> List.filter_map (fun located ->
             match located.Ast.form with
             | Ast.FList
                 (Ast.FSymbol ("def" | "defonce" | "defn" | "defn-")
              :: Ast.FSymbol name
              :: forms) ->
                 Some (name, forms)
             | _ -> None)
    in
    let initial_refs =
      List.fold_left
        (fun refs located ->
          match located.Ast.form with
          | Ast.FList (Ast.FSymbol "defmacro" :: _name :: forms) ->
              scan_definition refs forms
          | _ -> refs)
        String_set.empty located_ast
    in
    let rec close refs =
      let expanded =
        List.fold_left
          (fun refs (name, forms) ->
            if String_set.mem name refs then scan_definition refs forms
            else refs)
          refs definitions
      in
      if String_set.equal refs expanded then refs else close expanded
    in
    let helper_names = close initial_refs in
    List.map
      (fun located ->
        match located.Ast.form with
        | Ast.FList (Ast.FSymbol ("defn" | "defn-") :: Ast.FSymbol name :: forms)
          when String_set.mem name helper_names ->
            {
              located with
              Ast.form =
                Ast.FList
                  (Ast.FSymbol "macro-helper-defn" :: Ast.FSymbol name :: forms);
            }
        | Ast.FList
            (Ast.FSymbol ("def" | "defonce") :: Ast.FSymbol name :: forms)
          when String_set.mem name helper_names ->
            {
              located with
              Ast.form =
                Ast.FList
                  (Ast.FSymbol "macro-helper-def" :: Ast.FSymbol name :: forms);
            }
        | _ -> located)
      located_ast

  let lower_namespace located_ast =
    let is_namespace = function
      | { Ast.form = Ast.FList (Ast.FSymbol "ns" :: _); _ } -> true
      | _ -> false
    in
    match located_ast with
    | [] -> Ok []
    | { Ast.form = Ast.FList (Ast.FSymbol "ns" :: forms); span; _ } :: body -> (
        if List.exists is_namespace body then
          Error.error ~code:Error_code.Semantic "ns may only appear once at the start of a file"
        else
          let rec drop_namespace_metadata = function
            | Ast.FSymbol metadata :: rest
              when String.starts_with ~prefix:"^" metadata ->
                drop_namespace_metadata rest
            | forms -> forms
          in
          match drop_namespace_metadata forms with
          | Ast.FSymbol namespace_name :: clauses ->
              let segments = String.split_on_char '.' namespace_name in
              if List.exists (fun segment -> segment = "") segments then
                Error.error ~code:Error_code.Interop "ns expects a namespace symbol and optional clauses"
              else
                let import_require_entry = function
                  | Ast.FVector (Ast.FSymbol package_name :: _imported_names)
                    when String.starts_with ~prefix:"clojure." package_name
                         || String.starts_with ~prefix:"java." package_name ->
                      Ok None
                  | Ast.FVector (Ast.FSymbol package_name :: imported_names)
                    ->
                      if
                        List.for_all
                          (function Ast.FSymbol _ -> true | _ -> false)
                          imported_names
                      then
                        Ok
                          (Some
                             (Ast.FVector
                                [ Ast.FSymbol package_name;
                                  Ast.FKeyword ":refer";
                                  Ast.FVector imported_names ]))
                      else
                        Error.error ~code:Error_code.Namespace
                          "ns :import class names must be symbols"
                  | form ->
                      Error.error ~code:Error_code.Macro
                        ("lg namespaces do not support :import "
                        ^ Macro_expander.string_of_form form)
                in
                let rec import_require_entries imported = function
                  | [] -> Ok (List.rev imported)
                  | entry :: rest -> (
                      match import_require_entry entry with
                      | Error _ as err -> err
                      | Ok None -> import_require_entries imported rest
                      | Ok (Some require_entry) ->
                          import_require_entries
                            (require_entry :: imported)
                            rest)
                in
                let rec parse_clauses require_entries exclusions =
                  function
                  | [] ->
                      Ok
                        ( List.rev require_entries |> List.concat,
                          List.rev exclusions |> List.concat )
                  | Ast.FList
                      (Ast.FKeyword (":require" | ":require-macros") :: entries)
                    :: rest ->
                      parse_clauses
                        (entries :: require_entries)
                        exclusions rest
                  | Ast.FList
                      [
                        Ast.FKeyword ":refer-clojure";
                        Ast.FKeyword ":exclude";
                        Ast.FVector names;
                      ]
                    :: rest ->
                      parse_clauses require_entries (names :: exclusions) rest
                  | Ast.FList (Ast.FKeyword ":import" :: entries) :: rest -> (
                      match import_require_entries [] entries with
                      | Error _ as err -> err
                      | Ok imported ->
                          parse_clauses
                            (imported :: require_entries)
                            exclusions rest)
                  | _ ->
                      Error.error ~code:Error_code.Semantic
                          "ns supports :require, :require-macros, :refer-clojure \
                         :exclude clauses"
                in
                Result.map
                  (fun (require_entries, exclusions) ->
                    let namespace_form =
                      namespace_scope_form span namespace_name
                    in
                    let synthetic_form head entries =
                      {
                        Ast.form = Ast.FList (Ast.FSymbol head :: entries);
                        span;
                        children = [];
                      }
                    in
                    let clauses =
                      []
                      |> (fun forms ->
                           if require_entries = [] then forms
                           else synthetic_form "require" require_entries :: forms)
                      |> (fun forms ->
                           if exclusions = [] then forms
                           else
                             synthetic_form "refer-clojure-exclude" exclusions
                             :: forms)
                      |> List.rev
                    in
                    (namespace_form :: clauses) @ body)
                  (parse_clauses [] [] clauses)
          | _ ->
              Error.error ~code:Error_code.Arity "ns expects a namespace symbol and optional clauses")
    | first :: rest ->
        if List.exists is_namespace rest then
          Error.error ~code:Error_code.Semantic "ns may only appear once at the start of a file"
        else Ok (first :: rest)

  let split_deftype_methods located_ast =
    let protocol_method_groups methods =
      let add_current groups = function
        | [] -> groups
        | current -> List.rev current :: groups
      in
      let rec loop groups current = function
        | [] -> List.rev (add_current groups current)
        | (Ast.FSymbol _ as protocol) :: rest ->
            loop (add_current groups current) [ protocol ] rest
        | method_form :: rest ->
            loop groups (method_form :: current) rest
      in
      loop [] [] methods
    in
    let all_fields_have_type_hints = function
      | Ast.FVector fields ->
          let rec loop pending_hint = function
            | [] -> not pending_hint
            | Ast.FSymbol metadata :: rest
              when String.starts_with ~prefix:"^" metadata ->
                loop true rest
            | Ast.FSymbol _field_name :: rest ->
                pending_hint && loop false rest
            | _ -> false
          in
          loop false fields
      | _ -> false
    in
    located_ast
    |> List.concat_map (fun located ->
           match located.Ast.form with
           | Ast.FList
               (Ast.FSymbol (("deftype" | "defrecord") as definition)
               :: name :: (Ast.FVector _ as fields) :: (_ :: _ as methods))
             when
               definition = "deftype"
               || all_fields_have_type_hints fields
               || List.exists
                    (function
                      | Ast.FSymbol "ILookup" -> true
                      | _ -> false)
                    methods
             ->
               {
                 located with
                 Ast.form =
                   Ast.FList [ Ast.FSymbol definition; name; fields ];
               }
               :: List.map
                    (fun method_group ->
                      {
                        located with
                        Ast.form =
                          Ast.FList
                            (Ast.FSymbol "deftype-methods" :: name
                           :: method_group);
                      })
                    (protocol_method_groups methods)
           | _ -> [ located ])

  let implementation_uncached ?(target = Target.default) ?reader_features
      ?(filename = "<string>") source =
    let line_starts = line_starts source in
    let is_compile_time_form located =
      match located.Ast.form with
      | Ast.FList
          (Ast.FSymbol ("defmacro" | "macro-helper-defn" | "macro-helper-def")
          :: _) ->
          true
      | _ -> false
    in
    let drop_clojure_compiler_directives located_ast =
      List.filter
        (fun located ->
          match located.Ast.form with
          | Ast.FList
              [
                Ast.FSymbol "set!";
                Ast.FSymbol ("*warn-on-reflection*" | "*unchecked-math*");
                _;
              ] ->
              false
          | _ -> true)
        located_ast
    in
    let same_span left right =
      left.Ast.span.start_offset = right.Ast.span.start_offset
      && left.Ast.span.end_offset = right.Ast.span.end_offset
    in
    let add_clj_compile_time_forms tokens located_ast =
      let uses_cljs_reader =
        Option.fold ~none:false
          ~some:(List.exists (String.equal ":cljs"))
          reader_features
      in
      match (target, uses_cljs_reader) with
      | Target.Native, false -> Ok located_ast
      | (Target.Native, true)
      | (Target.Melange, _)
      | (Target.Js_of_ocaml, _) -> (
          match
            Parser.parse_located ~target:Target.Native
              ~eof_offset:(String.length source) tokens
          with
          | Error _ as error -> error
          | Ok native_original -> (
              match lower_namespace native_original with
              | Error _ as error -> error
              | Ok native_located -> (
                  let compile_time_forms =
                    native_located
                    |> List.map normalize_located_metadata
                    |> extract_compile_time_helpers
                    |> List.filter is_compile_time_form
                  in
                  let located_ast =
                    List.filter
                      (fun located ->
                        not
                          (List.exists
                             (fun compile_time_form ->
                               same_span compile_time_form located)
                             compile_time_forms))
                      located_ast
                  in
                  match located_ast with
                  | ({
                       Ast.form = Ast.FList [ Ast.FSymbol "namespace-scope"; _ ];
                       _;
                     } as namespace_scope)
                    :: rest ->
                      Ok ((namespace_scope :: compile_time_forms) @ rest)
                  | _ -> Ok (compile_time_forms @ located_ast))))
    in
    match Lexer.tokenize source with
    | Error _ as err -> err
    | Ok tokens -> (
        match
          Parser.parse_located ~target ?reader_features
            ~eof_offset:(String.length source) tokens
        with
        | Error error ->
            Error (normalize_error_location filename line_starts error)
        | Ok original_located_ast -> (
            match lower_namespace original_located_ast with
            | Error (error : Error.t) ->
                Error (normalize_error_location filename line_starts error)
            | Ok target_located_ast -> (
                match
                  add_clj_compile_time_forms tokens target_located_ast
                with
                | Error error ->
                    Error (normalize_error_location filename line_starts error)
                | Ok located_ast ->
                let located_ast =
                  located_ast
                  |> List.map normalize_located_metadata
                  |> extract_compile_time_helpers
                  |> drop_clojure_compiler_directives
                  |> split_deftype_methods
                in
                let rec form_locations acc located =
                  let location =
                    location filename line_starts located.Ast.span
                  in
                  List.fold_left form_locations
                    ((located.Ast.form, location) :: acc)
                    located.Ast.children
                in
                let ast =
                  List.map (fun located -> located.Ast.form) located_ast
                in
                let form_locations =
                  List.fold_left form_locations
                    (List.fold_left form_locations [] original_located_ast)
                    located_ast
                in
                let normalized_form_locations =
                  let candidates = Hashtbl.create 128 in
                  List.iter
                    (fun (form, location) ->
                      let locations =
                        Hashtbl.find_opt candidates form
                        |> Option.value ~default:[]
                      in
                      Hashtbl.replace candidates form (location :: locations))
                    form_locations;
                  let compare_location left right =
                    let by_start =
                      Int.compare left.Location.loc_start.Lexing.pos_cnum
                        right.Location.loc_start.Lexing.pos_cnum
                    in
                    if by_start <> 0 then by_start
                    else
                      Int.compare left.Location.loc_end.Lexing.pos_cnum
                        right.Location.loc_end.Lexing.pos_cnum
                  in
                  Hashtbl.filter_map_inplace
                    (fun _ locations ->
                      Some (List.sort_uniq compare_location locations))
                    candidates;
                  let rec bind_form bindings form =
                    let bindings =
                      match Hashtbl.find_opt candidates form with
                      | Some (location :: remaining) ->
                          Hashtbl.replace candidates form remaining;
                          (form, location) :: bindings
                      | Some [] | None -> bindings
                    in
                    match form with
                    | Ast.FList forms | Ast.FVector forms ->
                        List.fold_left bind_form bindings forms
                    | Ast.FMap entries ->
                        List.fold_left
                          (fun bindings (key, value) ->
                            bind_form (bind_form bindings key) value)
                          bindings entries
                    | Ast.FSymbol _ | Ast.FCoreSymbol _ | Ast.FKeyword _
                    | Ast.FString _ | Ast.FRegex _ | Ast.FInt _ | Ast.FFloat _
                    | Ast.FDecimal _ | Ast.FChar _ | Ast.FBool _ ->
                        bindings
                  in
                  List.fold_left bind_form [] ast
                in
                Ok
                  {
                    target;
                    source_unit =
                      "source_" ^ Digest.to_hex (Digest.string source);
                    ast;
                    locations =
                      List.map
                        (fun located ->
                          location filename line_starts located.Ast.span)
                        located_ast;
                    form_locations =
                      normalized_form_locations @ form_locations;
                    filename;
                    parsed_as = `Lg;
                  })))

  let parsed_sources = Hashtbl.create 64

  let implementation ?(target = Target.default) ?reader_features
      ?(filename = "<string>") source =
    if Filename.check_suffix filename ".mli" then
      Ocaml_interface.parse ~filename source
      |> Result.map (fun signature ->
           { target; filename;
             source_unit = "interface_" ^ Digest.to_hex (Digest.string source);
             ast = []; locations = []; form_locations = [];
             parsed_as = `Mli signature })
    else
    let reader_features_key =
      Option.value reader_features ~default:(Target.reader_features target)
      |> String.concat ","
    in
    let key =
      String.concat "\000"
        [
          Target.to_string target;
          reader_features_key;
          filename;
          Digest.to_hex (Digest.string source);
        ]
    in
    match Hashtbl.find_opt parsed_sources key with
    | Some parsed -> Ok parsed
    | None -> (
        match
          implementation_uncached ~target ?reader_features ~filename source
        with
        | Error _ as error -> error
        | Ok parsed as result ->
            Hashtbl.add parsed_sources key parsed;
            result)
end

module Ocaml_parsetree_backend = struct
  let implementation ?(previous_items = []) ?(previous_set_modules = [])
      (typed : typed_result) =
    match
      let items = List.combine typed.locations typed.items in
      let previous_set_modules =
        List.sort_uniq String.compare
          (previous_set_modules
          @ Lowering.requested_set_modules_from_located_items previous_items)
      in
      if previous_set_modules = [] then Lowering.structure_of_located_items items
      else
        Lowering.structure_of_incremental_located_items_with_modules
          ~previous_set_modules items
    with
    | Error _ as err -> err
    | Ok structure -> Ok { ast = typed.ast; items = typed.items; structure }

  let print = Lowering.print_implementation
end

module Ocaml_typechecker = struct
  type analysis = {
    typed_structure : Typedtree.structure;
    compiler_env : Env.t;
    diagnostics : diagnostic list;
  }

  let exception_message exn =
    Format.asprintf "%a" Location.report_exception exn |> String.trim

  let raw_exception_location exn =
    match Location.error_of_exn exn with
    | Some (`Ok report) -> Some report.Location.main.loc
    | Some `Already_displayed | None -> None

  let origin_of_attribute
      ({ Parsetree.attr_name = { txt; _ }; attr_payload; _ } :
        Parsetree.attribute) =
    if txt <> "lg.origin" then None
    else
      match attr_payload with
      | PStr
          [
            {
              pstr_desc =
                Pstr_eval
                  ( {
                      pexp_desc =
                        Pexp_constant
                          { pconst_desc = Pconst_string (origin, _, _); _ };
                      _;
                    },
                    _ );
              _;
            };
          ] ->
          Source_node_id.origin_of_string origin
      | _ -> None

  let origins_of_attributes attributes =
    attributes
    |> List.filter_map origin_of_attribute

  let related_origins structure error_location =
    let contains (candidate : Location.t) =
      String.equal candidate.loc_start.pos_fname
        error_location.Location.loc_start.pos_fname
      && candidate.loc_start.pos_cnum <= error_location.loc_start.pos_cnum
      && candidate.loc_end.pos_cnum >= error_location.loc_end.pos_cnum
    in
    let best = ref None in
    let consider (expression : Parsetree.expression) =
      if contains expression.pexp_loc then
        let origins = origins_of_attributes expression.pexp_attributes in
        if origins <> [] then
          let width =
            expression.pexp_loc.loc_end.pos_cnum
            - expression.pexp_loc.loc_start.pos_cnum
          in
          match !best with
          | Some (best_width, _) when best_width <= width -> ()
          | Some _ | None -> best := Some (width, origins)
    in
    let base = Ast_iterator.default_iterator in
    let iterator =
      {
        base with
        expr =
          (fun self expression ->
            consider expression;
            base.expr self expression);
      }
    in
    iterator.structure iterator structure;
    match !best with
    | None -> []
    | Some (_, origins) ->
        origins
        |> List.map (fun (origin : Source_node_id.origin) ->
               {
                 Error.location = origin.location;
                 message = origin.message;
               })

  let initial_env () =
    Ocaml_signature.init ();
    Lg_compiler_support.Ocaml_value.init
      ~melange:(Ocaml_signature.is_melange_target ())
      (Ocaml_signature.active_include_dirs ())

  let analyze ?compiler_env structure =
    let diagnostics = ref [] in
    let previous_warning_reporter = !Location.warning_reporter in
    let capture_warning location warning =
      match previous_warning_reporter location warning with
      | None -> None
      | Some report ->
          let message =
            Format.asprintf "%a" Location.print_report report |> String.trim
          in
          diagnostics :=
            { code = "OCAML-WARNING";
              phase = `Ocaml;
              message;
              severity = `Warning;
              location = Some location }
            :: !diagnostics;
          None
    in
    try
      let typed_structure, compiler_env =
        Fun.protect
          ~finally:(fun () ->
            Location.warning_reporter := previous_warning_reporter)
          (fun () ->
            Location.warning_reporter := capture_warning;
            let env = Option.value compiler_env ~default:(initial_env ()) in
            let typed_structure, _signature, _signature_names, _shape, env =
              Typemod.type_structure env structure
            in
            Envaux.reset_cache ();
            let env = env |> Env.keep_only_summary |> Envaux.env_of_only_summary in
            (typed_structure, env))
      in
      Ok { typed_structure; compiler_env; diagnostics = List.rev !diagnostics }
    with exn ->
      let raw_location = raw_exception_location exn in
      let location =
        match raw_location with
        | Some location when not location.Location.loc_ghost -> Some location
        | Some _ | None -> None
      in
      let related =
        Option.fold ~none:[] ~some:(related_origins structure)
          raw_location
      in
      Error.error ?location ~related ~code:Error_code.Ocaml
        ~phase:`Ocaml
        ("OCaml typecheck failed: " ^ exception_message exn)

  let structure structure =
    match analyze structure with
    | Error _ as err -> err
    | Ok analysis -> Ok analysis.diagnostics
end

let empty_state =
  {
    typecheck_state = Typecheck.empty_state;
    located_items = [];
    requested_set_modules = [];
    ocaml_env = None;
    pending_interfaces = [];
  }

let cacheable_state state = { state with ocaml_env = None }

let with_source_scope scope state =
  let typecheck_state = Compiler_state.with_scope scope state.typecheck_state in
  let typecheck_state =
    {
      typecheck_state with
      env = Require.add_source_core_bindings typecheck_state.env scope;
    }
  in
  {
    state with
    typecheck_state;
  }

let source_scope state = state.typecheck_state.scope

let target_include_dirs target include_dirs =
  match target with
  | Target.Native | Target.Js_of_ocaml ->
      List.filter
        (fun directory -> Filename.basename directory <> "melange")
        include_dirs
  | Target.Melange ->
      let melange_parents =
        include_dirs
        |> List.filter (fun directory ->
               Filename.basename directory = "melange")
        |> List.map Filename.dirname
      in
      let include_dirs =
        List.filter
          (fun directory ->
            Filename.basename directory <> "byte"
            && Filename.basename directory <> "native"
            && not (List.mem directory melange_parents))
          include_dirs
      in
      let target_specific, generic =
        List.partition
          (fun directory -> Filename.basename directory = "melange")
          include_dirs
      in
      let compiled_interfaces directory =
        let cache = compiled_interface_cache in
        match Hashtbl.find_opt cache directory with
        | Some interfaces -> interfaces
        | None ->
            let interfaces =
              if Sys.file_exists directory && Sys.is_directory directory then
                Sys.readdir directory |> Array.to_list
                |> List.filter (String.ends_with ~suffix:".cmi")
                |> String_set.of_list
              else String_set.empty
            in
            Hashtbl.replace cache directory interfaces;
            interfaces
      in
      let target_specific, target_interfaces =
        List.fold_left
          (fun (directories, interfaces) directory ->
            let directory_interfaces = compiled_interfaces directory in
            if String_set.disjoint interfaces directory_interfaces then
              ( directories @ [ directory ],
                String_set.union interfaces directory_interfaces )
            else (directories, interfaces))
          ([], String_set.empty) target_specific
      in
      let generic =
        List.filter
          (fun directory ->
            String_set.disjoint target_interfaces
              (compiled_interfaces directory))
          generic
      in
      target_specific @ generic

let restore_ocaml_environment ?(target = Target.default) ~packages state
    sources =
  let report_timings =
    Trace.enabled_any
      [ "compile.timing"; "compile.timing.details"; "compile.timing.debug" ]
  in
  let timed label f =
    let started_at = if report_timings then Unix.gettimeofday () else 0.0 in
    let result = f () in
    if report_timings then
      Printf.eprintf "lg: %s: %.3fs\n%!" label
        (Unix.gettimeofday () -. started_at);
    result
  in
  Ocaml_signature.set_melange_target (target = Target.Melange);
  let packages =
    match target with
    | Target.Melange ->
        "melange" :: "lg.rrbvec" :: "lg.runtime" :: "lg.runtime-melange"
        :: "lg.edn-backend" :: packages
    | Target.Js_of_ocaml -> "re" :: "js_of_ocaml" :: packages
    | Target.Native ->
        "re" :: "lg.rrbvec" :: "lg.runtime" :: "lg.edn-backend.native"
        :: packages
  in
  let packages =
    List.fold_left
      (fun packages package ->
        if List.mem package packages then packages else packages @ [ package ])
      [] packages
  in
  if report_timings then
    Printf.eprintf "lg: restore OCaml packages (%d): %s\n%!"
      (List.length packages)
      (String.concat ", " packages);
  match timed "resolve OCaml package include dirs" (fun () ->
            Ocaml_package.include_dirs packages)
  with
  | Error _ as error -> error
  | Ok include_dirs ->
      let include_dirs = target_include_dirs target include_dirs in
      timed "initialize OCaml signature include dirs" (fun () ->
          Ocaml_signature.add_include_dirs include_dirs);
      let rec restore compiler_env index = function
        | [] -> Ok { state with ocaml_env = compiler_env }
        | source :: rest -> (
            try
              let lexbuf = Lexing.from_string source in
              Location.init lexbuf (Printf.sprintf "<cached:%d>" index);
              let structure = Parse.implementation lexbuf in
              match Ocaml_typechecker.analyze ?compiler_env structure with
              | Error _ as error -> error
              | Ok analysis ->
                  restore (Some analysis.compiler_env) (index + 1) rest
            with exn ->
              Error.error ~code:Error_code.Interop
                ("failed to restore cached OCaml environment: "
               ^ Ocaml_typechecker.exception_message exn))
      in
      timed "retype cached OCaml prefix" (fun () -> restore None 0 sources)

let required_packages_from_ast ~target ast =
  let rec loop packages = function
    | [] -> Ok (List.sort_uniq String.compare packages)
    | Ast.FList [ Ast.FSymbol "ffi"; _; _; _; options ] :: rest ->
        Result.bind (Foreign_binding.options ~target options)
          (function
            | Foreign_binding.Native_symbol _ | Foreign_binding.Release_selection | Foreign_binding.Callback_selection ->
                loop ("lg.ffi" :: "ctypes-foreign" :: packages) rest
            | Foreign_binding.JavaScript_symbol _ | Foreign_binding.Object_selection _
            | Foreign_binding.Ocaml_primitive_selection _ -> loop packages rest)
    | Ast.FList (Ast.FSymbol ("module" | "module-functor") :: _ :: forms) :: rest ->
        Result.bind (loop packages forms) (fun packages -> loop packages rest)
    | Ast.FList (Ast.FSymbol "require" :: entries) :: rest -> (
        match Require.parse_entries entries with
        | Error _ as err -> err
        | Ok specs -> loop (Require.package_names specs @ packages) rest)
    | _ :: rest -> loop packages rest
  in
  loop [] ast

let prepare_packages target ast =
  Ocaml_signature.set_melange_target (target = Target.Melange);
  match required_packages_from_ast ~target ast with
  | Error _ as err -> err
  | Ok packages -> (
      let packages =
        match target with
        | Target.Melange -> "melange" :: packages
        | Target.Js_of_ocaml -> "re" :: "js_of_ocaml" :: packages
        | Target.Native -> "re" :: packages
      in
      match Ocaml_package.include_dirs packages with
      | Error _ as err -> err
      | Ok include_dirs ->
          let include_dirs = target_include_dirs target include_dirs in
          Ocaml_signature.add_include_dirs include_dirs;
          Ok packages)

let checked_parsetree (typed : typed_result) =
  match Ocaml_parsetree_backend.implementation typed with
  | Error _ as err -> err
  | Ok result -> (
      if Trace.enabled "compile.dump" then
        Printf.eprintf "%s\n%!"
          (Ocaml_parsetree.print_implementation result.structure);
      match Ocaml_typechecker.structure result.structure with
      | Error _ as err -> err
      | Ok diagnostics -> Ok (result, diagnostics))

let stabilize_dependencies ?(external_signature_dependencies = [])
    (parsed : parser_result) =
  let order =
    Dependency_graph.stable_order ~external_signature_dependencies parsed.ast
  in
  {
    parsed with
    ast = List.map (List.nth parsed.ast) order;
    locations = List.map (List.nth parsed.locations) order;
  }

let declaration_bindings ast env =
  let module Declared_names = Set.Make (String) in
  let rec declared_names declared = function
    | [] -> List.rev declared
    | Ast.FList (Ast.FSymbol "declare" :: form_names) :: rest ->
        let declared =
          List.fold_left
            (fun declared -> function
              | Ast.FSymbol name -> name :: declared | _ -> declared)
            declared form_names
        in
        declared_names declared rest
    | Ast.FList
        (Ast.FSymbol "declare+" :: Ast.FSymbol name :: _signature)
      :: rest ->
        declared_names (name :: declared) rest
    | Ast.FList
        (Ast.FSymbol "declare+"
        :: Ast.FList
             [ Ast.FSymbol "__type-hint"; _; Ast.FSymbol name ]
        :: _signature)
      :: rest ->
        declared_names (name :: declared) rest
    | Ast.FList
        [
          Ast.FSymbol "defn-signature";
          Ast.FList
            (Ast.FSymbol ("defn" | "defn-") :: Ast.FSymbol name :: _);
        ]
      :: rest ->
        declared_names (name :: declared) rest
    | _ :: rest -> declared_names declared rest
  in
  let recursive_declared_names =
    Dependency_graph.recursive_groups ast
    |> List.concat_map (fun indices ->
           indices
           |> List.concat_map (fun index ->
                List.nth ast index |> Dependency_graph.provided_names))
  in
  let declared =
    declared_names recursive_declared_names ast |> Declared_names.of_list
  in
  let final_name name =
    match String.rindex_opt name '/' with
    | None -> name
    | Some separator ->
        String.sub name (separator + 1) (String.length name - separator - 1)
  in
  let key_has_suffix key suffix =
    String.equal key suffix
    ||
    let key_length = String.length key in
    let suffix_length = String.length suffix in
    key_length > suffix_length
    && Char.equal key.[key_length - suffix_length - 1] '/'
    && String.ends_with ~suffix key
  in
  Declared_names.to_seq declared
  |> Seq.flat_map (fun name ->
         Compiler_environment.binding_entries_named (final_name name) env
         |> List.to_seq
         |> Seq.filter (fun (key, _) -> key_has_suffix key name))
  |> List.of_seq
  |> List.map (fun (key, (binding : Types.binding)) ->
         if binding.forward_declared then (key, binding)
         else (key, { binding with forward_declared = true }))
  |> fun bindings ->
  let declared_name name =
    Declared_names.mem name declared
    || Declared_names.mem (final_name name) declared
  in
  let compiler_binding_named name =
    Compiler_environment.binding_entries_named (final_name name) env
    |> List.find_map (fun (_key, binding) -> Some binding)
  in
  let param_types params parameter_tys =
    match Destructure.parse_param_specs params with
    | Error _ -> None
    | Ok specs when List.length specs = List.length parameter_tys ->
        Some
          (List.map2
             (fun (spec : Destructure.param_spec) ty -> (spec.source_name, ty))
             specs parameter_tys)
    | Ok _ -> None
  in
  let forwarded_signature = function
    | Ast.FList
        (Ast.FSymbol ("defn" | "defn-") :: Ast.FSymbol name
        :: (Ast.FVector _ as params) :: body_forms) -> (
        match (compiler_binding_named name, List.rev body_forms) with
        | Some { ty = Types.TFn (parameter_tys, return_ty); _ },
          Ast.FList (Ast.FSymbol callee :: arguments) :: _
          when declared_name callee -> (
            match param_types params parameter_tys with
            | Some local_params
              when List.length arguments = List.length local_params ->
                let argument_tys =
                  arguments
                  |> List.map (function
                       | Ast.FSymbol argument_name ->
                           List.assoc_opt argument_name local_params
                       | _ -> None)
                in
                if List.for_all Option.is_some argument_tys then
                  Some
                    ( callee,
                      Types.TFn
                        (List.filter_map Fun.id argument_tys, return_ty) )
                else None
            | Some _ | None -> None)
        | _ -> None)
    | _ -> None
  in
  let refine_binding bindings (name, forwarded_ty) =
    match
      bindings
      |> List.find_opt (fun (key, _) -> key_has_suffix key name)
    with
    | None -> bindings
    | Some (target_key, (binding : Types.binding)) -> (
        match Type_solver.unify Type_solver.empty binding.ty forwarded_ty with
        | Error _ -> bindings
        | Ok substitutions ->
            let refined_ty = Type_solver.apply substitutions forwarded_ty in
            List.map
              (fun (candidate, (candidate_binding : Types.binding)) ->
                if String.equal candidate target_key then
                  ( candidate,
                    {
                      candidate_binding with
                      ty = refined_ty;
                      scheme = None;
                      forward_declared = true;
                    } )
                else (candidate, candidate_binding))
              bindings)
  in
  ast
  |> List.filter_map forwarded_signature
  |> List.fold_left refine_binding bindings
  |> List.sort_uniq (fun (left, _) (right, _) -> String.compare left right)

let stabilization_ast ?(signed_names = []) ast =
  let module Signed_names = Set.Make (String) in
  let module Required_names = Set.Make (String) in
  let signed_names = Signed_names.of_list signed_names in
  let scope =
    ast
    |> List.find_map (function
         | Ast.FList
             [ Ast.FSymbol "namespace-scope"; Ast.FSymbol namespace ] ->
             Some namespace
         | _ -> None)
    |> Option.value ~default:""
  in
  let explicitly_signed_definition = function
    | Ast.FList
        (Ast.FSymbol ("def" | "defonce" | "defn" | "defn-")
        :: Ast.FSymbol name :: _) ->
        Signed_names.mem name signed_names
        || (scope <> ""
           && Signed_names.mem (Names.scoped_key scope name) signed_names)
    | _ -> false
  in
  let ordinary_definition = function
    | Ast.FList
        (Ast.FSymbol ("def" | "defonce" | "defn" | "defn-")
        :: Ast.FSymbol _ :: _) ->
        true
    | _ -> false
  in
  let add_name_variants names name =
    let names = Required_names.add name names in
    match String.rindex_opt name '/' with
    | None -> names
    | Some separator ->
        Required_names.add
          (String.sub name (separator + 1)
             (String.length name - separator - 1))
          names
  in
  let intersects names candidates =
    List.exists
      (fun candidate ->
        let variants = add_name_variants Required_names.empty candidate in
        not
          (Required_names.is_empty (Required_names.inter names variants)))
      candidates
  in
  let recursive_groups = Dependency_graph.recursive_groups ast in
  let recursive_indices = List.concat recursive_groups in
  let recursive_group_by_index = Array.make (List.length ast) None in
  List.iter
    (fun group ->
      List.iter
        (fun index -> recursive_group_by_index.(index) <- Some group)
        group)
    recursive_groups;
  let declared_names =
    let explicit =
      ast
      |> List.concat_map (function
           | Ast.FList (Ast.FSymbol ("declare" | "declare+") :: _)
           | Ast.FList [ Ast.FSymbol "defn-signature"; _ ] as form ->
               Dependency_graph.provided_names form
           | _ -> [])
    in
    let recursive =
      recursive_indices
      |> List.concat_map (fun index ->
             Dependency_graph.provided_names (List.nth ast index))
    in
    List.sort_uniq String.compare (explicit @ recursive)
  in
  if declared_names = [] then ast
  else
    let indexed = List.mapi (fun index form -> (index, form)) ast in
    let selected = Array.make (List.length ast) false in
    let rec close required_names =
      let required_names, changed =
        List.fold_left
          (fun (required_names, changed) (index, form) ->
            let provided = Dependency_graph.provided_names form in
            if
              ordinary_definition form
              && not selected.(index)
              && intersects required_names provided
            then
              let () = selected.(index) <- true in
              let required_names =
                if
                  explicitly_signed_definition form
                  || Option.is_some recursive_group_by_index.(index)
                then required_names
                else
                  List.fold_left add_name_variants required_names
                    (Dependency_graph.dependency_symbols form)
              in
              (required_names, true)
            else (required_names, changed))
          (required_names, false) indexed
      in
      if changed then close required_names else ()
    in
    let required_names =
      List.fold_left add_name_variants Required_names.empty declared_names
    in
    close required_names;
    List.mapi
      (fun index form ->
        match recursive_group_by_index.(index) with
        | Some (first :: _ as indices) when index = first ->
            let names =
              indices
              |> List.concat_map (fun member ->
                     List.nth ast member |> Dependency_graph.provided_names)
              |> List.sort_uniq String.compare
              |> List.map (fun name -> Ast.FSymbol name)
            in
            Ast.FList (Ast.FSymbol "declare" :: names)
        | Some (_ :: _) -> Ast.FList [ Ast.FSymbol "declare" ]
        | Some [] -> form
        | None when ordinary_definition form ->
            if not selected.(index) then
              Ast.FList [ Ast.FSymbol "declare" ]
            else if explicitly_signed_definition form then
              match Dependency_graph.provided_names form with
              | name :: _ ->
                  Ast.FList [ Ast.FSymbol "declare"; Ast.FSymbol name ]
              | [] -> form
            else form
        | None -> form)
      ast

let recursive_definition_ast ast =
  let definition_forms = function
    | Ast.FList
        (Ast.FSymbol ("defn" | "defn-") :: Ast.FSymbol _
        :: Ast.FString _docstring :: forms) ->
        Some forms
    | Ast.FList
        (Ast.FSymbol ("defn" | "defn-") :: Ast.FSymbol _ :: forms) ->
        Some forms
    | _ -> None
  in
  let plain_definition form =
    match definition_forms form with
    | Some (Ast.FVector _ :: _) -> true
    | Some (Ast.FList (Ast.FVector _ :: _) :: clauses) ->
        List.for_all
          (function Ast.FList (Ast.FVector _ :: _) -> true | _ -> false)
          clauses
    | Some _ | None -> false
  in
  let multi_arity_definition = function
    | form -> (
        match definition_forms form with
        | Some (Ast.FList (Ast.FVector _ :: _) :: _) -> true
        | Some _ | None -> false)
  in
  let recursive_groups =
    Dependency_graph.recursive_groups ast
    |> List.filter_map (fun indices ->
           if
             List.length indices >= 2
             && List.for_all
                  (fun index -> plain_definition (List.nth ast index))
                  indices
           then
             Some
               (List.stable_sort
                  (fun left right ->
                    Bool.compare
                      (multi_arity_definition (List.nth ast left))
                      (multi_arity_definition (List.nth ast right)))
                  indices)
           else None)
  in
  let normalize_definition = function
    | Ast.FList
        (Ast.FSymbol (("defn" | "defn-") as definition)
        :: (Ast.FSymbol _ as name) :: Ast.FString _docstring :: forms) ->
        Ast.FList (Ast.FSymbol definition :: name :: forms)
    | form -> form
  in
  List.mapi
    (fun index form ->
      match List.find_opt (List.exists (( = ) index)) recursive_groups with
      | None -> form
      | Some (first :: _ as indices) when index = first ->
          Ast.FList
            (Ast.FSymbol "recursive-definition-group"
            :: List.map
                 (fun member -> normalize_definition (List.nth ast member))
                 indices)
      | Some (_ :: _) -> Ast.FList [ Ast.FSymbol "declare" ]
      | Some [] -> form)
    ast

let affected_stabilization_forms ast evidence_ast changed_names =
  let module Names = Set.Make (String) in
  let add_name_variants names name =
    let names = Names.add name names in
    match String.rindex_opt name '/' with
    | None -> names
    | Some separator ->
        Names.add
          (String.sub name (separator + 1)
             (String.length name - separator - 1))
          names
  in
  let intersects names candidates =
    List.exists
      (fun candidate ->
        not (Names.is_empty (Names.inter names (add_name_variants Names.empty candidate))))
      candidates
  in
  let affected_names =
    List.fold_left add_name_variants Names.empty changed_names
  in
  let indexed =
    List.map2
      (fun original evidence ->
        ( original,
          evidence,
          List.sort_uniq String.compare
            (Dependency_graph.provided_names original
            @ Dependency_graph.provided_names evidence),
          List.sort_uniq String.compare
            (Dependency_graph.dependency_symbols original
            @ Dependency_graph.dependency_symbols evidence) ))
      ast evidence_ast
  in
  let can_recompile = function
    | Ast.FList
        (Ast.FSymbol
          ( "def" | "defonce" | "defn" | "defn-" | "defmacro"
          | "recursive-definition-group" )
        :: _) ->
        true
    | _ -> false
  in
  indexed
  |> List.filter_map (fun (original, evidence, provided, dependencies) ->
         if
           provided <> [] && can_recompile original
           && (intersects affected_names provided
              || intersects affected_names dependencies)
         then Some evidence
         else None)

let stabilize_typecheck ?compile_evidence ?compile_evidence_subset ~compile
    ~(initial_state : Compiler_state.t) ast =
  let report_timings = Trace.enabled "compile.timing" in
  let report_timing_details = Trace.enabled "compile.timing.details" in
  let module Signed_names = Set.Make (String) in
  let scope =
    ast
    |> List.find_map (function
         | Ast.FList
             [ Ast.FSymbol "namespace-scope"; Ast.FSymbol namespace ] ->
             Some namespace
         | _ -> None)
    |> Option.value ~default:""
  in
  let inline_signed_names =
    List.fold_left
      (fun names -> function
        | Ast.FList (Ast.FSymbol "signature" :: Ast.FSymbol name :: _) ->
            Signed_names.add
              (if String.contains name '/' then name
               else Names.scoped_key scope name)
              names
        | _ -> names)
      Signed_names.empty ast
  in
  let qualify_name name =
    if String.contains name '/' then name else Names.scoped_key scope name
  in
  let explicit_declarations =
    ast
    |> List.concat_map (function
         | Ast.FList (Ast.FSymbol "declare" :: names) ->
             List.filter_map
               (function Ast.FSymbol name -> Some (qualify_name name) | _ -> None)
               names
         | _ -> [])
  in
  let recursive_declarations =
    Dependency_graph.recursive_groups ast
    |> List.concat_map (fun indices ->
         indices
         |> List.concat_map (fun index ->
              List.nth ast index |> Dependency_graph.provided_names)
         |> List.map qualify_name)
  in
  let inferred_declarations =
    List.sort_uniq String.compare
      (explicit_declarations @ recursive_declarations)
  in
  let declaration_is_signed name =
    Signed_names.mem name inline_signed_names
    || Option.is_some
         (Signature_overlay.find_value name
            (Compiler_environment.signatures initial_state.env))
  in
  let declarations_are_fully_signed =
    inferred_declarations <> []
    && List.for_all declaration_is_signed inferred_declarations
  in
  let compile_pass compiler pass state =
    let started_at = if report_timings then Sys.time () else 0.0 in
    let result = compiler state in
    if report_timings then
      Printf.eprintf "lg: typecheck stabilization pass %d: %.3fs\n%!" pass
        (Sys.time () -. started_at);
    result
  in
  let binding_abi_equal (left : Types.binding) (right : Types.binding) =
    (match (left.scheme, right.scheme) with
    | Some left, Some right when left == right -> true
    | Some left, Some right ->
        Types.source_name (Type_solver.canonical_scheme_body left)
        = Types.source_name (Type_solver.canonical_scheme_body right)
    | None, None when left.ty == right.ty -> true
    | None, None ->
        Types.source_name (Type_solver.canonical left.ty)
        = Types.source_name (Type_solver.canonical right.ty)
    | Some _, None | None, Some _ -> false)
    && left.row_param_types = right.row_param_types
    && left.overload_row_param_types = right.overload_row_param_types
    && left.overload_targets = right.overload_targets
    && left.return_param_index = right.return_param_index
    && left.dynamically_bindable = right.dynamically_bindable
    && left.redef_root_name = right.redef_root_name
  in
  let binding_abi_equal_for name (left : Types.binding)
      (right : Types.binding) =
    if
      Signed_names.mem name inline_signed_names
      || Option.is_some
           (Signature_overlay.find_value name
              (Compiler_environment.signatures initial_state.env))
    then
        String.equal (Types.source_name left.ty) (Types.source_name right.ty)
    else binding_abi_equal left right
  in
  let declarations_abi_equal left right =
    List.length left = List.length right
    &&
    List.for_all2
      (fun (left_name, left_binding) (right_name, right_binding) ->
        left_name = right_name
        && binding_abi_equal_for left_name left_binding right_binding)
      left right
  in
  let changed_declaration_names previous next =
    next
    |> List.filter_map (fun (name, binding) ->
           match List.assoc_opt name previous with
           | Some previous_binding
             when binding_abi_equal_for name previous_binding binding ->
               None
           | Some _ | None -> Some name)
  in
  let report_changed_declarations previous next =
    if report_timings || report_timing_details then
      let previous_by_name name =
        List.find_opt (fun (candidate, _) -> String.equal name candidate) previous
        |> Option.map snd
      in
      next
      |> List.filter_map (fun (name, binding) ->
             match previous_by_name name with
             | Some previous_binding
               when binding_abi_equal_for name previous_binding binding ->
                 None
             | None -> Some name
             | Some previous_binding ->
                 let changes =
                   []
                   |> (fun changes ->
                        if
                          String.equal (Types.source_name previous_binding.ty)
                            (Types.source_name binding.ty)
                        then changes
                        else "type" :: changes)
                   |> (fun changes ->
                        if previous_binding.row_param_types = binding.row_param_types
                        then changes
                        else "rows" :: changes)
                   |> (fun changes ->
                        if
                          previous_binding.overload_row_param_types
                          = binding.overload_row_param_types
                        then changes
                        else "overload-rows" :: changes)
                   |> (fun changes ->
                        if previous_binding.overload_targets = binding.overload_targets
                        then changes
                        else "overloads" :: changes)
                   |> (fun changes ->
                        if
                          previous_binding.return_param_index
                          = binding.return_param_index
                        then changes
                        else "return-param" :: changes)
                 in
                 let label =
                   name ^ "[" ^ String.concat "," (List.rev changes) ^ "]"
                 in
                 if report_timing_details then
                   let previous_ty = Types.source_name previous_binding.ty in
                   let next_ty = Types.source_name binding.ty in
                   Some (label ^ " " ^ previous_ty ^ " => " ^ next_ty)
                 else Some label)
      |> function
      | [] -> ()
      | names ->
          Printf.eprintf "lg: changed declaration ABI: %s\n%!"
            (String.concat ", " names)
  in
  let evidence_compile = Option.value compile_evidence ~default:compile in
  let initial_compile state =
    match compile_evidence with
    | None -> compile state
    | Some compile_evidence -> (
        match compile_evidence state with
        | Ok _ as result -> result
        | Error _ -> compile state)
  in
  let seeded_state declarations protocol_evidence =
    {
      initial_state with
      env =
        initial_state.env
        |> Compiler_environment.add_bindings declarations
        |> Compiler_environment.with_protocol_evidence
             (Some protocol_evidence);
    }
  in
  let rec continue_full remaining pass declarations protocol_evidence =
    if remaining = 0 then
      Error.error ~code:Error_code.Semantic "type evidence did not stabilize after 16 passes"
    else
      match
        compile_pass compile pass
          (seeded_state declarations protocol_evidence)
      with
      | Error _ as error -> error
      | Ok ((next_state : Compiler_state.t), items) ->
          let next_declarations = declaration_bindings ast next_state.env in
          let next_protocols =
            Compiler_environment.protocols next_state.env
          in
          if declarations_abi_equal next_declarations declarations then
            Ok (next_state, items)
          else (
            report_changed_declarations declarations next_declarations;
            continue_full (remaining - 1) (pass + 1) next_declarations
              next_protocols
          )
  and finish remaining pass declarations protocol_evidence evidence_result =
    match compile_evidence with
    | None -> Ok evidence_result
    | Some _ ->
        if remaining = 0 then
          Error.error ~code:Error_code.Semantic "type evidence did not stabilize after 16 passes"
        else
          match
            compile_pass compile pass
              (seeded_state declarations protocol_evidence)
          with
          | Error _ as error -> error
          | Ok ((next_state : Compiler_state.t), items) ->
              let next_declarations =
                declaration_bindings ast next_state.env
              in
              let next_protocols =
                Compiler_environment.protocols next_state.env
              in
              if declarations_abi_equal next_declarations declarations then
                Ok (next_state, items)
              else (
                report_changed_declarations declarations next_declarations;
                continue_full (remaining - 1) (pass + 1)
                  next_declarations next_protocols
              )
  in
  let rec continue remaining pass declarations protocol_evidence
      (evidence_base : Compiler_state.t) changed_names =
    if remaining = 0 then
      Error.error ~code:Error_code.Semantic "type evidence did not stabilize after 16 passes"
    else
      let full_state = seeded_state declarations protocol_evidence in
      let subset_state =
        {
          evidence_base with
          items = initial_state.items;
          env =
            evidence_base.env
            |> Compiler_environment.add_bindings declarations
            |> Compiler_environment.with_protocol_evidence
                 (Some protocol_evidence);
        }
      in
      let compiler _state =
        match compile_evidence_subset with
        | None -> evidence_compile full_state
        | Some compile_subset -> (
            match compile_subset changed_names subset_state with
            | Ok _ as result -> result
            | Error error ->
                if report_timings then
                  Printf.eprintf "lg: stabilization subset fallback: %s\n%!"
                    error.Error.message;
                evidence_compile full_state)
      in
      match
        compile_pass compiler pass full_state
      with
      | Error _ as error -> error
      | Ok ((next_state : Compiler_state.t), items) ->
          let next_declarations = declaration_bindings ast next_state.env in
          let next_protocols =
            Compiler_environment.protocols next_state.env
          in
          if declarations_abi_equal next_declarations declarations then
            finish (remaining - 1) (pass + 1) next_declarations
              next_protocols (next_state, items)
          else (
            report_changed_declarations declarations next_declarations;
            let changed_names =
              changed_declaration_names declarations next_declarations
            in
            continue (remaining - 1) (pass + 1) next_declarations
              next_protocols evidence_base changed_names
          )
  in
  if declarations_are_fully_signed then compile_pass compile 1 initial_state
  else
  match compile_pass initial_compile 1 initial_state with
  | Error _ as error -> error
  | Ok (((first_state : Compiler_state.t), _) as first_result) ->
      let initial_declarations =
        declaration_bindings ast initial_state.env
      in
      let first_declarations = declaration_bindings ast first_state.env in
      let first_protocols = Compiler_environment.protocols first_state.env in
      if declarations_abi_equal first_declarations initial_declarations then
        finish 15 2 first_declarations first_protocols first_result
      else (
        report_changed_declarations initial_declarations first_declarations;
        continue 15 2 first_declarations first_protocols first_state
          (changed_declaration_names initial_declarations first_declarations))

let typecheck (parsed : parser_result) =
  let parsed = stabilize_dependencies parsed in
  match prepare_packages parsed.target parsed.ast with
  | Error _ as err -> err
  | Ok _ -> (
      let initial_state =
        Compiler_state.with_target parsed.target Typecheck.empty_state
      in
      let compilation_ast = recursive_definition_ast parsed.ast in
      let compile state =
        Source_context.with_source_unit parsed.source_unit (fun () ->
            Source_context.with_locations parsed.form_locations (fun () ->
                Typecheck.compile_forms_incremental state compilation_ast))
      in
      let signed_names =
        initial_state.env |> Compiler_environment.signatures
        |> Signature_overlay.value_names
      in
      let evidence_ast = stabilization_ast ~signed_names parsed.ast in
      if Trace.enabled "compile.timing.debug" then begin
        let evidence_names =
          evidence_ast
          |> List.filter_map (fun form ->
                 match Dependency_graph.provided_names form with
                 | [] -> None
                 | names -> Some (String.concat "/" names))
        in
        Printf.eprintf "lg: stabilization evidence forms: %s\n%!"
          (String.concat ", " evidence_names)
      end;
      let compile_evidence =
        if List.for_all2 ( == ) evidence_ast parsed.ast then None
        else
          Some
            (fun state ->
              Source_context.with_source_unit parsed.source_unit (fun () ->
                  Source_context.with_locations parsed.form_locations (fun () ->
                  Typecheck.compile_forms_incremental state evidence_ast)))
      in
      let compile_evidence_subset =
        Option.map
          (fun _ changed_names state ->
            let forms =
              affected_stabilization_forms parsed.ast evidence_ast
                changed_names
            in
            if Trace.enabled "compile.timing" then
              Printf.eprintf "lg: stabilization subset: %d forms\n%!"
                (List.length forms);
            Source_context.with_source_unit parsed.source_unit (fun () ->
                Source_context.with_locations parsed.form_locations (fun () ->
                    Typecheck.compile_forms_incremental state forms)))
          compile_evidence
      in
      match
        stabilize_typecheck ?compile_evidence ?compile_evidence_subset ~compile
          ~initial_state parsed.ast
      with
      | Error _ as err -> err
      | Ok (typecheck_state, items) ->
          Ok
            {
              ast = parsed.ast;
              items;
              locations = parsed.locations;
              typecheck_state;
            } )

let typecheck_lg_incremental state (parsed : parser_result) =
  let external_signature_dependencies =
    state.typecheck_state.env |> Compiler_environment.signatures
    |> Signature_overlay.value_type_dependencies
  in
  let parsed =
    stabilize_dependencies ~external_signature_dependencies parsed
  in
  match prepare_packages parsed.target parsed.ast with
  | Error _ as err -> err
  | Ok _ -> (
      let initial_state =
        if state.located_items = [] then
          Compiler_state.with_target parsed.target state.typecheck_state
        else state.typecheck_state
      in
      let initial_state =
        {
          initial_state with
          env =
            Compiler_environment.with_protocol_evidence None initial_state.env;
        }
      in
      let compilation_ast = recursive_definition_ast parsed.ast in
      let compile typecheck_state =
        Source_context.with_source_unit parsed.source_unit (fun () ->
            Source_context.with_locations parsed.form_locations (fun () ->
                Typecheck.compile_forms_incremental typecheck_state
                  compilation_ast))
      in
      let signed_names =
        initial_state.env |> Compiler_environment.signatures
        |> Signature_overlay.value_names
      in
      let evidence_ast = stabilization_ast ~signed_names parsed.ast in
      if Trace.enabled "compile.timing.debug" then begin
        let evidence_names =
          evidence_ast
          |> List.filter_map (fun form ->
                 match Dependency_graph.provided_names form with
                 | [] -> None
                 | names -> Some (String.concat "/" names))
        in
        Printf.eprintf "lg: stabilization evidence forms: %s\n%!"
          (String.concat ", " evidence_names)
      end;
      let compile_evidence =
        if List.for_all2 ( == ) evidence_ast parsed.ast then None
        else
          Some
            (fun typecheck_state ->
              Source_context.with_source_unit parsed.source_unit (fun () ->
                  Source_context.with_locations parsed.form_locations (fun () ->
                      Typecheck.compile_forms_incremental typecheck_state
                        evidence_ast)))
      in
      let compile_evidence_subset =
        Option.map
          (fun _ changed_names typecheck_state ->
            let forms =
              affected_stabilization_forms parsed.ast evidence_ast
                changed_names
            in
            if Trace.enabled "compile.timing" then
              Printf.eprintf "lg: stabilization subset: %d forms\n%!"
                (List.length forms);
            Source_context.with_source_unit parsed.source_unit (fun () ->
                Source_context.with_locations parsed.form_locations (fun () ->
                    Typecheck.compile_forms_incremental typecheck_state forms)))
          compile_evidence
      in
      match
        stabilize_typecheck ?compile_evidence ?compile_evidence_subset ~compile
          ~initial_state parsed.ast
      with
      | Error _ as err -> err
      | Ok (typecheck_state, items) ->
          let located_items =
            state.located_items @ List.combine parsed.locations items
          in
          let state =
            { state with typecheck_state; located_items }
          in
          Ok
            ( state,
              {
                ast = parsed.ast;
                items;
                locations = parsed.locations;
                typecheck_state;
              } ))

let interface_definition_forms state forms =
  let rec collect (state : Typecheck.state) collected = function
    | [] -> Ok (List.rev collected)
    | (Ast.FList (Ast.FSymbol "do" :: forms)) :: rest ->
        collect state collected (forms @ rest)
    | (Ast.FList (Ast.FSymbol
        ("namespace-scope" | "require" | "refer-clojure" | "defmacro"
         | "macro-helper-defn" | "macro-helper-def") :: _) as form) :: rest ->
        Result.bind (Typecheck.compile_forms_incremental state [form])
          (fun (state, _) -> collect state (form :: collected) rest)
    | (Ast.FList (Ast.FSymbol name :: arguments) as form) :: rest ->
        (match Compiler_environment.find_macro ~scope:state.scope name state.env with
        | Some definition ->
            Result.bind (Macro_expander.expand ~call_site:form ~scope:state.scope
              ~compiler_env:state.env definition arguments)
              (fun expanded -> collect state collected (expanded :: rest))
        | None -> collect state (form :: collected) rest)
    | form :: rest -> collect state (form :: collected) rest
  in
  collect state [] forms

let typecheck_incremental state (parsed : parser_result) =
  let stem = Ocaml_interface.source_stem parsed.filename in
  match parsed.parsed_as with
  | `Mli signature ->
      if List.mem_assoc stem state.pending_interfaces then
        Error.error ~code:Error_code.Duplicate ("Duplicate OCaml interface for " ^ stem)
      else
        let state = { state with pending_interfaces =
          (stem, signature) :: state.pending_interfaces } in
        Ok (state, { ast = []; items = []; locations = [];
                     typecheck_state = state.typecheck_state })
  | `Lg ->
      if Filename.check_suffix parsed.filename ".lgi" then
        typecheck_lg_incremental state parsed
      else match List.assoc_opt stem state.pending_interfaces with
      | None -> typecheck_lg_incremental state parsed
      | Some signature ->
          let scope = List.find_map (function
            | Ast.FList [Ast.FSymbol "namespace-scope"; Ast.FSymbol scope] -> Some scope
            | _ -> None) parsed.ast
            |> Option.value ~default:state.typecheck_state.scope in
          Result.bind (interface_definition_forms state.typecheck_state parsed.ast)
            (fun definitions ->
          Result.bind (Ocaml_interface.translate ~filename:parsed.filename ~scope
              ~env:state.typecheck_state.env definitions signature)
            (fun (declarations, form_locations, type_module) ->
              let ast, locations = List.split declarations in
              let interface = { parsed with ast; locations; form_locations } in
              let state = { state with pending_interfaces =
                List.remove_assoc stem state.pending_interfaces } in
              Result.bind (typecheck_lg_incremental state interface)
                (fun (state, interface_typed) ->
                  let state = match type_module with
                    | None -> state
                    | Some module_name ->
                        let env = Module_environment.open_bindings ~qualified:true scope
                          state.typecheck_state.env module_name in
                        { state with typecheck_state = { state.typecheck_state with env } }
                  in
                  Result.map (fun (state, (typed : typed_result)) ->
                    (state, { typed with
                      ast = interface_typed.ast @ typed.ast;
                      items = interface_typed.items @ typed.items;
                      locations = interface_typed.locations @ typed.locations }))
                    (typecheck_lg_incremental state parsed))))

let prepare_source ?(target = Target.default) ?reader_target
    ?(filename = "<string>") source =
  let reader_features =
    Option.map
      (fun reader_target ->
        [ Target.feature target; Target.reader_dialect_feature reader_target ])
      reader_target
  in
  match
    Lg_frontend.implementation ~target ?reader_features ~filename source
  with
  | Error _ as err -> err
  | Ok parsed ->
      required_packages_from_ast ~target parsed.ast
      |> Result.map (fun required_packages -> { parsed; required_packages })

let required_ocaml_packages ?(target = Target.default) ?(filename = "<string>")
    source =
  prepare_source ~target ~filename source
  |> Result.map (fun prepared -> prepared.required_packages)

let prepared_source_required_packages prepared = prepared.required_packages

let analyze ?(target = Target.default) ?(filename = "<string>") source =
  Info_tree.reset ();
  match Lg_frontend.implementation ~target ~filename source with
  | Error _ as err -> err
  | Ok parsed -> (
      match typecheck parsed with
      | Error _ as err -> err
      | Ok typed -> (
          match Ocaml_parsetree_backend.implementation typed with
          | Error _ as err -> err
          | Ok parsetree -> (
              if Trace.enabled "compile.dump" then
                Printf.eprintf "%s\n%!"
                  (Ocaml_parsetree.print_implementation parsetree.structure);
              let structure =
                Lg_compiler_support.Ocaml_module.mark_private_values
                  ~is_private:(Compiler_environment.export_is_private typed.typecheck_state.env)
                  parsetree.structure
              in
              match Ocaml_typechecker.analyze structure with
              | Error _ as err -> err
              | Ok analysis ->
                  Ok
                    {
                      typed_structure = analysis.typed_structure;
                      compiler_env = analysis.compiler_env;
                      typecheck_state = typed.typecheck_state;
                      diagnostics = analysis.diagnostics;
                      info_tree = Info_tree.snapshot ();
                    })))

let interface_of_analysis (analysis : language_analysis) =
  Printtyp.wrap_printing_env ~error:false analysis.compiler_env (fun () ->
      Format.asprintf "%a@." Printtyp.signature
        (Lg_compiler_support.Ocaml_module.public_signature
           ~compiler_env:analysis.compiler_env
           ~is_private:(fun name ->
             Compiler_environment.export_is_private analysis.typecheck_state.env name)
           analysis.typed_structure.str_type))

let interface ?(target = Target.default) ?(filename = "<string>") source =
  analyze ~target ~filename source |> Result.map interface_of_analysis

let order_workspace_from_state ?(target = Target.default) ?reader_target
    initial_state sources =
  let reader_features =
    Option.map
      (fun reader_target ->
        [ Target.feature target; Target.reader_dialect_feature reader_target ])
      reader_target
  in
  let rec parse parsed = function
    | [] -> Ok (List.rev parsed)
    | (filename, source) :: rest -> (
        match
          Lg_frontend.implementation ~target ?reader_features ~filename source
        with
        | Error _ as error -> error
        | Ok result -> parse ((filename, result) :: parsed) rest)
  in
  let source_stem = Ocaml_interface.source_stem in
  let rec group_sources = function
    | [] -> []
    | ((filename, _) as source) :: rest ->
        let stem = source_stem filename in
        let matching, remaining =
          List.partition
            (fun (candidate, _) -> source_stem candidate = stem)
            rest
        in
        let group =
          source :: matching
          |> List.stable_sort (fun (left, _) (right, _) ->
                 Bool.compare
                   (not (Ocaml_interface.is_interface left))
                   (not (Ocaml_interface.is_interface right)))
        in
        group :: group_sources remaining
  in
  let rec typecheck_group state = function
    | [] -> Ok state
    | (_filename, parsed) :: rest ->
        Result.bind (typecheck_incremental state parsed) (fun (state, _typed) ->
            typecheck_group state rest)
  in
  let rec order state ordered pending =
    match pending with
    | [] -> Ok (List.rev ordered)
    | _ ->
        let rec try_pending deferred first_error = function
          | [] -> (
              match first_error with
              | Some error -> Error error
              | None -> Error.error ~code:Error_code.Semantic "unable to order workspace sources")
          | group :: rest -> (
              match typecheck_group state group with
              | Error error ->
                  try_pending
                    (group :: deferred)
                    (match first_error with
                    | Some _ -> first_error
                    | None -> Some error)
                    rest
              | Ok next_state ->
                  let filenames = List.map fst group in
                  order next_state (List.rev_append filenames ordered)
                    (List.rev_append deferred rest))
        in
        try_pending [] None pending
  in
  Result.bind (parse [] sources) (fun sources ->
      order initial_state [] (group_sources sources))

let analyze_workspace_with_errors_from_state ?(target = Target.default)
    ?(check_incremental_ocaml = true) initial_state sources =
  Info_tree.reset ();
  let sources = List.stable_sort (fun (left, _) (right, _) ->
      Bool.compare (not (Ocaml_interface.is_interface left))
        (not (Ocaml_interface.is_interface right))) sources in
  let validate_ocaml state =
    match Lowering.structure_of_located_items state.located_items with
    | Error _ as err -> err
    | Ok structure ->
        Ocaml_typechecker.analyze ?compiler_env:initial_state.ocaml_env structure
        |> Result.map ignore
  in
  let rec parse parsed errors = function
    | [] -> Ok (List.rev parsed, List.rev errors)
    | (filename, source) :: rest -> (
        match Lg_frontend.implementation ~target ~filename source with
        | Error error -> parse parsed ((filename, error) :: errors) rest
        | Ok result -> parse ((filename, result) :: parsed) errors rest)
  in
  let rec compile state compiled pending =
    match pending with
    | [] -> Ok (state, List.rev compiled, [])
    | _ ->
        let rec try_pending deferred errors = function
          | [] -> Ok (state, List.rev compiled, List.rev errors)
          | (filename, parsed) :: rest -> (
              match typecheck_incremental state parsed with
              | Error error ->
                  try_pending
                    ((filename, parsed) :: deferred)
                    ((filename, error) :: errors)
                    rest
              | Ok (next_state, _typed) ->
                  if not check_incremental_ocaml then
                    compile next_state (filename :: compiled)
                      (List.rev_append deferred rest)
                  else
                    match validate_ocaml next_state with
                    | Ok () ->
                        compile next_state (filename :: compiled)
                          (List.rev_append deferred rest)
                    | Error error ->
                        try_pending
                          ((filename, parsed) :: deferred)
                          ((filename, error) :: errors)
                          rest)
        in
        try_pending [] [] pending
  in
  match parse [] [] sources with
  | Error _ as err -> err
  | Ok (parsed, parse_errors) -> (
      match compile initial_state [] parsed with
      | Error _ as err -> err
      | Ok (_state, [], compile_errors) -> Ok ([], parse_errors @ compile_errors)
      | Ok (state, filenames, compile_errors) -> (
          match Lowering.structure_of_located_items state.located_items with
          | Error _ as err -> err
          | Ok structure -> (
              if Trace.enabled "compile.dump" then
                Printf.eprintf "%s\n%!"
                  (Ocaml_parsetree.print_implementation structure);
              match
                Ocaml_typechecker.analyze
                  ?compiler_env:initial_state.ocaml_env structure
              with
              | Error _ as err -> err
              | Ok analysis ->
                  let result filename =
                    {
                      typed_structure = analysis.typed_structure;
                      compiler_env = analysis.compiler_env;
                      typecheck_state = state.typecheck_state;
                      info_tree = Info_tree.snapshot ();
                      diagnostics =
                        List.filter
                          (fun diagnostic ->
                            match diagnostic.location with
                            | Some location ->
                                location.Location.loc_start.Lexing.pos_fname
                                = filename
                            | None -> false)
                          analysis.diagnostics;
                    }
                  in
                  Ok
                    ( List.map
                        (fun filename -> (filename, result filename))
                        filenames,
                      parse_errors @ compile_errors ))))

let analyze_workspace_with_errors ?(target = Target.default) sources =
  analyze_workspace_with_errors_from_state ~target empty_state sources

let analyze_from_state ?(target = Target.default) ?(filename = "<string>")
    state source =
  match
    analyze_workspace_with_errors_from_state ~target state
      [ (filename, source) ]
  with
  | Error _ as err -> err
  | Ok ((_, analysis) :: _, []) -> Ok analysis
  | Ok ([], (_, error) :: _) -> Error error
  | Ok ([], []) -> Error.error ~code:Error_code.Semantic "source contains no analyzable lg forms"
  | Ok ((_, analysis) :: _, _errors) -> Ok analysis

let interface_from_state ?(target = Target.default) ?(filename = "<string>")
    state source =
  analyze_from_state ~target ~filename state source
  |> Result.map interface_of_analysis

let analyze_workspace ?(target = Target.default) sources =
  match analyze_workspace_with_errors ~target sources with
  | Error _ as err -> err
  | Ok ([], (_, error) :: _) -> Error error
  | Ok ([], []) -> Error.error ~code:Error_code.Semantic "workspace contains no analyzable lg files"
  | Ok (analyses, []) -> Ok analyses
  | Ok (analyses, _errors) -> Ok analyses

let implementation_with_diagnostics ?(target = Target.default)
    ?(filename = "<string>") source =
  match Lg_frontend.implementation ~target ~filename source with
  | Error _ as err -> err
  | Ok parsed -> (
      match typecheck parsed with
      | Error _ as err -> err
      | Ok typed -> (
          match checked_parsetree typed with
          | Error _ as err -> err
          | Ok (result, diagnostics) ->
              Ok
                {
                  ocaml_source = Ocaml_parsetree_backend.print result.structure;
                  diagnostics;
                }))

let implementation ?(target = Target.default) ?(filename = "<string>") source =
  match implementation_with_diagnostics ~target ~filename source with
  | Error _ as err -> err
  | Ok compilation -> Ok compilation.ocaml_source

let implementation_parsetree ?(target = Target.default) ?(filename = "<string>")
    source =
  match Lg_frontend.implementation ~target ~filename source with
  | Error _ as err -> err
  | Ok parsed -> (
      match typecheck parsed with
      | Error _ as err -> err
      | Ok typed -> (
          match checked_parsetree typed with
          | Error _ as err -> err
          | Ok (result, _diagnostics) -> Ok result.structure))

let typecheck_parsetree ?(target = Target.default) ?(filename = "<string>")
    source =
  match Lg_frontend.implementation ~target ~filename source with
  | Error _ as err -> err
  | Ok parsed -> (
      match typecheck parsed with
      | Error _ as err -> err
      | Ok typed -> (
          match checked_parsetree typed with
          | Error _ as err -> err
          | Ok _ -> Ok ()))

let print_parsetree structure = Ocaml_parsetree_backend.print structure

let compile_prepared_chunk_with_diagnostics ?(check_ocaml = true) state
    prepared =
  let previous_set_modules = state.requested_set_modules in
  let parsed = prepared.parsed in
  match prepare_packages parsed.target parsed.ast with
  | Error _ as err -> err
  | Ok _ -> (
      match typecheck_incremental state parsed with
      | Error _ as err -> err
      | Ok (state, typed) ->
          (match
             Ocaml_parsetree_backend.implementation ~previous_set_modules typed
           with
          | Error _ as err -> err
          | Ok result ->
              let current_items = List.combine typed.locations typed.items in
              let requested_set_modules =
                List.sort_uniq String.compare
                  (previous_set_modules
                  @ Lowering.requested_set_modules_from_located_items
                      current_items)
              in
              let state =
                { state with located_items = []; requested_set_modules }
              in
              let reserved_modules =
                state.typecheck_state.env |> Compiler_environment.modules
                |> Module_registry.module_bindings
                |> List.map (fun (name, _) ->
                    match String.split_on_char '.' name with
                    | root :: _ -> root
                    | [] -> name)
              in
              let ocaml_source =
                Ocaml_parsetree_backend.print ~reserved_modules result.structure
              in
              if Trace.enabled "compile.dump" then
                Printf.eprintf "%s\n%!" ocaml_source;
              if not check_ocaml then
                Ok (state, { ocaml_source; diagnostics = [] })
              else
                match
                  Ocaml_typechecker.analyze ?compiler_env:state.ocaml_env
                    result.structure
                with
                | Error _ as err -> err
                | Ok analysis ->
                    let state =
                      { state with ocaml_env = Some analysis.compiler_env }
                    in
                    Ok
                      ( state,
                        {
                          ocaml_source;
                          diagnostics = analysis.diagnostics;
                        } )))

let compile_chunk_with_diagnostics ?(target = Target.default)
    ?(filename = "<string>") ?(check_ocaml = true) state source =
  Result.bind
    (prepare_source ~target ~filename source)
    (compile_prepared_chunk_with_diagnostics ~check_ocaml state)

let compile_chunk ?(target = Target.default) ?(filename = "<string>") state
    source =
  match compile_chunk_with_diagnostics ~target ~filename state source with
  | Error _ as err -> err
  | Ok (state, compilation) -> Ok (state, compilation.ocaml_source)

let compile_chunk_parsetree ?(target = Target.default) ?(filename = "<string>")
    ?(check_ocaml = true) state source =
  let previous_items = state.located_items in
  match Lg_frontend.implementation ~target ~filename source with
  | Error _ as err -> err
  | Ok parsed -> (
      match typecheck_incremental state parsed with
      | Error _ as err -> err
      | Ok (state, typed) -> (
          match
            Ocaml_parsetree_backend.implementation ~previous_items typed
          with
          | Error _ as err -> err
          | Ok result -> (
              if Trace.enabled "compile.dump" then
                Printf.eprintf "%s\n%!"
                  (Ocaml_parsetree_backend.print result.structure);
              if not check_ocaml then Ok (state, result.structure)
              else
                match
                  Ocaml_typechecker.analyze ?compiler_env:state.ocaml_env
                    result.structure
                with
                | Error _ as err -> err
                | Ok analysis ->
                    let state =
                      { state with ocaml_env = Some analysis.compiler_env }
                    in
                    Ok (state, result.structure))))

type pending_repl_kind =
  | Pending_value
  | Pending_definition of string
  | Pending_namespace
  | Pending_summary of string

let repl_form_error ?location message =
  Error.error ?location ~code:Error_code.Repl ~phase:`Semantic message

let rec first_source_name = function
  | Ast.FSymbol name :: _ when not (String.starts_with ~prefix:"^" name) ->
      Some name
  | _ :: rest -> first_source_name rest
  | [] -> None

let classify_repl_form form =
  match form with
  | Ast.FList (Ast.FSymbol "ns" :: _) -> Ok Pending_namespace
  | Ast.FList
      (Ast.FSymbol ("def" | "defonce" | "defn" | "defn-" | "ffi") :: rest) -> (
      match first_source_name rest with
      | Some name -> Ok (Pending_definition name)
      | None -> repl_form_error "REPL definition is missing its name")
  | Ast.FList (Ast.FSymbol "defmacro" :: rest) -> (
      match first_source_name rest with
      | Some name -> Ok (Pending_summary ("macro " ^ name))
      | None -> repl_form_error "REPL macro definition is missing its name")
  | Ast.FList
      (Ast.FSymbol
        (( "extern-type" | "type" | "type-record" | "type-variant" | "defrecord"
         | "deftype" | "defprotocol" | "module" | "module-signature" ) as
        head)
      :: rest) ->
      let name = first_source_name rest |> Option.value ~default:"<anonymous>" in
      Ok (Pending_summary (head ^ " " ^ name))
  | _ -> Ok Pending_value

let parse_single_repl_form ?(target = Target.default) source =
  match Lexer.tokenize source with
  | Error _ as error -> error
  | Ok tokens -> (
      match Parser.parse ~target tokens with
      | Error _ as error -> error
      | Ok [ form ] -> Ok form
      | Ok [] -> repl_form_error "REPL input contains no form"
      | Ok _ -> repl_form_error "REPL evaluation expects exactly one form")

let repl_definition_type state name =
  let scope = source_scope state in
  match Resolver.lookup_binding scope state.typecheck_state.env name with
  | Error _ -> repl_form_error ("unable to resolve REPL definition " ^ name)
  | Ok binding ->
      let binding = Types.instantiate_binding binding in
      let ty =
        Types.runtime_root_value_type binding
        |> Option.value ~default:binding.ty
      in
      Ok (Types.source_name ty)

let compile_repl_form ?(target = Target.default) ?(filename = "<string>")
    ?(check_ocaml = true) state source =
  match parse_single_repl_form ~target source with
  | Error _ as error -> error
  | Ok form -> (
      match classify_repl_form form with
      | Error _ as error -> error
      | Ok pending ->
          let compiled_source =
            match pending with
            | Pending_value -> "(__lg_repl-result " ^ source ^ "\n)"
            | Pending_definition _ | Pending_namespace | Pending_summary _ ->
                source
          in
          match
            compile_chunk_parsetree ~target ~filename ~check_ocaml state
              compiled_source
          with
          | Error _ as error -> error
          | Ok (next_state, structure) -> (
              match pending with
              | Pending_value ->
                  Ok (next_state, { structure; kind = Repl_value })
              | Pending_namespace ->
                  Ok
                    ( next_state,
                      {
                        structure;
                        kind = Repl_namespace (source_scope next_state);
                      } )
              | Pending_summary summary ->
                  Ok (next_state, { structure; kind = Repl_summary summary })
              | Pending_definition name ->
                  Result.map
                    (fun type_name ->
                      ( next_state,
                        {
                          structure;
                          kind = Repl_definition { name; type_name };
                        } ))
                    (repl_definition_type next_state name)))

let rec semantic_expression_type = function
  | Semantic_ir.Typed (ty, _) -> Some ty
  | Semantic_ir.Located (_, _, expression)
  | Semantic_ir.SharedValue (_, expression) ->
      semantic_expression_type expression
  | _ -> None

let rec repl_item_type = function
  | Lowered.Foreign_binding foreign -> Some foreign.value_type
  | Lowered.Value_binding { expression; _ }
  | Lowered.Recursive_value_binding { expression; _ }
  | Lowered.Deferred_value_binding { expression; _ } ->
      semantic_expression_type expression
  | Lowered.Recursive_value_bindings bindings ->
      List.find_map
        (fun (binding : Lowered.recursive_value) ->
          semantic_expression_type binding.expression)
        (List.rev bindings)
  | Lowered.Group items -> List.find_map repl_item_type (List.rev items)
  | Lowered.Polymorphic_holder_type _ | Lowered.Comment _
  | Lowered.Opaque_type _ | Lowered.Type_def _ | Lowered.Type_alias _ | Lowered.Type_variant _
  | Lowered.Module_def _ | Lowered.Module_alias _ | Lowered.Module_functor _
  | Lowered.Module_apply _ | Lowered.Module_signature _
  | Lowered.Open_module _ | Lowered.Include_module _ | Lowered.Record_def _
  | Lowered.Projected_record_def _ ->
      None

let rec drop count values =
  if count <= 0 then values
  else match values with [] -> [] | _ :: rest -> drop (count - 1) rest

let infer_repl_type ?(target = Target.default) state source =
  match parse_single_repl_form ~target source with
  | Error _ as error -> error
  | Ok form -> (
      match classify_repl_form form with
      | Error _ as error -> error
      | Ok Pending_namespace | Ok (Pending_summary _) ->
          repl_form_error "REPL form does not have a value type"
      | Ok (Pending_definition name) -> (
          match compile_chunk_parsetree ~target state source with
          | Error _ as error -> error
          | Ok (candidate_state, _) -> repl_definition_type candidate_state name)
      | Ok Pending_value ->
          let previous_count = List.length state.located_items in
          match compile_chunk_parsetree ~target state source with
          | Error _ as error -> error
          | Ok (candidate_state, _) ->
              let current_items =
                candidate_state.located_items
                |> drop previous_count |> List.map snd |> List.rev
              in
              (match List.find_map repl_item_type current_items with
              | Some ty -> Ok (Types.source_name ty)
              | None -> repl_form_error "unable to determine REPL form type"))
