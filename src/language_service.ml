type hover = {
  contents : string;
  range : Ast.source_span;
}

type completion_item = {
  label : string;
  detail : string;
}

type semantic_token_kind =
  [ `Namespace
  | `Type
  | `Function
  | `Variable
  | `Parameter
  | `Property
  | `Enum_member
  | `Interface
  | `Method
  | `Keyword
  | `String
  | `Number ]

type semantic_token = {
  range : Ast.source_span;
  kind : semantic_token_kind;
}

type signature_help = {
  label : string;
  parameters : string list;
  active_parameter : int;
}

type text_edit = {
  range : Ast.source_span;
  new_text : string;
}

type symbol_kind =
  [ `Module
  | `Function
  | `Variable
  | `Type
  | `Interface
  | `Method
  | `Field
  | `Constructor ]

type document_symbol = {
  name : string;
  detail : string option;
  kind : symbol_kind;
  range : Ast.source_span;
  selection_range : Ast.source_span;
  children : document_symbol list;
}

type t = {
  filename : string;
  source : string;
  tokens : Ast.token list;
  forms : Ast.located_form list;
  compiler : Toolchain.language_analysis;
}

let analyze ~filename source =
  match
    Compiler_session.run (fun () -> Toolchain.analyze ~filename source)
  with
  | Error _ as err -> err
  | Ok compiler -> (
      match Lexer.tokenize source with
      | Error _ as err -> err
      | Ok tokens -> (
          match Parser.parse_located ~eof_offset:(String.length source) tokens with
          | Error _ as err -> err
          | Ok forms -> Ok { filename; source; tokens; forms; compiler }))

let analyze_from_state ?(target = Target.default) ~filename state source =
  match
    Compiler_session.run (fun () ->
        Toolchain.analyze_from_state ~target ~filename state source)
  with
  | Error _ as err -> err
  | Ok compiler -> (
      match Lexer.tokenize source with
      | Error _ as err -> err
      | Ok tokens -> (
          match Parser.parse_located ~eof_offset:(String.length source) tokens with
          | Error _ as err -> err
          | Ok forms -> Ok { filename; source; tokens; forms; compiler }))

let recover_completed_prefix ~filename source =
  match Lexer.tokenize source with
  | Error _ -> None
  | Ok tokens -> (
      let forms, error =
        Parser.parse_located_recovering ~eof_offset:(String.length source) tokens
      in
      match (List.rev forms, error) with
      | last :: _, Some _ ->
          let prefix = String.sub source 0 last.Ast.span.end_offset in
          analyze ~filename prefix |> Result.to_option
      | _ -> None)

let analyze_workspace_with_errors_using analyze_compiler sources =
  let rec parse acc = function
    | [] -> Ok (List.rev acc)
    | (filename, source) :: rest -> (
        match Lexer.tokenize source with
        | Error _ -> parse acc rest
        | Ok tokens -> (
            match
              Parser.parse_located ~eof_offset:(String.length source) tokens
            with
            | Error _ -> parse acc rest
            | Ok forms -> parse ((filename, source, tokens, forms) :: acc) rest))
  in
  match parse [] sources with
  | Error _ as err -> err
  | Ok parsed -> (
      match analyze_compiler sources with
      | Error _ as err -> err
      | Ok (analyses, errors) ->
          let compiler filename = List.assoc_opt filename analyses in
          Ok
            ( List.filter_map
                (fun (filename, source, tokens, forms) ->
                  compiler filename
                  |> Option.map (fun compiler ->
                         ( filename,
                           { filename; source; tokens; forms; compiler } )))
                parsed,
              errors ))

let analyze_workspace_with_errors sources =
  analyze_workspace_with_errors_using
    (fun sources ->
      Compiler_session.run (fun () ->
          Toolchain.analyze_workspace_with_errors sources))
    sources

let analyze_workspace_with_errors_from_state ?(target = Target.default) state
    sources =
  analyze_workspace_with_errors_using
    (fun sources ->
      Compiler_session.run (fun () ->
          Toolchain.analyze_workspace_with_errors_from_state ~target
            ~check_incremental_ocaml:false state sources))
    sources

let analyze_workspace sources =
  match analyze_workspace_with_errors sources with
  | Error _ as err -> err
  | Ok ([], (_, error) :: _) -> Error error
  | Ok ([], []) -> Error.error ~code:Error_code.Semantic "workspace contains no analyzable lg files"
  | Ok (analyses, []) -> Ok analyses
  | Ok (analyses, _errors) -> Ok analyses

let analyze_workspace_from_state ?(target = Target.default) state sources =
  match analyze_workspace_with_errors_from_state ~target state sources with
  | Error _ as err -> err
  | Ok ([], (_, error) :: _) -> Error error
  | Ok ([], []) -> Error.error ~code:Error_code.Semantic "workspace contains no analyzable lg files"
  | Ok (analyses, []) -> Ok analyses
  | Ok (analyses, _errors) -> Ok analyses

let diagnostics analysis = analysis.compiler.diagnostics

let token_at analysis offset =
  List.find_opt
    (fun (token : Ast.token) ->
      token.span.start_offset <= offset && offset < token.span.end_offset)
    analysis.tokens

let symbol_span_at analysis offset =
  match token_at analysis offset with
  | Some { desc = Symbol _; span } -> Some span
  | _ -> None

let location_contains_offset location offset =
  (not location.Location.loc_ghost)
  && location.loc_start.Lexing.pos_cnum <= offset
  && offset < location.loc_end.Lexing.pos_cnum

let location_size location =
  location.Location.loc_end.Lexing.pos_cnum
  - location.loc_start.Lexing.pos_cnum

let smallest_expression typed_structure offset predicate =
  let best = ref None in
  let consider expression =
    if location_contains_offset expression.Typedtree.exp_loc offset && predicate expression
    then
      match !best with
      | None -> best := Some expression
      | Some current
        when location_size expression.exp_loc < location_size current.exp_loc ->
          best := Some expression
      | Some _ -> ()
  in
  let base = Tast_iterator.default_iterator in
  let iterator =
    {
      base with
      expr =
        (fun self expression ->
          consider expression;
          base.expr self expression);
    }
  in
  iterator.structure iterator typed_structure;
  !best

let source_node_ids_of_attributes attributes =
  attributes
  |> List.filter_map
       (fun ({ Parsetree.attr_name = { txt; _ }; attr_payload; _ } : Parsetree.attribute) ->
         if txt <> "lg.node_id" then None
         else
           match attr_payload with
           | PStr
               [ { pstr_desc =
                     Pstr_eval
                       ( { pexp_desc =
                             Pexp_constant
                               { pconst_desc = Pconst_string (id, _, _); _ };
                           _ },
                         _ );
                   _ } ] ->
               Some id
           | _ -> None)

let source_node_id_of_attributes attributes =
  match source_node_ids_of_attributes attributes with
  | id :: _ -> Some id
  | [] -> None

let source_node_id_range id =
  match String.rindex_opt id ':' with
  | None -> None
  | Some separator -> (
      let range =
        String.sub id (separator + 1) (String.length id - separator - 1)
      in
      match String.split_on_char '-' range with
      | [ start_offset; end_offset ] -> (
          match (int_of_string_opt start_offset, int_of_string_opt end_offset) with
          | Some start_offset, Some end_offset -> Some (start_offset, end_offset)
          | _ -> None)
      | _ -> None)

let source_node_id_in_attributes attributes offset =
  source_node_ids_of_attributes attributes
  |> List.filter_map (fun id ->
         match source_node_id_range id with
         | Some (start_offset, end_offset)
           when start_offset <= offset && offset < end_offset ->
             Some (end_offset - start_offset, id)
         | Some _ | None -> None)
  |> List.sort (fun (left, _) (right, _) -> Int.compare left right)
  |> function (_, id) :: _ -> Some id | [] -> None

let source_node_id_of_pattern pattern =
  match source_node_id_of_attributes pattern.Typedtree.pat_attributes with
  | Some _ as id -> id
  | None ->
      pattern.pat_extra
      |> List.find_map (fun (_, _, attributes) ->
             source_node_id_of_attributes attributes)

let source_node_id_at analysis ~offset =
  let expression =
    smallest_expression analysis.compiler.typed_structure offset (fun expression ->
        Option.is_some
          (source_node_id_in_attributes expression.exp_attributes offset))
  in
  let pattern = ref None in
  let base = Tast_iterator.default_iterator in
  let consider_pattern pattern_value =
    if
      location_contains_offset pattern_value.Typedtree.pat_loc offset
      && Option.is_some (source_node_id_of_pattern pattern_value)
    then
      match !pattern with
      | None ->
          pattern :=
            Some (pattern_value.pat_loc, source_node_id_of_pattern pattern_value)
      | Some (current_location, _)
        when location_size pattern_value.pat_loc
             < location_size current_location ->
          pattern :=
            Some (pattern_value.pat_loc, source_node_id_of_pattern pattern_value)
      | Some _ -> ();
  in
  let visit_pattern : type k.
      Tast_iterator.iterator -> k Typedtree.general_pattern -> unit =
   fun self pattern_value ->
    consider_pattern pattern_value;
    base.pat self pattern_value
  in
  let iterator =
    { base with
      pat = visit_pattern;
      expr =
        (fun self expression ->
          (match expression.Typedtree.exp_desc with
          | Texp_function (params, _) ->
              List.iter
                (fun param ->
                  match param.Typedtree.fp_kind with
                  | Tparam_pat pattern -> consider_pattern pattern
                  | Tparam_optional_default (pattern, _) ->
                      consider_pattern pattern)
                params
          | _ -> ());
          base.expr self expression);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  let smaller_id left right =
    match (source_node_id_range left, source_node_id_range right) with
    | Some (left_start, left_end), Some (right_start, right_end) ->
        if left_end - left_start <= right_end - right_start then left else right
    | Some _, None -> left
    | None, Some _ -> right
    | None, None -> left
  in
  match (expression, !pattern) with
  | None, None -> None
  | Some expression, None ->
      source_node_id_in_attributes expression.exp_attributes offset
  | None, Some (_, id) -> id
  | Some expression, Some (_pattern_location, pattern_id) -> (
      match
        ( pattern_id,
          source_node_id_in_attributes expression.exp_attributes offset )
      with
      | Some pattern_id, Some expression_id ->
          Some (smaller_id pattern_id expression_id)
      | Some id, None | None, Some id -> Some id
      | None, None -> None)

let source_type_name printed =
  let is_identifier_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  let length = String.length printed in
  let buffer = Buffer.create length in
  let rec copy index =
    if index >= length then Buffer.contents buffer
    else
      let is_int64 =
        index + 5 <= length
        && String.sub printed index 5 = "int64"
        && (index = 0 || not (is_identifier_char printed.[index - 1]))
        && (index + 5 = length
           || not (is_identifier_char printed.[index + 5]))
      in
      if is_int64 then (
        Buffer.add_string buffer "int";
        copy (index + 5))
      else (
        Buffer.add_char buffer printed.[index];
        copy (index + 1))
  in
  copy 0

let print_type env ty =
  Printtyp.wrap_printing_env ~error:false env (fun () ->
      Format.asprintf "%a" Printtyp.type_scheme ty)
  |> source_type_name

let source_symbol_basename name =
  match String.rindex_opt name '/' with
  | None -> name
  | Some index -> String.sub name (index + 1) (String.length name - index - 1)

let is_core_symbol_candidate name =
  match String.rindex_opt name '/' with
  | None -> true
  | Some index ->
      let qualifier = String.sub name 0 index in
      String.equal qualifier "clojure.core"
      || String.equal qualifier "cljs.core"

let identifier_name_matches source_name path =
  let expected = source_symbol_basename source_name |> Names.sanitize_name in
  let actual = Path.name path |> Names.sanitize_name in
  actual = expected || String.ends_with ~suffix:("_" ^ expected) actual

let expression_hover analysis ~offset =
  match symbol_span_at analysis offset with
  | None -> None
  | Some range ->
      let identifier expression =
        match expression.Typedtree.exp_desc with
        | Typedtree.Texp_ident _ -> true
        | _ -> false
      in
      let expression =
        match
          smallest_expression analysis.compiler.typed_structure offset identifier
        with
        | Some _ as expression -> expression
        | None ->
            smallest_expression analysis.compiler.typed_structure offset (fun _ -> true)
      in
      expression
      |> Option.map (fun (expression : Typedtree.expression) ->
             {
               contents = print_type expression.exp_env expression.exp_type;
               range;
             })

type semantic_key =
  | Ocaml_uid of Typedtree.Uid.t
  | Protocol_key of Protocol_id.t
  | Method_key of Method_id.t

type semantic_identity = {
  key : semantic_key;
  definition_location : Location.t;
}

type semantic_occurrence = {
  identity : semantic_identity;
  range : Ast.source_span;
}

let compare_semantic_key left right =
  match (left, right) with
  | Ocaml_uid left, Ocaml_uid right -> Typedtree.Uid.compare left right
  | Protocol_key left, Protocol_key right -> Protocol_id.compare left right
  | Method_key left, Method_key right -> Method_id.compare left right
  | Ocaml_uid _, _ -> -1
  | _, Ocaml_uid _ -> 1
  | Protocol_key _, _ -> -1
  | _, Protocol_key _ -> 1

let equal_semantic_key left right = compare_semantic_key left right = 0

let consider_semantic_identity best ~offset ~location ~matches ~uid
    ~definition_location =
  if location_contains_offset location offset && matches then
    let size = location_size location in
    match !best with
    | None -> best := Some (size, { key = Ocaml_uid uid; definition_location })
    | Some (current_size, _) when size < current_size ->
        best := Some (size, { key = Ocaml_uid uid; definition_location })
    | Some _ -> ()

let best_semantic_identity best = Option.map snd !best

let identifier_identity_at analysis offset source_name =
  match
    smallest_expression analysis.compiler.typed_structure offset
      (fun expression ->
        match expression.Typedtree.exp_desc with
        | Typedtree.Texp_ident (path, _, _) ->
            identifier_name_matches source_name path
        | _ -> false)
  with
  | Some { Typedtree.exp_desc = Texp_ident (_, _, description); _ } ->
      Some
        {
          key = Ocaml_uid description.val_uid;
          definition_location = description.val_loc;
        }
  | Some _ | None -> None

let binding_identity_at analysis offset source_name =
  let best = ref None in
  let consider location name uid =
    consider_semantic_identity best ~offset ~location
      ~matches:
        (Names.sanitize_name source_name = Names.sanitize_name name)
      ~uid ~definition_location:location
  in
  let base = Tast_iterator.default_iterator in
  let iterator =
    {
      base with
      pat =
        (fun (type kind) self
             (pattern : kind Typedtree.general_pattern) ->
          (match pattern.pat_desc with
          | Typedtree.Tpat_var (_, name, uid) ->
              consider pattern.pat_loc name.txt uid
          | Typedtree.Tpat_alias (_, _, name, uid, _) ->
              consider pattern.pat_loc name.txt uid
          | _ -> ());
          base.pat self pattern);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  best_semantic_identity best

let constructor_name_matches source_name constructor_name =
  Names.sanitize_name (source_symbol_basename source_name)
  = Names.sanitize_name constructor_name

let constructor_identity_at analysis offset source_name =
  let best = ref None in
  let consider location name uid definition_location =
    consider_semantic_identity best ~offset ~location
      ~matches:(constructor_name_matches source_name name) ~uid
      ~definition_location
  in
  let base = Tast_iterator.default_iterator in
  let visit_pattern : type kind.
      Tast_iterator.iterator -> kind Typedtree.general_pattern -> unit =
   fun self pattern ->
    (match pattern.pat_desc with
    | Typedtree.Tpat_construct (_, description, _, _) ->
        consider pattern.pat_loc description.cstr_name description.cstr_uid
          description.cstr_loc
    | _ -> ());
    base.pat self pattern
  in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          (match expression.Typedtree.exp_desc with
          | Texp_construct (_, description, _) ->
              consider expression.exp_loc description.cstr_name
                description.cstr_uid description.cstr_loc
          | _ -> ());
          base.expr self expression);
      pat = visit_pattern;
      type_declaration =
        (fun self declaration ->
          (match declaration.Typedtree.typ_kind with
          | Ttype_variant constructors ->
              List.iter
                (fun (constructor : Typedtree.constructor_declaration) ->
                  consider constructor.cd_loc constructor.cd_name.txt
                    constructor.cd_uid constructor.cd_loc)
                constructors
          | _ -> ());
          base.type_declaration self declaration);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  best_semantic_identity best

let label_name_matches source_name label_name =
  Names.sanitize_name (source_symbol_basename source_name)
  = Names.sanitize_name label_name

let label_identity_at analysis offset source_name =
  let best = ref None in
  let consider location name uid definition_location =
    consider_semantic_identity best ~offset ~location
      ~matches:(label_name_matches source_name name) ~uid ~definition_location
  in
  let consider_description location description =
    consider location description.Data_types.lbl_name description.lbl_uid
      description.lbl_loc
  in
  let base = Tast_iterator.default_iterator in
  let visit_pattern : type kind.
      Tast_iterator.iterator -> kind Typedtree.general_pattern -> unit =
   fun self pattern ->
    (match pattern.pat_desc with
    | Typedtree.Tpat_record (fields, _) ->
        List.iter
          (fun (_, description, _) ->
            consider_description pattern.pat_loc description)
          fields
    | _ -> ());
    base.pat self pattern
  in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          (match expression.Typedtree.exp_desc with
          | Texp_record { fields; _ } ->
              Array.iter
                (fun ((description : Data_types.label_description), _) ->
                  consider_description expression.exp_loc description)
                fields
          | Texp_field (_, _, description)
          | Texp_atomic_loc (_, _, description) ->
              consider_description expression.exp_loc description
          | Texp_setfield (_, _, description, _) ->
              consider_description expression.exp_loc description
          | _ -> ());
          base.expr self expression);
      pat = visit_pattern;
      type_declaration =
        (fun self declaration ->
          (match declaration.Typedtree.typ_kind with
          | Ttype_record fields ->
              List.iter
                (fun (field : Typedtree.label_declaration) ->
                  consider field.ld_loc field.ld_name.txt field.ld_uid field.ld_loc)
                fields
          | _ -> ());
          base.type_declaration self declaration);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  best_semantic_identity best

let source_type_name source_name =
  let strip prefix value =
    if String.starts_with ~prefix value then
      String.sub value (String.length prefix)
        (String.length value - String.length prefix)
    else value
  in
  source_name |> strip "^:" |> strip "^" |> strip ":"

let is_type_annotation source_name =
  String.starts_with ~prefix:"^" source_name

let type_annotation_name_range source_name (span : Ast.source_span) =
  let prefix_length =
    if String.starts_with ~prefix:"^:" source_name then 2
    else if is_type_annotation source_name then 1
    else 0
  in
  { span with start_offset = span.start_offset + prefix_length }

let ocaml_type_name source_name =
  match List.rev (String.split_on_char '.' (source_type_name source_name)) with
  | [] -> source_name
  | type_name :: reversed_modules ->
      let type_name = Names.sanitize_name type_name in
      (match List.rev reversed_modules with
      | [] -> type_name
      | modules ->
          Names.module_path_to_ocaml (String.concat "." modules)
          ^ "." ^ type_name)

let longident_of_dotted_name name =
  match String.split_on_char '.' name with
  | [] -> Longident.Lident name
  | first :: rest ->
      List.fold_left
        (fun path segment ->
          Longident.Ldot (Location.mknoloc path, Location.mknoloc segment))
        (Longident.Lident first) rest

let type_name_matches source_name path =
  Path.name path = ocaml_type_name source_name

let type_identity_at analysis offset source_name =
  let best = ref None in
  let consider location path declaration =
    consider_semantic_identity best ~offset ~location
      ~matches:(type_name_matches source_name path)
      ~uid:(Lg_compiler_support.Ocaml_type.uid declaration)
      ~definition_location:
        (Lg_compiler_support.Ocaml_type.location declaration)
  in
  let base = Tast_iterator.default_iterator in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          if location_contains_offset expression.Typedtree.exp_loc offset then
            let longident =
              longident_of_dotted_name (ocaml_type_name source_name)
            in
            (match Env.find_type_by_name longident expression.exp_env with
            | path, declaration ->
                consider expression.exp_loc path declaration
            | exception Not_found -> ());
          base.expr self expression);
      typ =
        (fun self core_type ->
          (match core_type.Typedtree.ctyp_desc with
          | Ttyp_constr (path, _, _) ->
              let declaration = Env.find_type path core_type.ctyp_env in
              consider core_type.ctyp_loc path declaration
          | _ -> ());
          base.typ self core_type);
      type_declaration =
        (fun self declaration ->
          let path = Path.Pident declaration.Typedtree.typ_id in
          consider declaration.typ_loc path declaration.typ_type;
          base.type_declaration self declaration);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  match best_semantic_identity best with
  | Some _ as identity -> identity
  | None when is_type_annotation source_name -> (
      let longident = longident_of_dotted_name (ocaml_type_name source_name) in
      match
        Env.find_type_by_name longident
          analysis.compiler.typed_structure.str_final_env
      with
      | _, declaration ->
          Some
            { key =
                Ocaml_uid (Lg_compiler_support.Ocaml_type.uid declaration);
              definition_location =
                Lg_compiler_support.Ocaml_type.location declaration }
      | exception Not_found -> None)
  | None -> None

let module_name_matches source_name path =
  Path.name path = Names.module_path_to_ocaml source_name

let module_identity_at analysis offset source_name =
  let best = ref None in
  let consider location path uid definition_location =
    consider_semantic_identity best ~offset ~location
      ~matches:(module_name_matches source_name path) ~uid ~definition_location
  in
  let base = Tast_iterator.default_iterator in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          if location_contains_offset expression.Typedtree.exp_loc offset then
            match
              Env.find_module_by_name
                (longident_of_dotted_name
                   (Names.module_path_to_ocaml source_name))
                expression.exp_env
            with
            | path, declaration ->
                consider expression.exp_loc path
                  (Lg_compiler_support.Ocaml_module.uid declaration)
                  (Lg_compiler_support.Ocaml_module.location declaration)
            | exception Not_found -> ();
          base.expr self expression);
      module_expr =
        (fun self module_expression ->
          (match module_expression.Typedtree.mod_desc with
          | Tmod_ident (path, _) ->
              let declaration = Env.find_module path module_expression.mod_env in
              consider module_expression.mod_loc path
                (Lg_compiler_support.Ocaml_module.uid declaration)
                (Lg_compiler_support.Ocaml_module.location declaration)
          | Tmod_functor
              (Typedtree.Named (Some id, parameter_name, _), body) ->
              let path = Path.Pident id in
              let declaration = Env.find_module path body.mod_env in
              consider parameter_name.loc path
                (Lg_compiler_support.Ocaml_module.uid declaration)
                (Lg_compiler_support.Ocaml_module.location declaration)
          | _ -> ());
          base.module_expr self module_expression);
      module_binding =
        (fun self binding ->
          (match (binding.Typedtree.mb_name.txt, binding.mb_id) with
          | Some _, Some id ->
              consider binding.mb_name.loc (Path.Pident id) binding.mb_uid
                binding.mb_name.loc
          | _ -> ());
          base.module_binding self binding);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  best_semantic_identity best

let module_type_identity_at analysis offset source_name =
  let best = ref None in
  let consider location path uid definition_location =
    consider_semantic_identity best ~offset ~location
      ~matches:(module_name_matches source_name path) ~uid
      ~definition_location
  in
  let base = Tast_iterator.default_iterator in
  let iterator =
    { base with
      module_type =
        (fun self module_type ->
          (match module_type.Typedtree.mty_desc with
          | Tmty_ident (path, _) ->
              let declaration = Env.find_modtype path module_type.mty_env in
              consider module_type.mty_loc path
                (Lg_compiler_support.Ocaml_module.type_uid declaration)
                (Lg_compiler_support.Ocaml_module.type_location declaration)
          | _ -> ());
          base.module_type self module_type);
      module_type_declaration =
        (fun self declaration ->
          consider declaration.Typedtree.mtd_name.loc
            (Path.Pident declaration.mtd_id) declaration.mtd_uid
            declaration.mtd_name.loc;
          base.module_type_declaration self declaration);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  best_semantic_identity best

let ocaml_module_path_of_namespace namespace =
  let ocaml_prefix = "ocaml." in
  if String.starts_with ~prefix:ocaml_prefix namespace then
    String.sub namespace (String.length ocaml_prefix)
      (String.length namespace - String.length ocaml_prefix)
  else Names.module_path_to_ocaml namespace

let starts_with_uppercase name =
  String.length name > 0
  &&
  let first = name.[0] in
  first >= 'A' && first <= 'Z'

let is_ocaml_module_path name =
  match String.split_on_char '.' name with
  | first :: _ -> starts_with_uppercase first
  | [] -> false

let module_identity_by_ocaml_path analysis module_path =
  match
    Env.find_module_by_name (longident_of_dotted_name module_path)
      analysis.compiler.typed_structure.str_final_env
  with
  | _path, declaration ->
      Some
        {
          key =
            Ocaml_uid (Lg_compiler_support.Ocaml_module.uid declaration);
          definition_location =
            Lg_compiler_support.Ocaml_module.location declaration;
        }
  | exception _ -> None

let value_identity_by_ocaml_path analysis value_path =
  match
    Env.find_value_by_name (longident_of_dotted_name value_path)
      analysis.compiler.typed_structure.str_final_env
  with
  | _, description ->
      Some
        {
          key = Ocaml_uid description.val_uid;
          definition_location = description.val_loc;
        }
  | exception _ -> None

let constructor_identity_by_ocaml_path analysis constructor_path =
  match
    Env.lookup_constructor ~use:false ~loc:Location.none Env.Positive
      (longident_of_dotted_name constructor_path)
      analysis.compiler.typed_structure.str_final_env
  with
  | description ->
      Some
        {
          key = Ocaml_uid description.cstr_uid;
          definition_location = description.cstr_loc;
        }
  | exception _ -> None

let value_location_by_ocaml_path env value_path =
  match Env.find_value_by_name (longident_of_dotted_name value_path) env with
  | _, description -> Some description.val_loc
  | exception Not_found -> None

let constructor_location_by_ocaml_path env constructor_path =
  match
    Env.lookup_constructor ~use:false ~loc:Location.none Env.Positive
      (longident_of_dotted_name constructor_path)
      env
  with
  | description -> Some description.cstr_loc
  | exception _ -> None

let value_hover_by_ocaml_path env source_name range value_path =
  match Env.find_value_by_name (longident_of_dotted_name value_path) env with
  | _, description ->
      Some
        {
          contents =
            source_symbol_basename source_name ^ " : "
            ^ print_type env description.val_type;
          range;
        }
  | exception Not_found -> None

let constructor_hover_by_ocaml_path env source_name range constructor_path =
  match
    Env.lookup_constructor ~use:false ~loc:Location.none Env.Positive
          (longident_of_dotted_name constructor_path)
          env
  with
  | description ->
      let argument_types = List.map (print_type env) description.cstr_args in
      let result_type = print_type env description.cstr_res in
      let signature =
        match argument_types with
        | [] -> result_type
        | _ -> String.concat " -> " (argument_types @ [ result_type ])
      in
      Some
        {
          contents =
            source_symbol_basename source_name ^ " : " ^ signature;
          range;
        }
  | exception _ -> None

let ocaml_alias_module_path analysis alias =
  let state = analysis.compiler.typecheck_state in
  match
    Compiler_environment.resolve_namespace_alias ~scope:state.scope alias
      state.env
  with
  | Some namespace -> Some (ocaml_module_path_of_namespace namespace)
  | None -> None

let ocaml_alias_module_identity_at analysis alias =
  ocaml_alias_module_path analysis alias
  |> fun module_path ->
  Option.bind module_path (module_identity_by_ocaml_path analysis)

let ocaml_alias_member_identity_at analysis alias member =
  ocaml_alias_module_path analysis alias
  |> fun module_path ->
  Option.bind module_path (fun module_path ->
         let value_path = module_path ^ "." ^ Names.ocaml_member_name member in
         match value_identity_by_ocaml_path analysis value_path with
         | Some _ as identity -> identity
         | None ->
             constructor_identity_by_ocaml_path analysis
               (module_path ^ "." ^ member))

let require_alias_occurrence_at analysis offset =
  let contains (span : Ast.source_span) =
    span.start_offset <= offset && offset < span.end_offset
  in
  let with_fallback_location fallback identity =
    if identity.definition_location.Location.loc_ghost then
      { identity with definition_location = fallback }
    else identity
  in
  let rec alias_target = function
    | { Ast.form = Ast.FKeyword (":as" | "as") | FSymbol (":as" | "as"); _ }
      :: { form = FSymbol alias; span; _ }
      :: _ when contains span ->
        Some alias
    | _ :: rest -> alias_target rest
    | [] -> None
  in
  let require_spec = function
    | { Ast.form = Ast.FVector
          (Ast.FSymbol namespace :: _);
        span = vector_span;
        children =
          ({ form = FSymbol namespace_symbol; span = namespace_span; _ } :: rest);
        _ }
      when String.equal namespace namespace_symbol
           && (contains namespace_span || contains vector_span) ->
        let alias =
          match alias_target rest with
          | Some alias -> Some alias
          | None when contains namespace_span -> Some namespace
          | None -> None
        in
        Option.bind alias (fun alias ->
            module_identity_by_ocaml_path analysis
              (ocaml_module_path_of_namespace namespace)
            |> Option.map (fun identity ->
                   let identity =
                     with_fallback_location
                       (Parser.location_of_span namespace_span)
                       identity
                   in
                   {
                     identity;
                     range =
                       if contains namespace_span then namespace_span
                       else
                         rest
                         |> List.find_map (fun child ->
                                match child.Ast.form with
                                | FSymbol candidate when String.equal candidate alias ->
                                    Some child.span
                                | _ -> None)
                         |> Option.value ~default:namespace_span;
                   }))
    | _ -> None
  in
  let clause_is_require = function
    | { Ast.form =
          FList
            ((FKeyword "require" | FKeyword ":require" | FSymbol ":require"
             | FSymbol "require")
             :: _);
        _ } ->
        true
    | _ -> false
  in
  let rec find_require_spec form =
    match require_spec form with
    | Some _ as occurrence -> occurrence
    | None -> List.find_map find_require_spec form.Ast.children
  in
  let find form =
    match form.Ast.form with
    | FList (FSymbol "ns" :: _namespace :: _) ->
        form.children
        |> List.filter clause_is_require
        |> List.find_map find_require_spec
    | FList (FSymbol "require" :: _) -> find_require_spec form
    | _ -> None
  in
  List.find_map find analysis.forms

let protocol_registry analysis =
  analysis.compiler.typecheck_state.env |> Compiler_environment.protocols

let protocol_id_named analysis source_name =
  let registry = protocol_registry analysis in
  let direct = Protocol_id.of_string source_name in
  match Protocol_registry.find_protocol direct registry with
  | Some _ -> Some direct
  | None ->
      Protocol_registry.declarations registry
      |> List.find_map (fun (protocol_id, _) ->
             if Protocol_id.name protocol_id = source_name then Some protocol_id
             else None)

let protocol_identity_at analysis source_name =
  let registry = protocol_registry analysis in
  Option.bind (protocol_id_named analysis source_name) (fun protocol_id ->
         Protocol_registry.protocol_location protocol_id registry
         |> Option.map (fun definition_location ->
                { key = Protocol_key protocol_id; definition_location }))

let method_identity analysis protocol_id method_name =
  let method_id = Protocol.method_id protocol_id method_name in
  Protocol_registry.method_location protocol_id method_id
    (protocol_registry analysis)
  |> Option.map (fun definition_location ->
         { key = Method_key method_id; definition_location })

let protocol_defines_method analysis protocol_name method_name =
  match protocol_id_named analysis protocol_name with
  | None -> false
  | Some protocol_id ->
      let method_id = Protocol.method_id protocol_id method_name in
      Option.is_some
        (Protocol_registry.find_method protocol_id method_id
           (protocol_registry analysis))

let method_identity_at analysis offset ?protocol_name method_name =
  let registry = protocol_registry analysis in
  let declaration_identity =
    Protocol_registry.declarations registry
    |> List.find_map (fun (_, (declaration : Protocol_registry.declaration)) ->
           Protocol_registry.Method_map.bindings declaration.method_locations
           |> List.find_map (fun (method_id, location) ->
                  if
                    Method_id.name method_id = method_name
                    && location_contains_offset location offset
                  then
                    Some
                      { key = Method_key method_id;
                        definition_location = location }
                  else None))
  in
  let implementation_identity () =
    Protocol_registry.implementation_locations registry
    |> List.find_map (fun ((protocol_id, method_id, _), location) ->
           if
             Method_id.name method_id = method_name
             && location_contains_offset location offset
           then
             Protocol_registry.method_location protocol_id method_id registry
             |> Option.map (fun definition_location ->
                    { key = Method_key method_id; definition_location })
           else None)
  in
  let located =
    match declaration_identity with
    | Some _ as identity -> identity
    | None -> implementation_identity ()
  in
  match located with
  | Some _ as identity -> identity
  | None -> (
      match protocol_name with
      | Some protocol_name ->
          Option.bind (protocol_id_named analysis protocol_name) (fun protocol_id ->
                 method_identity analysis protocol_id method_name)
      | None -> (
          match
            Protocol_registry.protocols_for_method ~owner:[] ~method_name registry
          with
          | [ protocol_id ] -> method_identity analysis protocol_id method_name
          | [] | _ :: _ :: _ -> None))

let qualified_symbol_parts (token : Ast.token) source_name =
  if
    is_type_annotation source_name
    || String.starts_with ~prefix:":" source_name
  then None
  else
    let separator =
      match String.rindex_opt source_name '/' with
      | Some _ as separator -> separator
      | None -> String.rindex_opt source_name '.'
    in
    match separator with
    | Some index when index > 0 && index + 1 < String.length source_name ->
        let qualifier = String.sub source_name 0 index in
        let member =
          String.sub source_name (index + 1)
            (String.length source_name - index - 1)
        in
        Some
          ( qualifier,
            { Ast.start_offset = token.span.start_offset;
              end_offset = token.span.start_offset + index },
            member,
            { Ast.start_offset = token.span.start_offset + index + 1;
              end_offset = token.span.end_offset } )
    | _ -> None

type source_symbol_role =
  | Module_name
  | Protocol_name of string
  | Protocol_method of string

let source_symbol_role_at analysis offset =
  let contains (span : Ast.source_span) =
    span.start_offset <= offset && offset < span.end_offset
  in
  let qualify scope name = if scope = "" then name else scope ^ "/" ^ name in
  let rec find scope (form : Ast.located_form) =
    match form.children with
    | { form = FSymbol "module"; _ }
      :: ({ form = FSymbol module_name; span; _ } as _name)
      :: body ->
        if contains span then Some Module_name
        else
          let nested_scope = if scope = "" then module_name else scope ^ "." ^ module_name in
          List.find_map (find nested_scope) body
    | { form = FSymbol "defprotocol"; _ }
      :: { form = FSymbol protocol_name; span; _ }
      :: methods ->
        let protocol_name = qualify scope protocol_name in
        if contains span then Some (Protocol_name protocol_name)
        else
          methods
          |> List.find_map (fun (method_form : Ast.located_form) ->
                 match method_form.children with
                 | { form = FSymbol _; span; _ } :: _ when contains span ->
                     Some (Protocol_method protocol_name)
                 | _ -> None)
    | { form = FSymbol "extend-type"; _ }
      :: _receiver
      :: { form = FSymbol protocol_name; span; _ }
      :: methods ->
        let protocol_name = qualify scope protocol_name in
        if contains span then Some (Protocol_name protocol_name)
        else
          methods
          |> List.find_map (fun (method_form : Ast.located_form) ->
                 match method_form.children with
                 | { form = FSymbol _; span; _ } :: _ when contains span ->
                     Some (Protocol_method protocol_name)
                 | _ -> None)
    | children -> List.find_map (find scope) children
  in
  List.find_map (find "") analysis.forms

let member_identity_at analysis offset source_name =
  match identifier_identity_at analysis offset source_name with
  | Some _ as identity -> identity
  | None -> (
      match binding_identity_at analysis offset source_name with
      | Some _ as identity -> identity
      | None -> (
          match constructor_identity_at analysis offset source_name with
          | Some _ as identity -> identity
          | None -> (
              match label_identity_at analysis offset source_name with
              | Some _ as identity -> identity
              | None -> type_identity_at analysis offset source_name)))

let semantic_occurrence_at analysis offset =
  match token_at analysis offset with
  | Some ({ desc = Symbol source_name; span; _ } as token) -> (
      match require_alias_occurrence_at analysis offset with
      | Some _ as occurrence -> occurrence
      | None -> (
      match qualified_symbol_parts token source_name with
      | Some (qualifier, qualifier_range, member, _)
        when offset < qualifier_range.end_offset ->
          (if protocol_defines_method analysis qualifier member then
             protocol_identity_at analysis qualifier
           else
             match ocaml_alias_module_identity_at analysis qualifier with
             | Some _ as identity -> identity
             | None -> module_identity_at analysis offset qualifier)
          |> Option.map (fun identity -> { identity; range = qualifier_range })
      | qualification ->
          let range =
            if is_type_annotation source_name then
              type_annotation_name_range source_name span
            else
              match qualification with
            | Some (_, _, _, member_range) -> member_range
            | None -> span
          in
          let method_name = source_symbol_basename source_name in
          let identity =
            match
              match qualification with
              | Some (qualifier, _, _, _) ->
                  (match
                     method_identity_at analysis offset ~protocol_name:qualifier
                       method_name
                   with
                  | Some _ as identity -> identity
                  | None ->
                      ocaml_alias_member_identity_at analysis qualifier
                        method_name)
              | None -> (
                  match source_symbol_role_at analysis offset with
                  | Some Module_name ->
                      module_identity_at analysis offset source_name
                  | Some (Protocol_name protocol_name) ->
                      protocol_identity_at analysis protocol_name
                  | Some (Protocol_method protocol_name) ->
                      method_identity_at analysis offset ~protocol_name method_name
                  | None -> (
                      match protocol_identity_at analysis source_name with
                      | Some _ as identity -> identity
                      | None -> method_identity_at analysis offset method_name))
            with
            | Some _ as identity -> identity
            | None -> (
                match member_identity_at analysis offset source_name with
                | Some _ as identity -> identity
                | None -> (
                    match module_identity_at analysis offset source_name with
                    | Some _ as identity -> identity
                    | None -> module_type_identity_at analysis offset source_name))
          in
          Option.map (fun identity -> { identity; range }) identity))
  | Some { desc = Keyword source_name; span; _ }
    when String.length source_name > 1 ->
      let field_name = String.sub source_name 1 (String.length source_name - 1) in
      label_identity_at analysis offset field_name
      |> Option.map (fun identity ->
             { identity;
               range = { span with start_offset = span.start_offset + 1 } })
  | _ -> None

let semantic_identity_at analysis offset =
  semantic_occurrence_at analysis offset
  |> Option.map (fun occurrence -> occurrence.identity)

let path_of_file_uri uri =
  if String.starts_with ~prefix:"file://" uri then
    String.sub uri 7 (String.length uri - 7)
  else uri

let rec find_repo_root_opt directory =
  if Sys.file_exists (Filename.concat directory "dune-project") then
    Some directory
  else
    let parent = Filename.dirname directory in
    if String.equal parent directory then None else find_repo_root_opt parent

let existing_absolute_relative_file root filename =
  let candidate = Filename.concat root filename in
  if Sys.file_exists candidate then Some candidate else None

let ocaml_standard_library_file filename =
  if Filename.is_relative filename then
    existing_absolute_relative_file Config.standard_library filename
  else None

let normalize_definition_location_for_filename context_filename location =
  let filename = location.Location.loc_start.Lexing.pos_fname in
  if
    String.equal filename ""
    || Filename.is_relative filename = false
    || String.starts_with ~prefix:"file://" filename
  then location
  else
    match
      context_filename |> path_of_file_uri |> Filename.dirname |> find_repo_root_opt
    with
    | None -> location
    | Some root ->
        let absolute =
          match existing_absolute_relative_file root filename with
          | Some path -> path
          | None -> (
              match ocaml_standard_library_file filename with
              | Some path -> path
              | None -> Filename.concat root filename)
        in
        let update_position position =
          { position with Lexing.pos_fname = absolute }
        in
        {
          location with
          Location.loc_start = update_position location.loc_start;
          loc_end = update_position location.loc_end;
        }

let normalize_definition_location analysis location =
  normalize_definition_location_for_filename analysis.filename location

let source_line_starts source =
  let starts = ref [ 0 ] in
  String.iteri
    (fun index char ->
      if char = '\n' then starts := (index + 1) :: !starts)
    source;
  !starts |> List.rev |> Array.of_list

let source_position filename line_starts offset =
  let rec search low high =
    if low > high then max 0 (low - 1)
    else
      let middle = (low + high) / 2 in
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

let source_location filename source (span : Ast.source_span) =
  let line_starts = source_line_starts source in
  {
    Location.loc_start =
      source_position filename line_starts span.start_offset;
    loc_end = source_position filename line_starts span.end_offset;
    loc_ghost = false;
  }

let source_definition_cache = Hashtbl.create 64

let source_definition_location_lexical path source name =
  let find_substring_from text pattern offset =
    let pattern_length = String.length pattern in
    let text_length = String.length text in
    let limit = text_length - pattern_length in
    let rec loop index =
      if index > limit then None
      else if String.sub text index pattern_length = pattern then Some index
      else loop (index + 1)
    in
    if pattern_length = 0 || offset > limit then None else loop offset
  in
  [ "(defn "; "(defn- "; "(def "; "(defonce "; "(defmacro " ]
  |> List.find_map (fun prefix ->
         match find_substring_from source (prefix ^ name) 0 with
         | None -> None
         | Some start ->
             let name_start = start + String.length prefix in
             let name_end = name_start + String.length name in
             Some
               (source_location path source
                  { start_offset = name_start; end_offset = name_end }))

let source_definition_location path source name =
  let cache_key = (path, Digest.to_hex (Digest.string source), name) in
  match Hashtbl.find_opt source_definition_cache cache_key with
  | Some location -> location
  | None ->
      let location =
        source_definition_location_lexical path source name
      in
      Hashtbl.add source_definition_cache cache_key location;
      location

let constructor_definition_cache = Hashtbl.create 64

let constructor_definition_location_lexical path source name =
  let line_starts = source_line_starts source in
  let source_length = String.length source in
  let line_end start =
    match String.index_from_opt source start '\n' with
    | Some index -> index
    | None -> source_length
  in
  let is_constructor_delimiter = function
    | ' ' | '\t' | '\r' | '\n' | '|' | ')' | ';' -> true
    | _ -> false
  in
  let rec find_line index =
    if index >= Array.length line_starts then None
    else
      let start = line_starts.(index) in
      let limit = line_end start in
      let rec skip_spaces offset =
        if offset < limit && (source.[offset] = ' ' || source.[offset] = '\t')
        then skip_spaces (offset + 1)
        else offset
      in
      let offset = skip_spaces start in
      let constructor_start =
        if offset < limit && source.[offset] = '|' then
          Some (skip_spaces (offset + 1))
        else
          match String.index_from_opt source offset '=' with
          | Some equals when equals < limit -> Some (skip_spaces (equals + 1))
          | Some _ | None -> None
      in
      match constructor_start with
      | None -> find_line (index + 1)
      | Some offset ->
          let name_end = offset + String.length name in
          if
            name_end <= limit
            && String.sub source offset (String.length name) = name
            && (name_end = limit || is_constructor_delimiter source.[name_end])
          then
            Some
              (source_location path source
                 { start_offset = offset; end_offset = name_end })
          else find_line (index + 1)
  in
  find_line 0

let constructor_definition_location path source name =
  let cache_key = (path, Digest.to_hex (Digest.string source), name) in
  match Hashtbl.find_opt constructor_definition_cache cache_key with
  | Some location -> location
  | None ->
      let location =
        constructor_definition_location_lexical path source name
      in
      Hashtbl.add constructor_definition_cache cache_key location;
      location

let module_source_cache = Hashtbl.create 32

let source_basename_of_module_name name =
  let buffer = Buffer.create (String.length name + 8) in
  String.iteri
    (fun index char ->
      if
        index > 0
        && char >= 'A'
        && char <= 'Z'
        && Buffer.length buffer > 0
        && Buffer.nth buffer (Buffer.length buffer - 1) <> '_'
      then Buffer.add_char buffer '_';
      Buffer.add_char buffer (Char.lowercase_ascii char))
    name;
  Buffer.contents buffer

let source_roots_for_filename filename =
  [
    Some (Filename.dirname (path_of_file_uri filename));
    Some (Sys.getcwd ());
    Some (Filename.dirname Sys.executable_name);
  ]
  |> List.filter_map (function
       | None -> None
       | Some path -> find_repo_root_opt path)
  |> List.sort_uniq String.compare

let source_files_for_module filename module_path =
  let module_name =
    match List.rev (String.split_on_char '.' module_path) with
    | name :: _ -> name
    | [] -> module_path
  in
  let basename = source_basename_of_module_name module_name in
  let cache_key = (source_roots_for_filename filename, basename) in
  match Hashtbl.find_opt module_source_cache cache_key with
  | Some paths -> paths
  | None ->
      let target_names = [ basename ^ ".mli"; basename ^ ".ml" ] in
      let skip_dir name =
        name = "_build" || name = "_opam" || name = "node_modules"
        || name = ".git" || String.starts_with ~prefix:"." name
      in
      let rec scan acc dir =
        match Sys.readdir dir with
        | exception Sys_error _ -> acc
        | entries ->
            Array.fold_left
              (fun acc entry ->
                if skip_dir entry then acc
                else
                  let path = Filename.concat dir entry in
                  match (Sys.is_directory path, List.mem entry target_names) with
                  | true, _ -> scan acc path
                  | false, true -> path :: acc
                  | false, false -> acc
                  | exception Sys_error _ -> acc)
              acc entries
      in
      let paths =
        source_roots_for_filename filename
        |> List.fold_left scan []
        |> List.sort_uniq String.compare
        |> List.sort (fun left right ->
             match (Filename.check_suffix left ".mli", Filename.check_suffix right ".mli") with
             | true, false -> -1
             | false, true -> 1
             | _ -> String.compare left right)
      in
      Hashtbl.add module_source_cache cache_key paths;
      paths

let included_module_paths source =
  let words =
    source
    |> String.map (function '(' | ')' | '\n' | '\r' | '\t' -> ' ' | char -> char)
    |> String.split_on_char ' '
    |> List.filter (( <> ) "")
  in
  let rec collect acc = function
    | "include" :: "module" :: "type" :: "of" :: module_name :: rest
    | "include" :: module_name :: rest ->
        collect (module_name :: acc) rest
    | _ :: rest -> collect acc rest
    | [] -> List.rev acc
  in
  collect [] words

let rec external_constructor_source_location ?(visited = []) ~filename module_path
    constructor_name =
  if List.mem module_path visited then None
  else
    let visited = module_path :: visited in
    source_files_for_module filename module_path
    |> List.find_map (fun path ->
           let source = In_channel.with_open_bin path In_channel.input_all in
           match constructor_definition_location path source constructor_name with
           | Some _ as location -> location
           | None ->
               included_module_paths source
               |> List.find_map (fun included ->
                      external_constructor_source_location ~visited ~filename
                        included constructor_name))

let stdlib_source_candidates_for_filename filename relative =
  let unique_paths paths =
    let seen = Hashtbl.create 8 in
    paths
    |> List.filter (fun path ->
           if Hashtbl.mem seen path then false
           else (
             Hashtbl.add seen path ();
             true))
  in
  let roots =
    [
      Some (Filename.dirname (path_of_file_uri filename));
      Some (Sys.getcwd ());
      Some (Filename.dirname Sys.executable_name);
    ]
    |> List.filter_map (function
         | None -> None
         | Some path -> find_repo_root_opt path)
    |> unique_paths
  in
  roots
  |> List.concat_map (fun root ->
         [
           Filename.concat root relative;
           Filename.concat root (Filename.concat "duniverse/lg" relative);
         ])

let stdlib_source_candidates analysis relative =
  stdlib_source_candidates_for_filename analysis.filename relative

let stdlib_core_definition_location analysis source_name =
  let name = source_symbol_basename source_name in
  stdlib_source_candidates analysis "stdlib/clojure/core.cljc"
  |> List.find_map (fun path ->
         if Sys.file_exists path then
           let source = In_channel.with_open_bin path In_channel.input_all in
           source_definition_location path source name
         else None)

let stdlib_core_definition_location_for_filename filename source_name =
  let name = source_symbol_basename source_name in
  stdlib_source_candidates_for_filename filename "stdlib/clojure/core.cljc"
  |> List.find_map (fun path ->
         if Sys.file_exists path then
           let source = In_channel.with_open_bin path In_channel.input_all in
           source_definition_location path source name
         else None)

let paren_depth_delta line =
  let delta = ref 0 in
  String.iter
    (function
      | '(' -> incr delta
      | ')' -> decr delta
      | _ -> ())
    line;
  !delta

let stdlib_core_signature_for_filename filename source_name =
  let name = source_symbol_basename source_name in
  let marker = "(signature clojure.core/" ^ name in
  let signature_from_source source =
    let lines = String.split_on_char '\n' source in
    let signature_line_matches line =
      let line = String.trim line in
      let marker_length = String.length marker in
      String.starts_with ~prefix:marker line
      && (String.length line = marker_length
         ||
         (String.length line > marker_length
         &&
         match line.[marker_length] with
         | ' ' | '\t' | '\r' | '\n' | ')' -> true
         | _ -> false))
    in
    let rec find = function
      | [] -> None
      | line :: rest ->
          if signature_line_matches line then
            let rec collect depth collected = function
              | [] -> Some (String.concat "\n" (List.rev collected))
              | line :: rest ->
                  let depth = depth + paren_depth_delta line in
                  let collected = line :: collected in
                  if depth <= 0 then
                    Some (String.concat "\n" (List.rev collected))
                  else collect depth collected rest
            in
            let depth = paren_depth_delta line in
            if depth <= 0 then Some line else collect depth [ line ] rest
          else find rest
    in
    find lines
  in
  stdlib_source_candidates_for_filename filename "stdlib/clojure/core.lgi"
  |> List.find_map (fun path ->
         if Sys.file_exists path then
           let source = In_channel.with_open_bin path In_channel.input_all in
           signature_from_source source
         else None)

let require_alias_target_location analysis alias =
  let contains_alias child =
    match child.Ast.form with
    | FSymbol candidate when String.equal candidate alias -> true
    | _ -> false
  in
  let rec alias_in_spec namespace_span = function
    | { Ast.form = Ast.FKeyword (":as" | "as") | FSymbol (":as" | "as"); _ }
      :: alias_form :: _ when contains_alias alias_form ->
        Some (source_location analysis.filename analysis.source namespace_span)
    | _ :: rest -> alias_in_spec namespace_span rest
    | [] -> None
  in
  let require_spec form =
    match (form.Ast.form, form.children) with
    | FVector (FSymbol _ :: _),
      ({ Ast.form = FSymbol _; span = namespace_span; _ } :: rest) ->
        alias_in_spec namespace_span rest
    | _ -> None
  in
  let clause_is_require = function
    | { Ast.form =
          FList
            ((FKeyword "require" | FKeyword ":require" | FSymbol ":require"
             | FSymbol "require")
             :: _);
        _ } ->
        true
    | _ -> false
  in
  let rec find_require_spec form =
    match require_spec form with
    | Some _ as location -> location
    | None -> List.find_map find_require_spec form.Ast.children
  in
  let find form =
    match form.Ast.form with
    | FList (FSymbol "ns" :: _namespace :: _) ->
        form.children
        |> List.filter clause_is_require
        |> List.find_map find_require_spec
    | FList (FSymbol "require" :: _) -> find_require_spec form
    | _ -> None
  in
  List.find_map find analysis.forms

let definition analysis ~offset =
  match semantic_occurrence_at analysis offset with
  | Some { identity; _ }
    when not identity.definition_location.Location.loc_ghost ->
      Some (normalize_definition_location analysis identity.definition_location)
  | Some occurrence ->
      (match token_at analysis offset with
      | Some ({ desc = Symbol source_name; _ } as token) -> (
          match qualified_symbol_parts token source_name with
          | Some (qualifier, qualifier_range, _, _)
            when offset < qualifier_range.end_offset -> (
              match require_alias_target_location analysis qualifier with
              | Some _ as location -> location
              | None ->
                  stdlib_core_definition_location analysis
                    (String.sub analysis.source occurrence.range.start_offset
                       (occurrence.range.end_offset
                      - occurrence.range.start_offset)))
          | Some _ | None
            when is_core_symbol_candidate source_name ->
              stdlib_core_definition_location analysis
                (String.sub analysis.source occurrence.range.start_offset
                   (occurrence.range.end_offset - occurrence.range.start_offset))
          | Some _ | None -> None)
      | Some _ | None -> None)
  | None -> (
      match token_at analysis offset with
      | Some ({ desc = Symbol source_name; _ } as token) -> (
          match qualified_symbol_parts token source_name with
          | Some (qualifier, qualifier_range, _, _)
            when offset < qualifier_range.end_offset ->
              require_alias_target_location analysis qualifier
          | Some _ | None
            when is_core_symbol_candidate source_name ->
              stdlib_core_definition_location analysis source_name
          | Some _ | None -> None)
      | Some _ | None -> None)

let compare_span (left : Ast.source_span) (right : Ast.source_span) =
  Int.compare left.start_offset right.start_offset

let semantic_occurrences_for_token analysis (token : Ast.token) =
  let offsets =
    match token.desc with
    | Symbol source_name -> (
        match qualified_symbol_parts token source_name with
        | Some (_, qualifier_range, _, member_range) ->
            [ qualifier_range.start_offset; member_range.start_offset ]
        | None -> [ token.span.start_offset ])
    | Keyword _ -> [ token.span.start_offset ]
    | _ -> []
  in
  offsets
  |> List.filter_map (semantic_occurrence_at analysis)
  |> List.sort_uniq (fun left right ->
         let range_order = compare_span left.range right.range in
         if range_order <> 0 then range_order
         else compare_semantic_key left.identity.key right.identity.key)

let source_symbol_references analysis source_name =
  let target = source_symbol_basename source_name in
  analysis.tokens
  |> List.filter_map (fun (token : Ast.token) ->
         match token.desc with
         | Symbol candidate
           when String.equal (source_symbol_basename candidate) target ->
             Some token.span
         | _ -> None)
  |> List.sort_uniq compare_span

let source_token_at source offset =
  match Lexer.tokenize source with
  | Error _ -> None
  | Ok tokens ->
      List.find_opt
        (fun (token : Ast.token) ->
          token.span.start_offset <= offset && offset < token.span.end_offset)
        tokens

let source_fallback_definition ~filename ~source ~offset =
  match source_token_at source offset with
  | Some ({ desc = Symbol source_name; _ } as token) -> (
      match qualified_symbol_parts token source_name with
      | Some (_, _, _, _) when not (is_core_symbol_candidate source_name) ->
          None
      | Some _ | None ->
          stdlib_core_definition_location_for_filename filename source_name)
  | Some _ | None -> None

type source_require_alias = {
  namespace : string;
  alias : string option;
  namespace_span : Ast.source_span;
  alias_span : Ast.source_span option;
}

let source_require_aliases forms =
  let rec alias_target = function
    | { Ast.form = Ast.FKeyword (":as" | "as") | FSymbol (":as" | "as"); _ }
      :: { form = FSymbol alias; span; _ }
      :: _ ->
        Some (alias, span)
    | _ :: rest -> alias_target rest
    | [] -> None
  in
  let rec require_spec form =
    match (form.Ast.form, form.children) with
    | FVector (FSymbol namespace :: _),
      ({ Ast.form = FSymbol namespace_symbol; span = namespace_span; _ } :: rest)
      when String.equal namespace namespace_symbol ->
        let alias, alias_span =
          match alias_target rest with
          | Some (alias, span) -> (Some alias, Some span)
          | None -> (None, None)
        in
        [
          {
            namespace;
            alias;
            namespace_span;
            alias_span;
          };
        ]
    | _ ->
        form.children |> List.concat_map require_spec
  in
  let clause_is_require = function
    | { Ast.form =
          FList
            ((FKeyword "require" | FKeyword ":require" | FSymbol ":require"
             | FSymbol "require")
             :: _);
        _ } ->
        true
    | _ -> false
  in
  let source_form form =
    match form.Ast.form with
    | FList (FSymbol "ns" :: _namespace :: _) ->
        form.children
        |> List.filter clause_is_require
        |> List.concat_map require_spec
    | FList (FSymbol "require" :: _) -> require_spec form
    | _ -> []
  in
  forms |> List.concat_map source_form

let source_quick_definition ~filename ~state ~source ~offset =
  let contains (span : Ast.source_span) =
    span.start_offset <= offset && offset < span.end_offset
  in
  match Lexer.tokenize source with
  | Error _ -> source_fallback_definition ~filename ~source ~offset
  | Ok tokens -> (
      let token =
        List.find_opt
          (fun (token : Ast.token) ->
            token.span.start_offset <= offset && offset < token.span.end_offset)
          tokens
      in
      match
        Parser.parse_located ~eof_offset:(String.length source) tokens
      with
      | Error _ -> source_fallback_definition ~filename ~source ~offset
      | Ok forms -> (
          let aliases = source_require_aliases forms in
          let alias_target alias =
            aliases
            |> List.find_opt (fun item ->
                   match item.alias with
                   | Some candidate -> String.equal candidate alias
                   | None -> String.equal item.namespace alias)
          in
          let require_token_target () =
            aliases
            |> List.find_map (fun item ->
                   if contains item.namespace_span then
                     Some
                       (source_location filename source item.namespace_span)
                   else
                     match item.alias_span with
                     | Some span when contains span ->
                         Some
                           (source_location filename source item.namespace_span)
                     | Some _ | None -> None)
          in
          match token with
          | Some ({ desc = Symbol source_name; _ } as token) -> (
              match require_token_target () with
              | Some _ as location -> location
              | None -> (
                  match qualified_symbol_parts token source_name with
                  | Some (qualifier, qualifier_range, member, member_range) -> (
                      match alias_target qualifier with
                      | Some alias when contains qualifier_range ->
                          Some
                            (source_location filename source alias.namespace_span)
                      | Some alias when contains member_range ->
                          let module_path =
                            ocaml_module_path_of_namespace alias.namespace
                          in
                          let value_path =
                            module_path ^ "." ^ Names.ocaml_member_name member
                          in
                          let env = Compiler.state_environment state in
                          (match value_location_by_ocaml_path env value_path with
                          | Some location ->
                              Some
                                (normalize_definition_location_for_filename
                                   filename location)
                          | None ->
                              let constructor_path = module_path ^ "." ^ member in
                              (match
                                 constructor_location_by_ocaml_path env
                                   constructor_path
                               with
                              | Some location ->
                                  Some
                                    (normalize_definition_location_for_filename
                                       filename location)
                              | None ->
                                  external_constructor_source_location ~filename
                                    module_path
                                    member))
                      | None
                        when contains member_range
                             && is_ocaml_module_path qualifier ->
                          let module_path = qualifier in
                          let value_path =
                            module_path ^ "." ^ Names.ocaml_member_name member
                          in
                          let env = Compiler.state_environment state in
                          (match value_location_by_ocaml_path env value_path with
                          | Some location ->
                              Some
                                (normalize_definition_location_for_filename
                                   filename location)
                          | None ->
                              let constructor_path = module_path ^ "." ^ member in
                              (match
                                 constructor_location_by_ocaml_path env
                                   constructor_path
                               with
                              | Some location ->
                                  Some
                                    (normalize_definition_location_for_filename
                                       filename location)
                              | None ->
                                  external_constructor_source_location ~filename
                                    module_path member))
                      | Some _ | None ->
                          if is_core_symbol_candidate source_name then
                            stdlib_core_definition_location_for_filename filename
                              source_name
                          else None)
                  | None ->
                      if is_core_symbol_candidate source_name then
                        stdlib_core_definition_location_for_filename filename
                          source_name
                      else None))
          | Some _ | None -> source_fallback_definition ~filename ~source ~offset))

let core_value_hover ~filename env source_name range =
  let basename = source_symbol_basename source_name in
  match stdlib_core_signature_for_filename filename basename with
  | Some signature -> Some { contents = signature; range }
  | None ->
      let candidates =
        [
          Names.ocaml_binding_name "clojure.core" basename;
          Names.ocaml_binding_name "cljs.core" basename;
          "Clojure.Core." ^ Names.ocaml_member_name basename;
          "Cljs.Core." ^ Names.ocaml_member_name basename;
        ]
      in
      candidates
      |> List.find_map (fun path ->
             value_hover_by_ocaml_path env basename range path)

let source_name_of_ocaml_member name =
  let bang_suffix = "_bang" in
  let name =
    if String.ends_with ~suffix:bang_suffix name then
      String.sub name 0 (String.length name - String.length bang_suffix) ^ "!"
    else name
  in
  String.map (function '_' -> '-' | char -> char) name

let source_signature_name_before line marker =
  let marker_length = String.length marker in
  let line_length = String.length line in
  let rec find index =
    if marker_length = 0 || index + marker_length > line_length then None
    else if
      String.sub line index marker_length |> String.equal marker
    then Some index
    else find (index + 1)
  in
  match find 0 with
  | None -> None
  | Some index ->
      let name = String.sub line 0 index |> String.trim in
      if String.equal name "" then None else Some name

let module_signature_completions prefix line =
  let line = String.trim line in
  let prefixed kind detail =
    let kind_length = String.length kind in
    if not (String.starts_with ~prefix:kind line) then None
    else
      let rest =
        String.sub line kind_length (String.length line - kind_length)
        |> String.trim
      in
      rest
      |> source_signature_name_before " "
      |> Option.map (fun label -> ({ label; detail } : completion_item))
  in
  let value_completion () =
    let val_prefix = "val " in
    if String.starts_with ~prefix:val_prefix line then
      match String.index_opt line ':' with
      | Some separator ->
          let ocaml_name =
            String.sub line (String.length val_prefix)
              (separator - String.length val_prefix)
            |> String.trim
          in
          let label = source_name_of_ocaml_member ocaml_name in
          let detail =
            String.sub line (separator + 1)
              (String.length line - separator - 1)
            |> String.trim
          in
          Some ({ label; detail } : completion_item)
      | None -> None
    else None
  in
  let type_completion () =
    let type_prefix = "type " in
    if String.starts_with ~prefix:type_prefix line then
      let rest =
        String.sub line (String.length type_prefix)
          (String.length line - String.length type_prefix)
        |> String.trim
      in
      let declaration =
        match String.index_opt rest '=' with
        | Some index -> String.sub rest 0 index
        | None -> rest
        |> String.trim
      in
      let parts =
        declaration |> String.split_on_char ' '
        |> List.filter (fun part -> not (String.equal part ""))
      in
      match List.rev parts with
      | label :: _ -> Some ({ label; detail = "type" } : completion_item)
      | [] -> None
    else None
  in
  let constructor_completions () =
    let marker_completions marker =
      let marker_length = String.length marker in
      let line_length = String.length line in
      let rec loop offset completions =
        if offset + marker_length > line_length then completions
        else if
          String.sub line offset marker_length |> String.equal marker
        then
          let rest =
            String.sub line (offset + marker_length)
              (line_length - offset - marker_length)
            |> String.trim
          in
          let label_end =
            match String.index_opt rest ' ' with
            | Some index -> index
            | None -> String.length rest
          in
          let completions =
            if label_end = 0 then completions
            else
              let label = String.sub rest 0 label_end in
              match label.[0] with
              | 'A' .. 'Z'
                when String.starts_with ~prefix label ->
                  ({ label; detail = "constructor" } : completion_item)
                  :: completions
              | _ -> completions
          in
          loop (offset + marker_length) completions
        else loop (offset + 1) completions
      in
      loop 0 []
    in
    marker_completions "| " @ marker_completions "= "
  in
  let singleton (item : completion_item option) =
    match item with
    | Some item when String.starts_with ~prefix item.label -> [ item ]
    | Some _ | None -> []
  in
  singleton (value_completion ())
  @ constructor_completions ()
  @ singleton (type_completion ())
  @ singleton (prefixed "module " "module")

let module_value_completions env module_path prefix =
  match Env.find_module_by_name (longident_of_dotted_name module_path) env with
  | _, declaration -> (
      let printed =
        Printtyp.wrap_printing_env ~error:false env (fun () ->
            Format.asprintf "%a" Printtyp.modtype declaration.md_type)
      in
      printed |> String.split_on_char '\n'
      |> List.concat_map (module_signature_completions prefix)
      |> List.sort_uniq (fun (left : completion_item) right ->
             String.compare left.label right.label))
  | exception Not_found -> []

let source_quick_completions ~state ~source ~offset =
  let prefix_token token =
    match token.Ast.desc with
    | Symbol source_name
      when token.span.start_offset <= offset && offset <= token.span.end_offset ->
        let typed_prefix_length = max 0 (offset - token.span.start_offset) in
        Some
          (String.sub source_name 0
             (min typed_prefix_length (String.length source_name)))
    | _ -> None
  in
  match Lexer.tokenize source with
  | Error _ -> []
  | Ok tokens -> (
      match List.find_map prefix_token tokens with
      | None -> []
      | Some prefix -> (
          match String.rindex_opt prefix '/' with
          | None -> []
          | Some separator ->
              let qualifier = String.sub prefix 0 separator in
              let member_prefix =
                String.sub prefix (separator + 1)
                  (String.length prefix - separator - 1)
              in
              match Parser.parse_located ~eof_offset:(String.length source) tokens with
              | Error _ -> []
              | Ok forms ->
                  source_require_aliases forms
                  |> List.find_map (fun item ->
                         let matches_alias =
                           match item.alias with
                           | Some alias -> String.equal alias qualifier
                           | None -> String.equal item.namespace qualifier
                         in
                         if matches_alias then
                           let module_path =
                             ocaml_module_path_of_namespace item.namespace
                           in
                           Some
                             (module_value_completions
                                (Compiler.state_environment state)
                                module_path member_prefix)
                         else None)
                  |> Option.value ~default:[]))

let source_quick_hover ~state ~source ~offset =
  let contains (span : Ast.source_span) =
    span.start_offset <= offset && offset < span.end_offset
  in
  match Lexer.tokenize source with
  | Error _ -> None
  | Ok tokens -> (
      let token =
        List.find_opt
          (fun (token : Ast.token) ->
            token.span.start_offset <= offset && offset < token.span.end_offset)
          tokens
      in
      match
        Parser.parse_located ~eof_offset:(String.length source) tokens
      with
      | Error _ -> None
      | Ok forms -> (
          let aliases = source_require_aliases forms in
          let alias_target alias =
            aliases
            |> List.find_opt (fun item ->
                   match item.alias with
                   | Some candidate -> String.equal candidate alias
                   | None -> String.equal item.namespace alias)
          in
          match token with
          | Some ({ desc = Symbol source_name; _ } as token) -> (
              let env = Compiler.state_environment state in
              match qualified_symbol_parts token source_name with
              | Some (qualifier, qualifier_range, member, member_range) -> (
                  match alias_target qualifier with
                  | Some alias when contains qualifier_range ->
                      Some
                        {
                          contents = "module " ^ alias.namespace;
                          range = qualifier_range;
                        }
                  | Some alias when contains member_range ->
                      let module_path =
                        ocaml_module_path_of_namespace alias.namespace
                      in
                      let value_path =
                        module_path ^ "." ^ Names.ocaml_member_name member
                      in
                      (match
                         value_hover_by_ocaml_path env member member_range
                           value_path
                       with
                      | Some _ as hover -> hover
                      | None ->
                          constructor_hover_by_ocaml_path env member
                            member_range (module_path ^ "." ^ member))
                  | None
                    when contains member_range && is_ocaml_module_path qualifier ->
                      let module_path = qualifier in
                      let value_path =
                        module_path ^ "." ^ Names.ocaml_member_name member
                      in
                      (match
                         value_hover_by_ocaml_path env member member_range
                           value_path
                       with
                      | Some _ as hover -> hover
                      | None ->
                          constructor_hover_by_ocaml_path env member
                            member_range (module_path ^ "." ^ member))
                  | Some _ | None ->
                      if is_core_symbol_candidate source_name then
                        core_value_hover
                          ~filename:(Filename.concat (Sys.getcwd ()) "source.cljc")
                          env source_name token.span
                      else None)
              | None ->
                  if is_core_symbol_candidate source_name then
                    core_value_hover
                      ~filename:(Filename.concat (Sys.getcwd ()) "source.cljc")
                      env source_name token.span
                  else None)
          | Some _ | None -> None))

let source_fallback_references ~source ~offset =
  match source_token_at source offset with
  | Some { desc = Symbol source_name; _ }
    when is_core_symbol_candidate source_name ->
      let target = source_symbol_basename source_name in
      (match Lexer.tokenize source with
      | Error _ -> []
      | Ok tokens ->
          tokens
          |> List.filter_map (fun (token : Ast.token) ->
                 match token.desc with
                 | Symbol candidate
                   when is_core_symbol_candidate candidate
                        && String.equal (source_symbol_basename candidate) target
                   ->
                     Some token.span
                 | _ -> None)
          |> List.sort_uniq compare_span)
  | Some _ | None -> []

let references analysis ~offset =
  match semantic_identity_at analysis offset with
  | None -> (
      match token_at analysis offset with
      | Some { desc = Symbol source_name; _ }
        when is_core_symbol_candidate source_name
             && Option.is_some
               (stdlib_core_definition_location analysis source_name) ->
          source_symbol_references analysis source_name
      | Some _ | None -> [])
  | Some target ->
      analysis.tokens
      |> List.concat_map (semantic_occurrences_for_token analysis)
      |> List.filter_map (fun occurrence ->
             if equal_semantic_key occurrence.identity.key target.key then
               Some occurrence.range
             else None)
      |> List.sort_uniq compare_span

let semantic_uid_at analysis ~offset =
  Option.bind (semantic_identity_at analysis offset) (fun identity ->
         match identity.key with Ocaml_uid uid -> Some uid | _ -> None)

let semantic_key_at analysis ~offset =
  semantic_identity_at analysis offset |> Option.map (fun identity -> identity.key)

let print_module_type env module_type =
  Printtyp.wrap_printing_env ~error:false env (fun () ->
      Format.asprintf "%a" Printtyp.modtype module_type)

let print_type_declaration env id declaration =
  Printtyp.wrap_printing_env ~error:false env (fun () ->
      Format.asprintf "%a" (Printtyp.type_declaration id) declaration)

let uid_equal left right = Typedtree.Uid.compare left right = 0

let ocaml_semantic_hover analysis uid source_name =
  let contents = ref None in
  let set value = if Option.is_none !contents then contents := Some value in
  let set_type env name ty = set (name ^ " : " ^ print_type env ty) in
  let source_name = source_symbol_basename source_name in
  let final_env = analysis.compiler.typed_structure.str_final_env in
  let base = Tast_iterator.default_iterator in
  let visit_pattern : type kind.
      Tast_iterator.iterator -> kind Typedtree.general_pattern -> unit =
   fun self pattern ->
    (match pattern.pat_desc with
    | Tpat_var (_, name, pattern_uid)
    | Tpat_alias (_, _, name, pattern_uid, _)
      when uid_equal uid pattern_uid ->
        set_type pattern.pat_env name.txt pattern.pat_type
    | Tpat_construct (_, description, _, _)
      when uid_equal uid description.cstr_uid ->
        set ("constructor " ^ source_name)
    | Tpat_record (fields, _) ->
        fields
        |> List.iter (fun (_, (description : Data_types.label_description), _) ->
               if uid_equal uid description.lbl_uid then
                 set_type pattern.pat_env description.lbl_name description.lbl_arg)
    | _ -> ());
    base.pat self pattern
  in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          (match expression.Typedtree.exp_desc with
          | Texp_ident (_, _, description) when uid_equal uid description.val_uid ->
              set_type expression.exp_env source_name expression.exp_type
          | Texp_construct (_, description, _)
            when uid_equal uid description.cstr_uid ->
              set ("constructor " ^ source_name)
          | Texp_record { fields; _ } ->
              Array.iter
                (fun ((description : Data_types.label_description), _) ->
                  if uid_equal uid description.lbl_uid then
                    set_type expression.exp_env description.lbl_name
                      description.lbl_arg)
                fields
          | Texp_field (_, _, description)
          | Texp_atomic_loc (_, _, description)
            when uid_equal uid description.lbl_uid ->
              set_type expression.exp_env description.lbl_name description.lbl_arg
          | Texp_setfield (_, _, description, _)
            when uid_equal uid description.lbl_uid ->
              set_type expression.exp_env description.lbl_name description.lbl_arg
          | _ -> ());
          base.expr self expression);
      pat = visit_pattern;
      type_declaration =
        (fun self declaration ->
          if uid_equal uid declaration.Typedtree.typ_type.type_uid then
            set
              (print_type_declaration final_env declaration.typ_id
                 declaration.typ_type);
          (match declaration.typ_kind with
          | Ttype_variant constructors ->
              List.iter
                (fun (constructor : Typedtree.constructor_declaration) ->
                  if uid_equal uid constructor.cd_uid then
                    set ("constructor " ^ constructor.cd_name.txt))
                constructors
          | Ttype_record fields ->
              List.iter
                (fun (field : Typedtree.label_declaration) ->
                  if uid_equal uid field.ld_uid then
                    set_type field.ld_type.ctyp_env field.ld_name.txt
                      field.ld_type.ctyp_type)
                fields
          | _ -> ());
          base.type_declaration self declaration);
      module_expr =
        (fun self module_expression ->
          (match module_expression.Typedtree.mod_desc with
          | Tmod_ident (path, _) ->
              let declaration = Env.find_module path module_expression.mod_env in
              if
                uid_equal uid
                  (Lg_compiler_support.Ocaml_module.uid declaration)
              then
                set
                  ("module " ^ source_name ^ " : "
                 ^ print_module_type module_expression.mod_env declaration.md_type)
          | Tmod_functor
              ( Typedtree.Named (Some id, parameter_name, parameter_type),
                body ) ->
              let declaration = Env.find_module (Path.Pident id) body.mod_env in
              if
                uid_equal uid
                  (Lg_compiler_support.Ocaml_module.uid declaration)
              then
                set
                 ("module " ^ Option.value parameter_name.txt ~default:source_name
                 ^ " : "
                 ^ print_module_type parameter_type.mty_env parameter_type.mty_type)
          | _ -> ());
          base.module_expr self module_expression);
      module_binding =
        (fun self binding ->
          if uid_equal uid binding.Typedtree.mb_uid then
            set
              ("module " ^ source_name ^ " : "
             ^ print_module_type binding.mb_expr.mod_env binding.mb_expr.mod_type);
          base.module_binding self binding);
      module_type =
        (fun self module_type ->
          (match module_type.Typedtree.mty_desc with
          | Tmty_ident (path, _) ->
              let declaration = Env.find_modtype path module_type.mty_env in
              if
                uid_equal uid
                  (Lg_compiler_support.Ocaml_module.type_uid declaration)
              then
                set
                  ("module type " ^ source_name ^ " = "
                 ^ Option.fold ~none:"_"
                     ~some:(print_module_type module_type.mty_env)
                     declaration.mtd_type)
          | _ -> ());
          base.module_type self module_type);
      module_type_declaration =
        (fun self declaration ->
          if uid_equal uid declaration.Typedtree.mtd_uid then
            set
              ("module type " ^ source_name ^ " = "
             ^ Option.fold ~none:"_"
                 ~some:(fun module_type ->
                   print_module_type module_type.Typedtree.mty_env
                     module_type.mty_type)
                 declaration.mtd_type);
          base.module_type_declaration self declaration);
    }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  !contents

let protocol_semantic_hover analysis protocol_id =
  let registry = protocol_registry analysis in
  match Protocol_registry.find_protocol protocol_id registry with
  | Some _ -> Some ("protocol " ^ Protocol_id.to_string protocol_id)
  | None -> None

let method_semantic_hover analysis method_id =
  Protocol_registry.declarations (protocol_registry analysis)
  |> List.find_map (fun (_, (declaration : Protocol_registry.declaration)) ->
         Protocol_registry.Method_map.find_opt method_id declaration.methods
         |> Option.map (fun (signature : Protocol_registry.method_signature) ->
                Method_id.name method_id ^ " : "
                ^ Types.ocaml_name signature.method_ty))

let semantic_hover analysis occurrence source_name =
  let contents =
    match occurrence.identity.key with
    | Ocaml_uid uid -> ocaml_semantic_hover analysis uid source_name
    | Protocol_key protocol_id -> protocol_semantic_hover analysis protocol_id
    | Method_key method_id -> method_semantic_hover analysis method_id
  in
  Option.map
    (fun contents -> { contents; range = occurrence.range })
    contents

let hover analysis ~offset =
  match token_at analysis offset with
  | Some ({ desc = Symbol source_name; span } : Ast.token) -> (
      match
        if is_core_symbol_candidate source_name then
          stdlib_core_signature_for_filename analysis.filename source_name
          |> Option.map (fun contents -> { contents; range = span })
        else None
      with
      | Some _ as hover -> hover
      | None -> (
      match semantic_occurrence_at analysis offset with
      | Some occurrence -> (
          let occurrence_name =
            String.sub analysis.source occurrence.range.start_offset
              (occurrence.range.end_offset - occurrence.range.start_offset)
          in
          match semantic_hover analysis occurrence occurrence_name with
          | Some _ as hover -> hover
          | None -> expression_hover analysis ~offset)
      | None -> expression_hover analysis ~offset))
  | _ -> expression_hover analysis ~offset

let signature_call_at analysis offset =
  let contains (span : Ast.source_span) =
    span.start_offset <= offset && offset <= span.end_offset
  in
  let rec collect candidates (located : Ast.located_form) =
    let candidates = List.fold_left collect candidates located.children in
    match located.children with
    | ({ form = FSymbol _; _ } as head) :: arguments
      when contains located.span && head.span.end_offset <= offset ->
        (located.span, head, arguments) :: candidates
    | _ -> candidates
  in
  analysis.forms |> List.fold_left collect []
  |> List.sort (fun ((left : Ast.source_span), _, _)
                      ((right : Ast.source_span), _, _) ->
         Int.compare
           (left.end_offset - left.start_offset)
           (right.end_offset - right.start_offset))
  |> List.find_map (fun (_, (head : Ast.located_form), arguments) ->
         match
           smallest_expression analysis.compiler.typed_structure
             head.span.start_offset (fun expression ->
               match expression.Typedtree.exp_desc with
               | Texp_ident _ -> true
               | _ -> false)
         with
         | Some expression ->
             let parameters, return_type =
               Lg_compiler_support.Ocaml_type.arrow_parts expression.exp_type
             in
             if parameters = [] then None
             else Some (head, arguments, expression.exp_env, parameters, return_type)
         | None -> None)

let signature_help analysis ~offset =
  Option.map
    (fun ((head : Ast.located_form), arguments, env, parameters, return_type) ->
      let function_name =
        String.sub analysis.source head.span.start_offset
          (head.span.end_offset - head.span.start_offset)
      in
      let parameter_types = List.map (print_type env) parameters in
      let return_type = print_type env return_type in
      let function_type =
        String.concat " -> " (parameter_types @ [ return_type ])
      in
      let completed_arguments =
        List.fold_left
          (fun count (argument : Ast.located_form) ->
            if argument.span.end_offset < offset then count + 1 else count)
          0 arguments
      in
      { label = function_name ^ " : " ^ function_type;
        parameters = parameter_types;
        active_parameter =
          min completed_arguments (max 0 (List.length parameters - 1)) })
    (signature_call_at analysis offset)

let references_to_key analysis key =
  analysis.tokens
  |> List.concat_map (semantic_occurrences_for_token analysis)
  |> List.filter_map (fun occurrence ->
         if equal_semantic_key occurrence.identity.key key then Some occurrence.range
         else None)
  |> List.sort_uniq compare_span

let references_to_uid analysis uid = references_to_key analysis (Ocaml_uid uid)

let valid_rename_name name =
  match Lexer.tokenize name with
  | Ok [ { desc = Symbol parsed; span } ] ->
      parsed = name && span.start_offset = 0 && span.end_offset = String.length name
  | _ -> false

let rename analysis ~offset ~new_name =
  if not (valid_rename_name new_name) then Error.error ~code:Error_code.Invalid_form "invalid rename target"
  else
    match references analysis ~offset with
    | [] -> Error.error ~code:Error_code.Semantic "symbol cannot be renamed"
    | ranges -> Ok (List.map (fun range -> { range; new_text = new_name }) ranges)

let prepare_rename analysis ~offset =
  semantic_occurrence_at analysis offset
  |> Option.map (fun occurrence -> occurrence.range)

let symbol_kind = function
  | "defn" | "defn-" -> Some `Function
  | "def" | "defonce" -> Some `Variable
  | "module" | "module-alias" | "module-apply" | "module-functor" ->
      Some `Module
  | "module-signature" -> Some `Interface
  | "type-alias" | "type-record" | "type-variant" -> Some `Type
  | "defprotocol" -> Some `Interface
  | _ -> None

let leaf_symbol kind (located : Ast.located_form) =
  match (located.form, located.children) with
  | FSymbol name, _ ->
      Some
        { name;
          detail = None;
          kind;
          range = located.span;
          selection_range = located.span;
          children = [] }
  | _, { form = FSymbol name; span = selection_range; _ } :: _ ->
      Some
        { name;
          detail = None;
          kind;
          range = located.span;
          selection_range;
          children = [] }
  | _ -> None

let signature_item_symbol (located : Ast.located_form) =
  match located.children with
  | { form = FSymbol head; _ }
    :: { form = FSymbol name; span = selection_range; _ }
    :: _ ->
      let kind =
        match head with
        | "val" -> Some `Variable
        | "type" -> Some `Type
        | "module" -> Some `Module
        | _ -> None
      in
      Option.map
        (fun kind ->
          { name;
            detail = None;
            kind;
            range = located.span;
            selection_range;
            children = [] })
        kind
  | _ -> None

let rec child_symbols head rest =
  match head with
  | "module" | "module-functor" -> List.concat_map symbols_of_form rest
  | "type-record" -> List.filter_map (leaf_symbol `Field) rest
  | "type-variant" -> List.filter_map (leaf_symbol `Constructor) rest
  | "defprotocol" -> List.filter_map (leaf_symbol `Method) rest
  | "module-signature" -> List.filter_map signature_item_symbol rest
  | _ -> []

and symbols_of_form (located : Ast.located_form) =
  match located.children with
  | { form = FSymbol head; _ } :: ({ form = FSymbol name; span = selection_range; _ } as _name)
    :: rest -> (
      match symbol_kind head with
      | None -> []
      | Some kind ->
          let children = child_symbols head rest in
          [
            {
              name;
              detail = None;
              kind;
              range = located.span;
              selection_range;
              children;
            };
          ])
  | _ -> []

let document_symbols analysis = List.concat_map symbols_of_form analysis.forms

let semantic_kind_of_symbol_kind : symbol_kind -> semantic_token_kind = function
  | `Module -> `Namespace
  | `Function -> `Function
  | `Variable -> `Variable
  | `Type -> `Type
  | `Interface -> `Interface
  | `Method -> `Method
  | `Field -> `Property
  | `Constructor -> `Enum_member

let rec document_symbol_selections symbols =
  List.concat_map
    (fun (symbol : document_symbol) ->
      (symbol.selection_range, semantic_kind_of_symbol_kind symbol.kind)
      :: document_symbol_selections symbol.children)
    symbols

let special_form_names =
  [ "def";
    "defonce";
    "defn";
    "defn-";
    "fn";
    "let";
    "if";
    "and";
    "or";
    "do";
    "match";
    "try";
    "catch";
    "raise";
    "require";
    "module";
    "module-alias";
    "module-functor";
    "module-apply";
    "module-signature";
    "type-alias";
    "type-record";
    "type-variant";
    "defprotocol";
    "extend-type";
    "open";
    "include";
    "val";
    "type" ]

let rec special_form_spans (located : Ast.located_form) =
  let nested = List.concat_map special_form_spans located.children in
  match located.children with
  | { form = FSymbol name; span; _ } :: _
    when List.mem name special_form_names ->
      span :: nested
  | _ -> nested

let same_semantic_key key = function
  | Some identity -> equal_semantic_key key identity.key
  | None -> false

let function_parameter_uids analysis =
  let uids = ref [] in
  let pattern_base = Tast_iterator.default_iterator in
  let pattern_iterator =
    { pattern_base with
      pat =
        (fun (type kind) self (pattern : kind Typedtree.general_pattern) ->
          (match pattern.pat_desc with
          | Tpat_var (_, _, uid) -> uids := uid :: !uids
          | Tpat_alias (_, _, _, uid, _) -> uids := uid :: !uids
          | _ -> ());
          pattern_base.pat self pattern) }
  in
  let collect_pattern pattern = pattern_iterator.pat pattern_iterator pattern in
  let base = Tast_iterator.default_iterator in
  let iterator =
    { base with
      expr =
        (fun self expression ->
          (match expression.Typedtree.exp_desc with
          | Texp_function (parameters, _) ->
              List.iter
                (fun parameter ->
                  match parameter.Typedtree.fp_kind with
                  | Tparam_pat pattern -> collect_pattern pattern
                  | Tparam_optional_default (pattern, _) ->
                      collect_pattern pattern)
                parameters
          | _ -> ());
          base.expr self expression) }
  in
  iterator.structure iterator analysis.compiler.typed_structure;
  !uids

let semantic_kind_for_occurrence analysis declarations parameter_uids occurrence
    source_name =
  match
    List.find_opt
      (fun (range, _) -> range = occurrence.range)
      declarations
  with
  | Some (_, kind) -> kind
  | None -> (
      match occurrence.identity.key with
      | Protocol_key _ -> `Interface
      | Method_key _ -> `Method
      | Ocaml_uid uid as key ->
          let offset = occurrence.range.start_offset in
          if List.exists (uid_equal uid) parameter_uids then `Parameter
          else if same_semantic_key key (module_identity_at analysis offset source_name)
          then `Namespace
          else if
            same_semantic_key key
              (module_type_identity_at analysis offset source_name)
          then `Interface
          else if same_semantic_key key (type_identity_at analysis offset source_name)
          then `Type
          else if
            same_semantic_key key
              (constructor_identity_at analysis offset source_name)
          then `Enum_member
          else if same_semantic_key key (label_identity_at analysis offset source_name)
          then `Property
          else
            match ocaml_semantic_hover analysis uid source_name with
            | Some detail when String.contains detail '>' -> `Function
            | Some _ | None -> `Variable)

let semantic_tokens analysis =
  let declarations =
    document_symbols analysis |> document_symbol_selections
  in
  let special_forms =
    analysis.forms |> List.concat_map special_form_spans
  in
  let parameter_uids = function_parameter_uids analysis in
  let token_semantics (token : Ast.token) =
    match token.desc with
    | String _ | Regex _ | Char _ -> [ { range = token.span; kind = `String } ]
    | Int _ | Float _ | Decimal _ -> [ { range = token.span; kind = `Number } ]
    | Keyword _ | Bool _ -> [ { range = token.span; kind = `Keyword } ]
    | Symbol _ ->
        let occurrences = semantic_occurrences_for_token analysis token in
        if occurrences = [] then
          [ { range = token.span;
              kind =
                if List.mem token.span special_forms then `Keyword else `Variable } ]
        else
          List.map
            (fun occurrence ->
              let occurrence_name =
                String.sub analysis.source occurrence.range.start_offset
                  (occurrence.range.end_offset - occurrence.range.start_offset)
              in
              { range = occurrence.range;
                kind =
                  semantic_kind_for_occurrence analysis declarations parameter_uids
                    occurrence occurrence_name })
            occurrences
    | Lparen | Anon_lparen | Rparen | Lbracket | Rbracket | Lbrace
    | Set_lbrace | Rbrace | Quote | Syntax_quote | Unquote
    | Unquote_splicing | Deref | Var_quote _ -> []
  in
  analysis.tokens |> List.concat_map token_semantics
  |> List.sort (fun (left : semantic_token) (right : semantic_token) ->
         compare_span left.range right.range)

let completion_source_names analysis =
  analysis.compiler.typecheck_state.env
  |> Compiler_environment.filter_map (fun key (binding : Types.binding) ->
         if String.starts_with ~prefix:"__" key then None
         else Some (binding.ocaml_name, key))

let completions_from_state ?prefix ?limit state : completion_item list =
  Compiler_session.run (fun () ->
      let scope = Toolchain.source_scope state in
      let label key =
        match String.rindex_opt key '/' with
        | Some index
          when String.equal (String.sub key 0 index) scope
               && index + 1 < String.length key ->
            String.sub key (index + 1) (String.length key - index - 1)
        | Some _ | None -> key
      in
      let matches_prefix label =
        match prefix with
        | None -> true
        | Some prefix -> String.starts_with ~prefix label
      in
      let limit = Option.value limit ~default:max_int in
      let count = ref 0 in
      state.Toolchain.typecheck_state.env
      |> Compiler_environment.filter_map
           (fun key (binding : Types.binding) ->
             if !count >= limit || String.starts_with ~prefix:"__" key then None
             else
               let label = label key in
               if not (matches_prefix label) then None
               else (
                 incr count;
                 let binding = Types.instantiate_binding binding in
                 let ty =
                   Types.runtime_root_value_type binding
                   |> Option.value ~default:binding.ty
                 in
                 Some { label; detail = Types.source_name ty }))
      |> List.sort_uniq
           (fun (left : completion_item) (right : completion_item) ->
             String.compare left.label right.label))

let completion_field_source_names analysis =
  analysis.compiler.typecheck_state.env
  |> Compiler_environment.filter_map (fun _ (binding : Types.binding) ->
         match binding.ty with
         | TNamed_record record ->
             Some
               (List.map
                  (fun (field : Types.field) ->
                    ( field.ocaml_name,
                      String.sub field.keyword 1 (String.length field.keyword - 1) ))
                  record.fields)
         | _ -> None)
  |> List.concat

let qualified_completion_label owner name = String.concat "." (owner @ [ name ])

let type_completion_label type_id =
  qualified_completion_label (Type_id.owner type_id) (Type_id.name type_id)

let type_completion_detail = function
  | Type_registry.Alias -> "type alias"
  | Record -> "record type"
  | Variant -> "variant type"
  | Opaque -> "opaque foreign type"

let completions analysis ~offset : completion_item list =
  let env =
    match
      smallest_expression analysis.compiler.typed_structure offset (fun _ -> true)
    with
    | Some expression -> expression.exp_env
    | None -> analysis.compiler.compiler_env
  in
  let source_names = completion_source_names analysis in
  let source_label name =
    source_names |> List.assoc_opt name |> Option.value ~default:name
  in
  let values =
    Env.fold_values
      (fun name _path description items ->
        if String.starts_with ~prefix:"__" name then items
        else
          {
            label = source_label name;
            detail = print_type env description.val_type;
          }
          :: items)
      None env []
  in
  let constructors =
    Env.fold_constructors
      (fun description items ->
        let constructor_types =
          description.Data_types.cstr_args @ [ description.cstr_res ]
        in
        {
          label = source_label description.cstr_name;
          detail =
            constructor_types
            |> List.map (print_type env)
            |> String.concat " -> ";
        }
        :: items)
      None env values
  in
  let field_source_names = completion_field_source_names analysis in
  let labels =
    Env.fold_labels
      (fun description items ->
        let label =
          field_source_names
          |> List.assoc_opt description.Data_types.lbl_name
          |> Option.value ~default:description.lbl_name
        in
        { label; detail = print_type env description.lbl_arg } :: items)
      None env constructors
  in
  let types =
    analysis.compiler.typecheck_state.env
    |> Compiler_environment.types |> Type_registry.bindings
    |> List.fold_left
         (fun items (emitted_name, (declaration : Type_registry.declaration)) ->
           match
             Env.find_type_by_name (longident_of_dotted_name emitted_name) env
           with
           | _ ->
               { label = type_completion_label declaration.type_id;
                 detail = type_completion_detail declaration.kind }
               :: items
           | exception Not_found -> items)
         labels
  in
  let modules =
    let source_modules =
      analysis.compiler.typecheck_state.env |> Compiler_environment.modules
      |> Module_registry.module_bindings
      |> List.map (fun (emitted_name, declaration) ->
             ( emitted_name,
               qualified_completion_label
                 (Module_id.owner declaration.Module_registry.module_id)
                 (Module_id.name declaration.module_id) ))
    in
    Env.fold_modules
      (fun name _path _declaration items ->
        let label =
          source_modules |> List.assoc_opt name |> Option.value ~default:name
        in
        { label; detail = "module" } :: items)
      None env types
  in
  let source_signatures =
    analysis.compiler.typecheck_state.env |> Compiler_environment.modules
    |> Module_registry.signature_bindings
    |> List.map (fun (emitted_name, signature_id) ->
           ( emitted_name,
             qualified_completion_label (Signature_id.owner signature_id)
               (Signature_id.name signature_id) ))
  in
  let module_types =
    Env.fold_modtypes
      (fun name _path _declaration items ->
        let label =
          source_signatures |> List.assoc_opt name |> Option.value ~default:name
        in
        { label; detail = "module signature" } :: items)
      None env modules
  in
  Protocol_registry.declarations (protocol_registry analysis)
  |> List.fold_left
       (fun items (protocol_id, (declaration : Protocol_registry.declaration)) ->
         let protocol_name = Protocol_id.to_string protocol_id in
         let items = { label = protocol_name; detail = "protocol" } :: items in
         Protocol_registry.Method_map.fold
           (fun method_id _signature items ->
             let method_name = Method_id.name method_id in
             { label = protocol_name ^ "/" ^ method_name;
               detail = "protocol method" }
             :: { label = method_name; detail = "protocol method" }
             :: items)
           declaration.methods items)
       module_types
  |> List.sort_uniq (fun (left : completion_item) (right : completion_item) ->
         String.compare left.label right.label)

let repl_completions ?prefix ?limit state : completion_item list =
  completions_from_state ?prefix ?limit state

module String_map = Map.Make (String)
module String_set = Set.Make (String)

type workspace_index = {
  sources : string String_map.t;
  analyses : t String_map.t;
  errors : Error.t String_map.t;
  components : String_set.t list;
}

type workspace_symbol_kind =
  | Value_symbol
  | Namespace_symbol
  | Module_symbol
  | Module_type_symbol
  | Type_symbol
  | Constructor_symbol
  | Protocol_symbol
  | Method_symbol

module Workspace_symbol = struct
  type t = workspace_symbol_kind * string

  let compare = Stdlib.compare
end

module Workspace_symbol_set = Set.Make (Workspace_symbol)
module Workspace_symbol_map = Map.Make (Workspace_symbol)

let workspace_symbol_name (kind, name) =
  match kind with Type_symbol -> Names.sanitize_name name | _ -> name

let namespace_scoped_symbol = function
  | Value_symbol | Type_symbol | Constructor_symbol | Protocol_symbol
  | Method_symbol ->
      true
  | Namespace_symbol | Module_symbol | Module_type_symbol -> false

let namespace_qualified_name namespace kind name =
  let name = workspace_symbol_name (kind, name) in
  match namespace with
  | Some namespace when namespace_scoped_symbol kind -> namespace ^ "/" ^ name
  | _ -> name

let workspace_symbol ?namespace kind name =
  (kind, namespace_qualified_name namespace kind name)

let source_namespace forms =
  List.find_map
    (function
      | Ast.FList (FSymbol "ns" :: FSymbol namespace_name :: _) ->
          Some namespace_name
      | _ -> None)
    forms

let provided_symbols source =
  let open Ast in
  match Lexer.tokenize source with
  | Error _ -> Workspace_symbol_set.empty
  | Ok tokens -> (
      match Parser.parse tokens with
      | Error _ -> Workspace_symbol_set.empty
      | Ok forms ->
          let namespace = source_namespace forms in
          let add kind name symbols =
            Workspace_symbol_set.add (workspace_symbol ?namespace kind name)
              symbols
          in
          List.fold_left
            (fun symbols -> function
              | FList (FSymbol "ns" :: FSymbol namespace_name :: _) ->
                  Workspace_symbol_set.add
                    (workspace_symbol Namespace_symbol namespace_name)
                    symbols
              | FList
                  (FSymbol ("module-alias" | "module-apply")
                  :: FSymbol name :: _) ->
                  add Module_symbol name symbols
              | FList
                  (FSymbol "type-variant" :: FSymbol name :: constructors) ->
                  List.fold_left
                    (fun symbols -> function
                      | FSymbol constructor
                      | FList (FSymbol constructor :: _) ->
                          add Constructor_symbol constructor symbols
                      | _ -> symbols)
                    (add Type_symbol name symbols)
                    constructors
              | FList
                  (FSymbol ("module" | "module-functor") :: FSymbol name :: _) ->
                  add Module_symbol name symbols
              | FList (FSymbol "module-signature" :: FSymbol name :: _) ->
                  add Module_type_symbol name symbols
              | FList
                  (FSymbol ("def" | "defonce" | "defn" | "defn-")
                  :: FSymbol name :: _) ->
                  add Value_symbol name symbols
              | FList
                  (FSymbol ("type-alias" | "type-record") :: FSymbol name :: _) ->
                  add Type_symbol name symbols
              | FList (FSymbol "defprotocol" :: FSymbol protocol_name :: methods) ->
                  List.fold_left
                    (fun symbols -> function
                      | FList (FSymbol method_name :: _) ->
                          add Method_symbol method_name symbols
                      | _ -> symbols)
                    (add Protocol_symbol protocol_name symbols)
                    methods
              | _ -> symbols)
            Workspace_symbol_set.empty forms)

let pattern_names form =
  let rec collect names = function
    | Ast.FSymbol name when not (String.starts_with ~prefix:"^:" name) ->
        String_set.add name names
    | FVector forms | FList forms -> List.fold_left collect names forms
    | _ -> names
  in
  collect String_set.empty form

let add_type_name_reference add name references =
  match String.index_opt name '.' with
  | Some separator ->
      add Module_symbol (String.sub name 0 separator) references
  | None -> add Type_symbol name references

let rec add_type_references add ty references =
  match ty with
  | Types.TPoly_variant row -> List.fold_left (fun refs ty -> add_type_references add ty refs) references (List.filter_map snd row.tags)
  | Types.TOcaml name -> add_type_name_reference add name references
  | TOcaml_app (name, arguments) ->
      let references =
        if String.contains name '.' then
          add_type_name_reference add name references
        else references
      in
      List.fold_left
        (fun references argument -> add_type_references add argument references)
        references arguments
  | TConstraint constraint_ ->
      List.fold_left
        (fun references argument -> add_type_references add argument references)
        references (Types.constraint_children constraint_)
  | TTuple arguments ->
      List.fold_left
        (fun references argument -> add_type_references add argument references)
        references arguments
  | TArray inner | TRef inner | TList inner | TVector inner | TSet inner
  | TSeq inner ->
      add_type_references add inner references
  | TFn (arguments, return_type) ->
      List.fold_left
        (fun references argument -> add_type_references add argument references)
        (add_type_references add return_type references)
        arguments
  | TOverloaded_fn arities ->
      List.fold_left
        (fun references (arity : Types.fn_arity) ->
          let references =
            List.fold_left
              (fun references argument ->
                add_type_references add argument references)
              references arity.fixed_params
          in
          let references =
            match arity.rest_param with
            | None -> references
            | Some rest -> add_type_references add rest references
          in
          add_type_references add arity.return_ty references)
        references arities
  | TRecord fields | TNamed_record { fields; _ } ->
      List.fold_left
        (fun references (field : Types.field) ->
          add_type_references add field.ty references)
        references fields
  | TNullable inner -> add_type_references add inner references
  | TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
  | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ ->
      references

let add_type_annotation_references add source references =
  let keyword =
    if String.starts_with ~prefix:"^:" source then
      ":" ^ String.sub source 2 (String.length source - 2)
    else source
  in
  let references =
    let name =
      if String.starts_with ~prefix:":" keyword then
        String.sub keyword 1 (String.length keyword - 1)
      else keyword
    in
    match String.index_opt name '.' with
    | Some separator ->
        add Module_symbol (String.sub name 0 separator) references
    | None -> (
        match String.index_opt name '/' with
        | Some separator ->
            add Module_symbol (String.sub name 0 separator) references
        | None -> references)
  in
  match Type_annotation.of_keyword keyword with
  | Error _ -> references
  | Ok ty -> add_type_references add ty references

let rec declaration_type_references add references = function
  | Ast.FSymbol annotation when String.starts_with ~prefix:"^:" annotation ->
      add_type_annotation_references add annotation references
  | FKeyword annotation ->
      add_type_annotation_references add annotation references
  | FVector forms | FList forms ->
      List.fold_left (declaration_type_references add) references forms
  | FSymbol _ | FBool _ | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _
  | FRegex _
  | FMap _ | FCoreSymbol _ ->
      references

let namespace_require_keyword = function
  | Ast.FKeyword "require" | FKeyword ":require" | FSymbol ":require"
  | FSymbol "require" ->
      true
  | _ -> false

let namespace_require_reference add references = function
  | Ast.FVector (FSymbol namespace_name :: _)
  | FList (FSymbol namespace_name :: _) ->
      add Namespace_symbol namespace_name references
  | FSymbol namespace_name -> add Namespace_symbol namespace_name references
  | _ -> references

let namespace_clause_references add references = function
  | Ast.FList (keyword :: specs) when namespace_require_keyword keyword ->
      List.fold_left (namespace_require_reference add) references specs
  | _ -> references

let namespace_references add references clauses =
  List.fold_left (namespace_clause_references add) references clauses

let find_substring_from text pattern offset =
  let pattern_length = String.length pattern in
  let text_length = String.length text in
  let limit = text_length - pattern_length in
  let rec loop index =
    if index > limit then None
    else if String.sub text index pattern_length = pattern then Some index
    else loop (index + 1)
  in
  if pattern_length = 0 || offset > limit then None else loop offset

let namespace_token_char = function
  | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '-' | '_' | '.' -> true
  | _ -> false

let skip_whitespace text offset =
  let length = String.length text in
  let rec loop index =
    if index >= length then index
    else
      match text.[index] with
      | ' ' | '\n' | '\r' | '\t' | ',' -> loop (index + 1)
      | _ -> index
  in
  loop offset

let source_require_namespace_references add source references =
  let length = String.length source in
  let rec token_end index =
    if index < length && namespace_token_char source.[index] then
      token_end (index + 1)
    else index
  in
  let rec vectors limit offset references =
    match find_substring_from source "[" offset with
    | None -> references
    | Some vector_start when vector_start >= limit -> references
    | Some vector_start ->
        let start = skip_whitespace source (vector_start + 1) in
        let stop = token_end start in
        let references =
          if stop > start then
            let namespace_name = String.sub source start (stop - start) in
            if String.contains namespace_name '.' then
              add Namespace_symbol namespace_name references
            else references
          else references
        in
        vectors limit stop references
  in
  let rec requires offset references =
    match find_substring_from source ":require" offset with
    | None -> references
    | Some require_start ->
        let next = require_start + String.length ":require" in
        let limit =
          find_substring_from source "\n\n" next |> Option.value ~default:length
        in
        requires next (vectors limit next references)
  in
  requires 0 references

let add_symbol_references bound name references =
  let add kind name references =
    Workspace_symbol_set.add (workspace_symbol kind name) references
  in
  if String_set.mem name bound then references
  else if String.starts_with ~prefix:"^:" name then
    add_type_annotation_references add name references
  else
    match String.rindex_opt name '/' with
    | Some separator ->
        let qualifier = String.sub name 0 separator in
        let root =
          match String.index_opt qualifier '/' with
          | None -> qualifier
          | Some index -> String.sub qualifier 0 index
        in
        references |> add Module_symbol root |> add Protocol_symbol qualifier
    | None -> (
        match String.index_opt name '.' with
        | Some separator ->
            add Module_symbol (String.sub name 0 separator) references
        | None ->
            references |> add Value_symbol name |> add Type_symbol name
            |> add Constructor_symbol name |> add Method_symbol name)

let rec pattern_references bound references = function
  | Ast.FSymbol name when String.starts_with ~prefix:"^:" name ->
      add_symbol_references bound name references
  | FKeyword annotation ->
      let add kind name references =
        Workspace_symbol_set.add (workspace_symbol kind name) references
      in
      add_type_annotation_references add annotation references
  | FVector forms | FList forms ->
      List.fold_left (pattern_references bound) references forms
  | _ -> references

let referenced_symbols source =
  let open Ast in
  let current_namespace = ref None in
  let add kind name references =
    Workspace_symbol_set.add
      (workspace_symbol ?namespace:!current_namespace kind name)
      references
  in
  let rec forms bound references = function
    | [] -> references
    | form :: rest -> forms bound (form_references bound references form) rest
  and method_references bound references = function
    | FList (FSymbol _ :: params :: body) ->
        let references = pattern_references bound references params in
        let bound = String_set.union bound (pattern_names params) in
        forms bound references body
    | _ -> references
  and function_clause_references bound references = function
    | FList (params :: body) ->
        let references = pattern_references bound references params in
        let bound = String_set.union bound (pattern_names params) in
        forms bound references body
    | _ -> references
  and form_references bound references = function
    | FSymbol name -> add_symbol_references bound name references
    | FList (FSymbol "ns" :: _namespace :: clauses) ->
        namespace_references add references clauses
    | FList (FSymbol "require" :: specs) ->
        List.fold_left (namespace_require_reference add) references specs
    | FList
        (FSymbol ("defn" | "defn-") :: FSymbol _
        :: ((FList _) :: _ as clauses)) ->
        List.fold_left
          (function_clause_references bound)
          references clauses
    | FList (FSymbol ("defn" | "defn-") :: FSymbol _ :: params :: body) ->
        let references = pattern_references bound references params in
        let bound = String_set.union bound (pattern_names params) in
        forms bound references body
    | FList [ FSymbol ("def" | "defonce"); FSymbol _; value ] ->
        form_references bound references value
    | FList (FSymbol "fn" :: params :: body) ->
        let references = pattern_references bound references params in
        let bound = String_set.union bound (pattern_names params) in
        forms bound references body
    | FList (FSymbol "let" :: FVector bindings :: body) ->
        let rec bindings_references bound references = function
          | pattern :: value :: rest ->
              let references = form_references bound references value in
              let references = pattern_references bound references pattern in
              let bound = String_set.union bound (pattern_names pattern) in
              bindings_references bound references rest
          | [] -> (bound, references)
          | [ form ] -> (bound, form_references bound references form)
        in
        let bound, references = bindings_references bound references bindings in
        forms bound references body
    | FList [ FSymbol "module-alias"; FSymbol _; FSymbol target ] ->
        Workspace_symbol_set.add (workspace_symbol Module_symbol target) references
    | FList (FSymbol "module-apply" :: FSymbol _ :: FSymbol functor_name :: args) ->
        List.fold_left
          (fun references -> function
            | FSymbol name ->
                Workspace_symbol_set.add (workspace_symbol Module_symbol name)
                  references
            | _ -> references)
          (Workspace_symbol_set.add
             (workspace_symbol Module_symbol functor_name)
             references)
          args
    | FList (FSymbol "module" :: FSymbol _ :: FSymbol signature :: body) ->
        forms bound
          (Workspace_symbol_set.add
             (workspace_symbol Module_type_symbol signature)
             references)
          body
    | FList (FSymbol "module" :: FSymbol _ :: body) ->
        forms bound references body
    | FList
        (FSymbol ("type-alias" | "type-record" | "type-variant" | "defprotocol")
        :: declaration) ->
        List.fold_left (declaration_type_references add) references declaration
    | FList (FSymbol "extend-type" :: receiver :: FSymbol protocol :: methods) ->
        let references =
          Workspace_symbol_set.add (workspace_symbol Protocol_symbol protocol)
            references
        in
        let references =
          match receiver with
          | FSymbol name ->
              Workspace_symbol_set.add (workspace_symbol Type_symbol name) references
          | _ -> references
        in
        List.fold_left (method_references bound) references methods
    | FList list | FVector list -> forms bound references list
    | FMap entries ->
        List.fold_left
          (fun references (key, value) ->
            form_references bound (form_references bound references key) value)
          references entries
    | FBool _ | FInt _ | FFloat _ | FDecimal _ | FChar _ | FString _ | FRegex _
    | FKeyword _
    | FCoreSymbol _ ->
        references
  in
  match Lexer.tokenize source with
  | Error _ -> Workspace_symbol_set.empty
  | Ok tokens -> (
      match Parser.parse tokens with
      | Error _ -> Workspace_symbol_set.empty
      | Ok parsed ->
          current_namespace := source_namespace parsed;
          forms String_set.empty Workspace_symbol_set.empty parsed
          |> source_require_namespace_references add source)

let workspace_providers sources =
  String_map.fold
    (fun filename source providers ->
      match providers with
      | Error _ as err -> err
      | Ok providers ->
          Workspace_symbol_set.fold
            (fun symbol providers ->
              match providers with
              | Error _ as err -> err
              | Ok providers -> (
                  let existing =
                    Workspace_symbol_map.find_opt symbol providers
                    |> Option.value ~default:String_set.empty
                  in
                  Ok
                    (Workspace_symbol_map.add symbol
                       (String_set.add filename existing)
                       providers)))
            (provided_symbols source) (Ok providers))
    sources (Ok Workspace_symbol_map.empty)

let workspace_dependencies sources =
  match workspace_providers sources with
  | Error _ as err -> err
  | Ok providers ->
      Ok
        (String_map.mapi
           (fun filename source ->
             Workspace_symbol_set.fold
               (fun symbol dependencies ->
                 let providers =
                   Workspace_symbol_map.find_opt symbol providers
                   |> Option.value ~default:String_set.empty
                   |> String_set.remove filename
                 in
                 let providers =
                   match fst symbol with
                   | Namespace_symbol -> providers
                   | _ ->
                       if String_set.cardinal providers = 1 then providers
                       else String_set.empty
                 in
                 String_set.union providers dependencies)
               (referenced_symbols source)
               (String_map.fold (fun candidate _ dependencies ->
                  if candidate <> filename
                     && Ocaml_interface.source_stem candidate = Ocaml_interface.source_stem filename
                     && (Filename.check_suffix candidate ".mli" || Filename.check_suffix filename ".mli")
                  then String_set.add candidate dependencies else dependencies)
                  sources String_set.empty))
           sources)

let workspace_components sources =
  match workspace_dependencies sources with
  | Error _ as err -> err
  | Ok dependencies ->
      let adjacent filename =
        let direct =
          String_map.find_opt filename dependencies
          |> Option.value ~default:String_set.empty
        in
        String_map.fold
          (fun candidate candidate_dependencies adjacent ->
            if String_set.mem filename candidate_dependencies then
              String_set.add candidate adjacent
            else adjacent)
          dependencies direct
      in
      let rec component pending visited =
        match String_set.choose_opt pending with
        | None -> visited
        | Some filename ->
            let pending = String_set.remove filename pending in
            if String_set.mem filename visited then component pending visited
            else
              component
                (String_set.union pending (adjacent filename))
                (String_set.add filename visited)
      in
      let rec collect remaining components =
        match String_set.choose_opt remaining with
        | None -> List.rev components
        | Some filename ->
            let members =
              component (String_set.singleton filename) String_set.empty
            in
            collect (String_set.diff remaining members) (members :: components)
      in
      Ok
        (collect
           (String_map.to_seq sources |> Seq.map fst |> String_set.of_seq)
           [])

let dependency_closure dependencies filename =
  let rec visit pending visited =
    match String_set.choose_opt pending with
    | None -> visited
    | Some filename ->
        let pending = String_set.remove filename pending in
        if String_set.mem filename visited then visit pending visited
        else
          let direct =
            String_map.find_opt filename dependencies
            |> Option.value ~default:String_set.empty
          in
          visit (String_set.union pending direct) (String_set.add filename visited)
  in
  visit (String_set.singleton filename) String_set.empty

let topological_workspace_order dependencies filenames =
  let members = filenames in
  let rec visit filename (visiting, visited, ordered) =
    if String_set.mem filename visited then (visiting, visited, ordered)
    else if String_set.mem filename visiting then
      (visiting, String_set.add filename visited, filename :: ordered)
    else
      let direct =
        String_map.find_opt filename dependencies
        |> Option.value ~default:String_set.empty
        |> String_set.inter members
      in
      let visiting = String_set.add filename visiting in
      let visiting, visited, ordered =
        String_set.fold
          (fun dependency state -> visit dependency state)
          direct (visiting, visited, ordered)
      in
      ( String_set.remove filename visiting,
        String_set.add filename visited,
        filename :: ordered )
  in
  let _, _, ordered =
    String_set.fold
      (fun filename state -> visit filename state)
      filenames
      (String_set.empty, String_set.empty, [])
  in
  List.rev ordered

let source_stem = Ocaml_interface.source_stem

let source_unit_group sources filename =
  let stem = source_stem filename in
  String_map.to_seq sources
  |> Seq.map fst
  |> Seq.filter (fun candidate -> source_stem candidate = stem)
  |> String_set.of_seq

let analyze_component_from_state ?(target = Target.default) state sources filenames =
  let dependencies =
    workspace_dependencies sources |> Result.value ~default:String_map.empty
  in
  let component_sources =
    topological_workspace_order dependencies filenames
    |> List.map (fun filename -> (filename, String_map.find filename sources))
  in
  analyze_workspace_with_errors_from_state ~target state component_sources
  |> Result.map (fun (analyses, errors) ->
         ( List.fold_left
             (fun result (filename, analysis) ->
               String_map.add filename analysis result)
             String_map.empty analyses,
           List.fold_left
             (fun result (filename, error) ->
               String_map.add filename error result)
            String_map.empty errors ))

let analyze_component sources filenames =
  analyze_component_from_state Toolchain.empty_state sources filenames

let create_workspace_index_from_state ?(target = Target.default) state source_list =
  let sources =
    List.fold_left
      (fun sources (filename, source) -> String_map.add filename source sources)
      String_map.empty source_list
  in
  match workspace_components sources with
  | Error _ as err -> err
  | Ok components ->
      let dependencies =
        workspace_dependencies sources |> Result.value ~default:String_map.empty
      in
      let analyze_individually component analyses errors =
        String_set.fold
          (fun filename (analyses, errors) ->
            let closure = dependency_closure dependencies filename in
            match analyze_component_from_state ~target state sources closure with
            | Ok (closure_analyses, closure_errors) -> (
                match String_map.find_opt filename closure_analyses with
                | Some analysis ->
                    ( String_map.add filename analysis analyses,
                      String_map.remove filename errors )
                | None -> (
                    match String_map.find_opt filename closure_errors with
                    | Some error -> (analyses, String_map.add filename error errors)
                    | None -> (analyses, errors)))
            | Error _ -> (
                match
                  analyze_from_state ~target ~filename state
                    (String_map.find filename sources)
                with
                | Ok analysis ->
                    ( String_map.add filename analysis analyses,
                      String_map.remove filename errors )
                | Error error -> (analyses, String_map.add filename error errors)))
          component (analyses, errors)
      in
  let rec analyze_all analyses errors = function
    | [] -> Ok { sources; analyses; errors; components }
    | component :: rest -> (
        match analyze_component_from_state ~target state sources component with
        | Error _ ->
            let analyses, errors =
              analyze_individually component analyses errors
            in
            analyze_all analyses errors rest
        | Ok (component_analyses, component_errors) ->
            let failed =
              String_map.to_seq component_errors |> Seq.map fst
              |> String_set.of_seq
            in
            let component_analyses, component_errors =
              analyze_individually failed component_analyses component_errors
            in
            analyze_all
              (String_map.union (fun _ _ updated -> Some updated) analyses
                 component_analyses)
              (String_map.union (fun _ _ updated -> Some updated) errors
                 component_errors)
              rest)
  in
  analyze_all String_map.empty String_map.empty components

let create_workspace_index source_list =
  create_workspace_index_from_state Toolchain.empty_state source_list

let create_unanalyzed_workspace_index source_list =
  let sources =
    List.fold_left
      (fun sources (filename, source) -> String_map.add filename source sources)
      String_map.empty source_list
  in
  { sources; analyses = String_map.empty; errors = String_map.empty; components = [] }

let workspace_analysis index filename =
  String_map.find_opt filename index.analyses

let workspace_error index filename = String_map.find_opt filename index.errors

let component_containing filename components =
  List.find_opt (String_set.mem filename) components
  |> Option.value ~default:(String_set.singleton filename)

let rebuild_workspace_components ?(target = Target.default) state index ~sources
    ~components ~affected_components ~invalidated ~reported =
  let analyses = String_set.fold String_map.remove invalidated index.analyses in
  let errors = String_set.fold String_map.remove invalidated index.errors in
  let dependencies =
    workspace_dependencies sources |> Result.value ~default:String_map.empty
  in
  let analyze_individually component analyses errors =
    String_set.fold
      (fun filename (analyses, errors) ->
        let closure = dependency_closure dependencies filename in
        match analyze_component_from_state ~target state sources closure with
        | Ok (closure_analyses, closure_errors) -> (
            match String_map.find_opt filename closure_analyses with
            | Some analysis ->
                ( String_map.add filename analysis analyses,
                  String_map.remove filename errors )
            | None -> (
                match String_map.find_opt filename closure_errors with
                | Some error -> (analyses, String_map.add filename error errors)
                | None -> (analyses, errors)))
        | Error _ -> (
            match
              analyze_from_state ~target ~filename state
                (String_map.find filename sources)
            with
            | Ok analysis ->
                ( String_map.add filename analysis analyses,
                  String_map.remove filename errors )
            | Error error -> (analyses, String_map.add filename error errors)))
      component (analyses, errors)
  in
  let rec rebuild analyses errors = function
    | [] ->
        Ok
          ( { sources; analyses; errors; components },
            String_set.elements reported )
    | component :: rest -> (
        match analyze_component_from_state ~target state sources component with
        | Error _ ->
            let analyses, errors =
              analyze_individually component analyses errors
            in
            rebuild analyses errors rest
        | Ok (component_analyses, component_errors) ->
            let failed =
              String_map.to_seq component_errors |> Seq.map fst
              |> String_set.of_seq
            in
            let component_analyses, component_errors =
              analyze_individually failed component_analyses component_errors
            in
            rebuild
              (String_map.union (fun _ _ updated -> Some updated) analyses
                 component_analyses)
              (String_map.union (fun _ _ updated -> Some updated) errors
                 component_errors)
              rest)
  in
  rebuild analyses errors affected_components

let update_workspace_index_from_state ?(target = Target.default) state index ~filename
    ~source =
  match String_map.find_opt filename index.sources with
  | Some previous when previous = source -> Ok (index, [])
  | _ ->
      let old_affected = component_containing filename index.components in
      let sources = String_map.add filename source index.sources in
      (match workspace_components sources with
      | Error _ as err -> err
      | Ok components ->
      let affected_components =
        List.filter
          (fun component ->
            not (String_set.is_empty (String_set.inter component old_affected)))
          components
      in
      let reanalyzed =
        List.fold_left String_set.union String_set.empty affected_components
      in
      rebuild_workspace_components ~target state index ~sources ~components
        ~affected_components ~invalidated:reanalyzed ~reported:reanalyzed)

let update_workspace_index index ~filename ~source =
  update_workspace_index_from_state Toolchain.empty_state index ~filename ~source

let update_workspace_current_file_from_state ?(target = Target.default) state index
    ~filename ~source =
  match String_map.find_opt filename index.sources with
  | Some previous
    when previous = source
         && (String_map.mem filename index.analyses
            || String_map.mem filename index.errors) ->
      Ok (index, [])
  | _ ->
      let sources = String_map.add filename source index.sources in
      let dependencies =
        workspace_dependencies sources |> Result.value ~default:String_map.empty
      in
      let unit_group = source_unit_group sources filename in
      let closure =
        String_set.fold
          (fun filename closure ->
            String_set.union closure (dependency_closure dependencies filename))
          unit_group unit_group
      in
      let analyses = String_map.remove filename index.analyses in
      let errors = String_map.remove filename index.errors in
      let update_with_error error =
        Ok
          ( {
              index with
              sources;
              analyses;
              errors = String_map.add filename error errors;
            },
            [ filename ] )
      in
      match analyze_component_from_state ~target state sources closure with
      | Ok (closure_analyses, closure_errors) -> (
          match String_map.find_opt filename closure_analyses with
          | Some analysis ->
              Ok
                ( {
                    index with
                    sources;
                    analyses = String_map.add filename analysis analyses;
                    errors;
                  },
                  [ filename ] )
          | None -> (
              match String_map.find_opt filename closure_errors with
              | Some error -> update_with_error error
              | None -> Ok ({ index with sources; analyses; errors }, [ filename ])))
      | Error _ -> (
          match
            analyze_from_state ~target ~filename state
              (String_map.find filename sources)
          with
          | Ok analysis ->
              Ok
                ( {
                    index with
                    sources;
                    analyses = String_map.add filename analysis analyses;
                    errors;
                  },
                  [ filename ] )
          | Error error -> update_with_error error)

let remove_workspace_file_from_state ?(target = Target.default) state index ~filename =
  if not (String_map.mem filename index.sources) then Ok (index, [])
  else
    let old_affected = component_containing filename index.components in
    let sources = String_map.remove filename index.sources in
    match workspace_components sources with
    | Error _ as err -> err
    | Ok components ->
        let remaining_affected = String_set.remove filename old_affected in
        let affected_components =
          List.filter
            (fun component ->
              not
                (String_set.is_empty
                   (String_set.inter component remaining_affected)))
            components
        in
        let reanalyzed =
          List.fold_left String_set.union String_set.empty affected_components
        in
        let invalidated = String_set.add filename reanalyzed in
        rebuild_workspace_components ~target state index ~sources ~components
          ~affected_components ~invalidated ~reported:invalidated

let remove_workspace_file index ~filename =
  remove_workspace_file_from_state Toolchain.empty_state index ~filename
