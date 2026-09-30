open Asttypes
open Parsetree
open Lowered

module String_map = Map.Make (String)
module String_set = Set.Make (String)

let parse_expression ~context source =
  let lexbuf = Lexing.from_string source in
  Location.init lexbuf context;
  try Ok (Parse.expression lexbuf)
  with exn ->
    Error.error ~code:Error_code.Interop
      ("generated OCaml expression did not parse in " ^ context ^ ": "
     ^ Printexc.to_string exn)

let loc = Location.none

let rec compact_longident = function
  | Longident.Lident name -> Longident.Lident (Names.compact_generated_name name)
  | Longident.Ldot (path, name) ->
      Longident.Ldot
        ( { path with txt = compact_longident path.txt },
          { name with txt = Names.compact_generated_name name.txt } )
  | Longident.Lapply (fn, argument) ->
      Longident.Lapply
        ( { fn with txt = compact_longident fn.txt },
          { argument with txt = compact_longident argument.txt } )

let str value = Location.mkloc (Names.compact_generated_name value) loc
let lid value = Location.mkloc (compact_longident value) loc

let named_loc value location =
  Location.mkloc (Names.compact_generated_name value) location

let longident_of_string name =
  let name = Names.compact_runtime_path name in
  match String.split_on_char '.' name with
  | [] -> Longident.Lident name
  | first :: rest ->
      List.fold_left
        (fun path segment ->
          Longident.Ldot (lid path, str segment))
        (Longident.Lident first) rest

let type_constructor name args =
  Ast_helper.Typ.constr ~loc (lid (longident_of_string name)) args

let rec core_type ?(inference_variables = []) ?(type_variables = []) = function
  | Types.TOcaml_app (name, [Types.TOcaml signature]) when name = Types.module_package_name ->
      Ast_helper.Typ.package ~loc (Ast_helper.Typ.package_type ~loc (lid (longident_of_string signature)) [])
  | Types.TPoly_variant row ->
      let fields = List.map (fun (tag, payload) ->
        Ast_helper.Rf.tag ~loc (Location.mkloc tag loc) (Option.is_none payload)
          (Option.to_list (Option.map (core_type ~inference_variables ~type_variables) payload))) row.tags in
      Ast_helper.Typ.variant ~loc fields
        (if row.bound = Types.Lower_row then Open else Closed)
        (match row.bound with Types.Upper_row -> Some [] | Types.Bounded_row tags -> Some tags | _ -> None)
  | Types.TInt -> type_constructor "int" []
  | Types.TFloat -> type_constructor "float" []
  | Types.TChar -> type_constructor "char" []
  | Types.TString | Types.TRegex | Types.TSymbol | Types.TKeyword ->
      type_constructor "string" []
  | Types.TMap_keys ->
      Ast_helper.Typ.constr ~loc
        (lid (longident_of_string "Lg_runtime.Core_set.String_set.t")) []
  | Types.TBool -> type_constructor "bool" []
  | Types.TUnit -> type_constructor "unit" []
  | Types.TNil ->
      let payload =
        if List.mem "a" type_variables then Ast_helper.Typ.var ~loc "a"
        else Ast_helper.Typ.any ~loc ()
      in
      type_constructor "option" [ payload ]
  | Types.TNullable inner ->
      type_constructor "option" [ core_type ~inference_variables ~type_variables inner ]
  | Types.TUnknown -> Ast_helper.Typ.var ~loc "a"
  | Types.TMeta meta -> (
      match List.assoc_opt meta.id inference_variables with
      | Some name -> Ast_helper.Typ.var ~loc name
      | None -> Ast_helper.Typ.any ~loc ())
  | Types.TVar name -> Ast_helper.Typ.var ~loc name
  | Types.TOcaml name ->
      Ast_helper.Typ.constr ~loc (lid (longident_of_string name)) []
  | Types.TConstraint (Open_boundary_constraint _) ->
      type_constructor "Lg_runtime.Runtime_dynamic.t" []
  | Types.TConstraint (Truthy_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "bool" []));
          (None, value_ty);
        ]
  | Types.TConstraint (Nil_predicate_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "bool" []));
          (None, value_ty);
        ]
  | Types.TConstraint (Printable_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          ( None,
            Ast_helper.Typ.tuple ~loc
              [
                (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                         (type_constructor "string" []));
                (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                         (type_constructor "string" []));
              ] );
          (None, value_ty);
        ]
  | Types.TConstraint (Exception_data_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "Lg_edn_backend.t" []));
          (None, value_ty);
        ]
  | Types.TConstraint (Hashable_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "int" []));
          (None, value_ty);
        ]
  | Types.TConstraint (Comparable_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      let compare_ty =
        Ast_helper.Typ.arrow ~loc Nolabel value_ty
          (Ast_helper.Typ.arrow ~loc Nolabel value_ty
             (type_constructor "int" []))
      in
      Ast_helper.Typ.tuple ~loc [ (None, compare_ty); (None, value_ty) ]
  | Types.TConstraint (Array_index_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "int" []));
          (None, value_ty);
        ]
  | Types.TConstraint (Symbol_predicate_constraint value_ty) ->
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None, Ast_helper.Typ.arrow ~loc Nolabel value_ty
                   (type_constructor "option" [ type_constructor "string" [] ]));
          (None, value_ty);
        ]
  | Types.TConstraint (Contains_constraint { key = key_ty; storage = value_ty }) ->
      let key_ty = core_type ~inference_variables ~type_variables key_ty in
      let value_ty = core_type ~inference_variables ~type_variables value_ty in
      Ast_helper.Typ.tuple ~loc
        [
          (None,
           Ast_helper.Typ.arrow ~loc Nolabel key_ty
             (type_constructor "bool" []));
          (None, value_ty);
        ]
  | Types.TConstraint
      (Seqable_constraint
        { requirement = Required; element = inner; storage = container }) ->
      let element = core_type ~inference_variables ~type_variables inner in
      let value =
        core_type ~inference_variables ~type_variables (Types.constraint_value_type container)
      in
      let container = core_type ~inference_variables ~type_variables container in
      let adapter =
        Ast_helper.Typ.arrow ~loc Nolabel value
          (type_constructor "Seq.t" [ element ])
      in
      Ast_helper.Typ.tuple ~loc [ (None, adapter); (None, container) ]
  | Types.TConstraint
      (Seqable_constraint
        {
          requirement = (Optional | Optional_sequential);
          element = inner;
          storage = container;
        }) ->
      let element = core_type ~inference_variables ~type_variables inner in
      let value =
        core_type ~inference_variables ~type_variables (Types.constraint_value_type container)
      in
      let container = core_type ~inference_variables ~type_variables container in
      let adapter =
        Ast_helper.Typ.arrow ~loc Nolabel value
          (type_constructor "Seq.t" [ element ])
      in
      Ast_helper.Typ.tuple ~loc
        [ (None, type_constructor "option" [ adapter ]); (None, container) ]
  | Types.TConstraint
      (Protocol_constraint { witness = witness_ty; value = value_ty; _ }) ->
      Ast_helper.Typ.tuple ~loc
        [ (None,
            type_constructor "option"
              [ core_type ~inference_variables ~type_variables witness_ty ]);
          (None, core_type ~inference_variables ~type_variables value_ty);
        ]
  | Types.TOcaml_app (name, [ method_ty ])
    when name = Types.reify_self_method_name ->
      core_type ~inference_variables ~type_variables method_ty
  | (Types.TOcaml_app _ as ty)
    when Option.is_some (Types.reify_protocol_payload_info ty) ->
      let _, methods_ty, rest_ty =
        Types.reify_protocol_payload_info ty |> Option.get
      in
      Ast_helper.Typ.tuple ~loc
        [
          (None, core_type ~inference_variables ~type_variables methods_ty);
          (None, core_type ~inference_variables ~type_variables rest_ty);
        ]
  | Types.TOcaml_app (name, [ inner ]) when Types.is_next_seq_type_name name ->
      type_constructor "Seq.t" [ core_type ~inference_variables ~type_variables inner ]
  | Types.TOcaml_app (name, [ inner ])
    when name = Types.maybe_reduced_callback_type_name ->
      type_constructor Types.reduced_type_name
        [ core_type ~inference_variables ~type_variables inner ]
  | Types.TOcaml_app (name, args) ->
      Ast_helper.Typ.constr ~loc (lid (longident_of_string name))
        (List.map (core_type ~inference_variables ~type_variables) args)
  | Types.TTuple args ->
      Ast_helper.Typ.tuple ~loc
        (List.map
           (fun arg -> (None, core_type ~inference_variables ~type_variables arg))
           args)
  | Types.TArray inner ->
      type_constructor "array" [ core_type ~inference_variables ~type_variables inner ]
  | Types.TRef inner ->
      type_constructor "Lg_runtime.Runtime_reference.t"
        [ core_type ~inference_variables ~type_variables inner ]
  | Types.TList inner ->
      type_constructor "list" [ core_type ~inference_variables ~type_variables inner ]
  | Types.TSeq inner ->
      type_constructor "Seq.t" [ core_type ~inference_variables ~type_variables inner ]
  | Types.TSet inner -> (
      match Types.set_module_name inner with
      | Ok "Lg_runtime.Runtime_poly_set" ->
          type_constructor "Lg_runtime.Runtime_poly_set.t"
            [ core_type ~inference_variables ~type_variables inner ]
      | Ok "Lg_runtime.Runtime_map_set" -> (
          match (inner, Types.record_fields inner) with
          | Types.TOcaml_app
              ("Lg_runtime.Runtime_map.t", [ key_ty; value_ty ]),
            _ ->
              type_constructor "Lg_runtime.Runtime_map_set.t"
                [
                  core_type ~inference_variables ~type_variables key_ty;
                  core_type ~inference_variables ~type_variables value_ty;
                ]
          | Types.TRecord _, Some fields -> (
              match Types.homogeneous_record_value_type fields with
              | Some value_ty ->
                  type_constructor "Lg_runtime.Runtime_map_set.t"
                    [
                      core_type ~inference_variables ~type_variables Types.TKeyword;
                      core_type ~inference_variables ~type_variables value_ty;
                    ]
              | None -> assert false)
          | _ -> assert false)
      | Ok set_module ->
          Ast_helper.Typ.constr ~loc
            (lid (longident_of_string (set_module ^ ".t"))) []
      | Error _ ->
          type_constructor "unsupported_set"
            [ core_type ~inference_variables ~type_variables inner ])
  | Types.TVector inner ->
      Ast_helper.Typ.constr ~loc
        (lid
           (Longident.Ldot
              (lid (Longident.Lident "Rrbvec"), str "t")))
        [ core_type ~inference_variables ~type_variables inner ]
  | Types.TFn (args, ret) ->
      let args = match args with [] -> [ Types.TUnit ] | _ -> args in
      List.fold_right
        (fun arg result ->
          Ast_helper.Typ.arrow ~loc Nolabel
            (core_type ~inference_variables ~type_variables arg)
            result)
        args (core_type ~inference_variables ~type_variables ret)
  | Types.TOverloaded_fn arities ->
      core_type ~inference_variables ~type_variables (Types.overloaded_storage_type arities)
  | Types.TRecord fields -> (
      match Types.homogeneous_record_value_type fields with
      | Some value_ty ->
          core_type ~inference_variables ~type_variables (Types.dynamic_map Types.TKeyword value_ty)
      | None -> type_constructor "record" [])
  | Types.TNamed_record record ->
      Ast_helper.Typ.constr ~loc
        (lid (longident_of_string record.type_name))
        (List.map (core_type ~inference_variables ~type_variables) record.type_arguments)

let record_values_to_parsetree var_name values =
  let rec loop acc = function
    | [] -> Ok (List.rev acc)
    | ((field : Types.field), expression) :: rest -> (
        let context = "record " ^ var_name ^ " field " ^ field.keyword in
        match
          Ocaml_ir.to_parsetree ~context
            (Semantic_lowering.expression expression)
        with
        | Error _ as err -> err
        | Ok expr ->
            loop ((lid (Longident.Lident field.ocaml_name), expr) :: acc) rest)
  in
  loop [] values

let type_parameters parameters =
  List.map
    (fun name ->
      ( Ast_helper.Typ.var ~loc name,
        (Asttypes.NoVariance, Asttypes.NoInjectivity) ))
    parameters

let declaration_location = Option.value ~default:loc

let rec type_mentions name = function
  | Types.TPoly_variant row -> List.exists (type_mentions name) (List.filter_map snd row.tags)
  | Types.TOcaml candidate -> candidate = name
  | Types.TOcaml_app (candidate, args) ->
      candidate = name || List.exists (type_mentions name) args
  | Types.TTuple args -> List.exists (type_mentions name) args
  | Types.TConstraint constraint_ ->
      List.exists (type_mentions name) (Types.constraint_children constraint_)
  | Types.TArray inner | Types.TRef inner | Types.TList inner
  | Types.TVector inner | Types.TSet inner | Types.TSeq inner
  | Types.TNullable inner ->
      type_mentions name inner
  | Types.TFn (params, return_ty) ->
      List.exists (type_mentions name) params || type_mentions name return_ty
  | Types.TOverloaded_fn arities ->
      List.exists
        (fun (arity : Types.fn_arity) ->
          List.exists (type_mentions name) arity.fixed_params
          || Option.fold ~none:false ~some:(type_mentions name) arity.rest_param
          || type_mentions name arity.return_ty)
        arities
  | Types.TRecord fields ->
      List.exists (fun (field : Types.field) -> type_mentions name field.ty) fields
  | Types.TNamed_record record ->
      record.type_name = name
      || List.exists (type_mentions name) record.type_arguments
      || List.exists
           (fun (field : Types.field) -> type_mentions name field.ty)
           record.fields
  | Types.TInt | Types.TFloat | Types.TChar | Types.TString | Types.TRegex
  | Types.TMap_keys | Types.TSymbol | Types.TKeyword | Types.TBool | Types.TUnit
  | Types.TNil | Types.TUnknown | Types.TMeta _ | Types.TVar _ ->
      false

let warning_attribute location flags =
  Ast_helper.Attr.mk ~loc:location
    (Location.mkloc "warning" location)
    (PStr
       [
         Ast_helper.Str.eval ~loc:location
           (Ast_helper.Exp.constant ~loc:location
              (Ast_helper.Const.string ~loc:location flags));
       ])

let unused_type_warning_attribute location = warning_attribute location "-34"

let unused_constructor_warning_attribute location = warning_attribute location "-37"

let record_type_definition type_name parameters fields location =
  let declaration_loc = declaration_location location in
  let label_declarations =
    fields
    |> List.map (fun (field : Types.field) ->
           let field_loc = declaration_location field.location in
           Ast_helper.Type.field ~loc:field_loc
             ~mut:(if field.mutable_ then Mutable else Immutable)
             (named_loc field.ocaml_name field_loc)
             (let ty = core_type ~type_variables:(field.quantified @ parameters) field.ty in
              if field.quantified = [] then ty
              else Ast_helper.Typ.poly ~loc:field_loc
                (List.map (fun name -> named_loc name field_loc) field.quantified) ty))
  in
  let type_declaration =
    if fields = [] then
      Ast_helper.Type.mk ~loc:declaration_loc
        ~attrs:[ unused_type_warning_attribute declaration_loc ]
        ~params:(type_parameters parameters)
        ~manifest:(Ast_helper.Typ.constr ~loc:declaration_loc (lid (Longident.Lident "unit")) [])
        (named_loc type_name declaration_loc)
    else
      Ast_helper.Type.mk ~loc:declaration_loc
        ~params:(type_parameters parameters)
        ~kind:(Ptype_record label_declarations)
        (named_loc type_name declaration_loc)
  in
  let recursion =
    if List.exists (fun (field : Types.field) -> type_mentions type_name field.ty) fields
    then Recursive
    else Nonrecursive
  in
  Ast_helper.Str.type_ ~loc recursion [ type_declaration ]

let polymorphic_holder_type_definition type_name field_name value_type
    type_variables =
  let field_type =
    type_constructor "option" [ core_type ~type_variables value_type ]
    |> Ast_helper.Typ.poly ~loc (List.map str type_variables)
  in
  let field =
    Ast_helper.Type.field ~loc (str field_name) field_type
  in
  let declaration =
    Ast_helper.Type.mk ~loc ~kind:(Ptype_record [ field ]) (str type_name)
  in
  Ast_helper.Str.type_ ~loc Nonrecursive [ declaration ]

let type_alias_definition type_name parameters manifest location =
  let declaration_loc = declaration_location location in
  let type_declaration =
    Ast_helper.Type.mk ~loc:declaration_loc
      ~attrs:[ unused_type_warning_attribute declaration_loc ]
      ~params:(type_parameters parameters)
      ~manifest:(core_type manifest) (named_loc type_name declaration_loc)
  in
  Ast_helper.Str.type_ ~loc Nonrecursive [ type_declaration ]

let type_variant_definition type_name parameters constructors location =
  let declaration_loc = declaration_location location in
  let constructor_declarations =
    constructors
    |> List.map (fun (constructor : variant_constructor) ->
           let constructor_loc =
             Option.value constructor.location ~default:loc
           in
           Ast_helper.Type.constructor ~loc:constructor_loc
             ~args:(Pcstr_tuple (List.map core_type constructor.payload_types))
             ?res:(Option.map core_type constructor.result_type)
             (named_loc constructor.constructor_name constructor_loc))
  in
  let type_declaration =
    Ast_helper.Type.mk ~loc:declaration_loc ~params:(type_parameters parameters)
      ~attrs:[ unused_constructor_warning_attribute declaration_loc ]
      ~kind:(Ptype_variant constructor_declarations)
      (named_loc type_name declaration_loc)
  in
  Ast_helper.Str.type_ ~loc Recursive [ type_declaration ]

let rec signature_item = function
  | Signature_value { value_name; value_type; location; _ } ->
      let item_loc = declaration_location location in
      Ast_helper.Sig.value ~loc:item_loc
        (Ast_helper.Val.mk ~loc:item_loc (named_loc value_name item_loc)
           (core_type value_type))
  | Signature_type
      { type_name; type_parameters = parameters; manifest; location } ->
      let item_loc = declaration_location location in
      let type_declaration =
        match manifest with
        | None ->
            Ast_helper.Type.mk ~loc:item_loc ~params:(type_parameters parameters)
              (named_loc type_name item_loc)
        | Some manifest ->
            Ast_helper.Type.mk ~loc:item_loc ~params:(type_parameters parameters)
              ~manifest:(core_type manifest) (named_loc type_name item_loc)
      in
      Ast_helper.Sig.type_ ~loc:item_loc Nonrecursive [ type_declaration ]
  | Signature_module
      { module_name; module_signature; location; signature_location; _ } ->
      let item_loc = declaration_location location in
      let signature_loc = declaration_location signature_location in
      let module_type =
        Ast_helper.Mty.ident ~loc:signature_loc
          (Location.mkloc (longident_of_string module_signature) signature_loc)
      in
      Ast_helper.Sig.module_ ~loc:item_loc
        (Ast_helper.Md.mk ~loc:item_loc
           (Location.mkloc (Some module_name) item_loc) module_type)
  | Signature_inline_module {module_name; items; location; _} ->
      let loc = declaration_location location in
      Ast_helper.Sig.module_ ~loc (Ast_helper.Md.mk ~loc (Location.mkloc (Some module_name) loc)
        (Ast_helper.Mty.signature ~loc (List.map signature_item items)))
  | Signature_include { module_signature; signature_location; type_constraints } ->
      let signature_loc = declaration_location signature_location in
      let module_type =
        Ast_helper.Mty.ident ~loc:signature_loc
          (Location.mkloc (longident_of_string module_signature) signature_loc)
      in
      let module_type = match type_constraints with
        | [] -> module_type
        | constraints ->
            let constraints = List.map
              (fun (constraint_ : Lowered.signature_type_constraint) ->
                let loc = declaration_location constraint_.constraint_location in
                let name = constraint_.constrained_name in
                let declaration_name = List.hd (List.rev (String.split_on_char '.' name)) in
                let declaration = Ast_helper.Type.mk ~loc
                  ~params:(type_parameters constraint_.constrained_parameters)
                  ~manifest:(core_type constraint_.replacement) (named_loc declaration_name loc) in
                let path = Location.mkloc (longident_of_string name) loc in
                if constraint_.destructive then Parsetree.Pwith_typesubst (path, declaration)
                else Parsetree.Pwith_type (path, declaration)) constraints in
            Ast_helper.Mty.with_ ~loc:signature_loc module_type constraints
      in
      Ast_helper.Sig.include_ ~loc:signature_loc
        (Ast_helper.Incl.mk ~loc:signature_loc module_type)

let module_signature_definition signature_name items =
  let module_type =
    Ast_helper.Mty.signature ~loc (List.map signature_item items)
  in
  Ast_helper.Str.modtype ~loc
    (Ast_helper.Mtd.mk ~loc ~typ:module_type (str signature_name))

let set_module_definition module_name element_ty =
  let type_declaration =
    Ast_helper.Type.mk ~loc ~manifest:(core_type element_ty) (str "t")
  in
  let record_compare record_ty fields =
    let left_name = "__lg_set_left" in
    let right_name = "__lg_set_right" in
    let ident name =
      Ast_helper.Exp.ident ~loc (lid (Longident.Lident name))
    in
    let int_zero =
      Ast_helper.Exp.constant ~loc (Ast_helper.Const.int ~loc 0)
    in
    let rec compare_fields index = function
      | [] -> int_zero
      | (field : Types.field) :: rest ->
          let comparison_name =
            "__lg_set_comparison_" ^ string_of_int index
          in
          let project record_name =
            Ast_helper.Exp.field ~loc (ident record_name)
              (lid (Longident.Lident field.ocaml_name))
          in
          let comparison =
            Ast_helper.Exp.apply ~loc
              (Ast_helper.Exp.ident ~loc
                 (lid
                    (longident_of_string
                       "Lg_runtime.Runtime_compare.safe_compare")))
              [ (Nolabel, project left_name); (Nolabel, project right_name) ]
          in
          let condition =
            Ast_helper.Exp.apply ~loc
              (Ast_helper.Exp.ident ~loc (lid (Longident.Lident "=")))
              [ (Nolabel, ident comparison_name); (Nolabel, int_zero) ]
          in
          let body =
            Ast_helper.Exp.ifthenelse ~loc condition
              (compare_fields (index + 1) rest)
              (Some (ident comparison_name))
          in
          Ast_helper.Exp.let_ ~loc Nonrecursive
            [
              Ast_helper.Vb.mk ~loc
                (Ast_helper.Pat.var ~loc (str comparison_name))
                comparison;
            ]
            body
    in
    let parameter name =
      Ast_helper.Pat.constraint_ ~loc
        (Ast_helper.Pat.var ~loc (str name))
        (core_type record_ty)
    in
    let function_parameter pattern =
      {
        pparam_loc = loc;
        pparam_desc = Pparam_val (Nolabel, None, pattern);
      }
    in
    Ast_helper.Exp.function_ ~loc
      [
        function_parameter (parameter left_name);
        function_parameter (parameter right_name);
      ]
      None (Pfunction_body (compare_fields 0 fields))
  in
  let compare_binding =
    Ast_helper.Vb.mk ~loc (Ast_helper.Pat.var ~loc (str "compare"))
      (match element_ty with
      | Types.TNamed_record record ->
          record_compare element_ty record.fields
      | Types.TNullable (Types.TNamed_record record)
      | Types.TOcaml_app ("option", [ Types.TNamed_record record ]) ->
          Ast_helper.Exp.apply ~loc
            (Ast_helper.Exp.ident ~loc
               (lid
                  (longident_of_string
                     "Lg_runtime.Runtime_compare.compare_option")))
            [
              ( Nolabel,
                record_compare (Types.TNamed_record record) record.fields );
            ]
      | _ ->
          Ast_helper.Exp.ident ~loc
            (lid (longident_of_string "Stdlib.compare")))
  in
  let comparator =
    Ast_helper.Mod.structure ~loc
      [ Ast_helper.Str.type_ ~loc Nonrecursive [ type_declaration ];
        Ast_helper.Str.value ~loc Nonrecursive [ compare_binding ] ]
  in
  let set_make =
    Ast_helper.Mod.ident ~loc (lid (longident_of_string "Set.Make"))
  in
  let module_expr = Ast_helper.Mod.apply ~loc set_make comparator in
  let module_binding =
    Ast_helper.Mb.mk ~loc (Location.mkloc (Some module_name) loc) module_expr
  in
  Ast_helper.Str.module_ ~loc module_binding

let qualify_generated_module module_path module_name =
  if module_path = [] || String.contains module_name '.' then module_name
  else String.concat "." (module_path @ [ module_name ])

let rec collect_set_modules_from_type module_path modules = function
  | Types.TPoly_variant row -> List.fold_left (collect_set_modules_from_type module_path) modules (List.filter_map snd row.tags)
  | Types.TSet element_ty ->
      let modules =
        match Types.set_module_name element_ty with
        | Ok module_name ->
            String_map.add
              (qualify_generated_module module_path module_name)
              element_ty modules
        | Error _ -> modules
      in
      collect_set_modules_from_type module_path modules element_ty
  | Types.TNullable ty | Types.TArray ty | Types.TRef ty | Types.TList ty
  | Types.TVector ty | Types.TSeq ty ->
      collect_set_modules_from_type module_path modules ty
  | Types.TOcaml_app (_, arguments) | Types.TTuple arguments ->
      List.fold_left
        (collect_set_modules_from_type module_path)
        modules arguments
  | Types.TConstraint constraint_ ->
      List.fold_left
        (collect_set_modules_from_type module_path)
        modules (Types.constraint_children constraint_)
  | Types.TFn (parameters, return_ty) ->
      List.fold_left
        (collect_set_modules_from_type module_path)
        (collect_set_modules_from_type module_path modules return_ty)
        parameters
  | Types.TOverloaded_fn arities ->
      List.fold_left
        (fun modules (arity : Types.fn_arity) ->
          let modules =
            List.fold_left
              (collect_set_modules_from_type module_path)
              modules arity.fixed_params
          in
          let modules =
            Option.fold ~none:modules
              ~some:(collect_set_modules_from_type module_path modules)
              arity.rest_param
          in
          collect_set_modules_from_type module_path modules arity.return_ty)
        modules arities
  | Types.TRecord fields ->
      List.fold_left
        (fun modules (field : Types.field) ->
          collect_set_modules_from_type module_path modules field.ty)
        modules fields
  | Types.TNamed_record record ->
      List.fold_left
        (collect_set_modules_from_type module_path)
        modules record.type_arguments
  | Types.TInt | Types.TFloat | Types.TChar | Types.TString | Types.TRegex
  | Types.TMap_keys | Types.TSymbol | Types.TKeyword | Types.TBool | Types.TUnit
  | Types.TNil | Types.TUnknown | Types.TMeta _ | Types.TVar _ | Types.TOcaml _ ->
      modules

let collect_set_modules_from_expression module_path modules expression =
  let modules = ref modules in
  let collect_type ty =
    modules := collect_set_modules_from_type module_path !modules ty
  in
  ignore
    (Semantic_ir.rewrite
       (fun expression ->
         (match expression with
         | Semantic_ir.Typed (ty, _) -> collect_type ty
         | Semantic_ir.PackDynamic conversion ->
             collect_type conversion.source_ty;
             collect_type conversion.target_ty
         | Semantic_ir.UnpackDynamic conversion ->
             collect_type conversion.source_ty;
             collect_type conversion.target_ty
         | Semantic_ir.NullableToSeq conversion ->
             collect_type conversion.source_ty;
             collect_type conversion.element_ty
         | _ -> ());
         expression)
       expression);
  !modules

let rec collect_set_modules_from_items module_path modules items =
  let collect_expression = collect_set_modules_from_expression module_path in
  let collect_field modules (field : Types.field) =
    collect_set_modules_from_type module_path modules field.ty
  in
  List.fold_left
    (fun modules -> function
      | Value_binding { expression; _ }
      | Recursive_value_binding { expression; _ }
      | Deferred_value_binding { expression; _ } ->
          collect_expression modules expression
      | Recursive_value_bindings bindings ->
          List.fold_left
            (fun modules (binding : recursive_value) ->
              collect_expression modules binding.expression)
            modules bindings
      | Foreign_binding { value_type; _ }
      | Polymorphic_holder_type { value_type; _ } ->
          collect_set_modules_from_type module_path modules value_type
      | Type_def { fields; _ } ->
          List.fold_left collect_field modules fields
      | Opaque_type _ -> modules
      | Type_alias { manifest; _ } ->
          collect_set_modules_from_type module_path modules manifest
      | Type_variant { constructors; _ } ->
          List.fold_left
            (fun modules (constructor : variant_constructor) ->
              List.fold_left
                (collect_set_modules_from_type module_path)
                modules (constructor.payload_types @ Option.to_list constructor.result_type))
            modules constructors
      | Group items -> collect_set_modules_from_items module_path modules items
      | Module_def { module_name; items; _ } ->
          collect_set_modules_from_items (module_path @ [ module_name ]) modules
            items
      | Module_functor { functor_name; items; _ } ->
          collect_set_modules_from_items (module_path @ [ functor_name ]) modules
            items
      | Module_signature { items; _ } ->
          List.fold_left
            (fun modules -> function
              | Signature_value { value_type; _ } ->
                  collect_set_modules_from_type module_path modules value_type
              | Signature_type { manifest = Some manifest; _ } ->
                  collect_set_modules_from_type module_path modules manifest
              | Signature_type { manifest = None; _ } | Signature_inline_module _ | Signature_module _
              | Signature_include _ ->
                  modules)
            modules items
      | Record_def { fields; values; _ } ->
          let modules = List.fold_left collect_field modules fields in
          List.fold_left
            (fun modules (_, expression) ->
              collect_expression modules expression)
            modules values
      | Projected_record_def { fields; source; _ } ->
          collect_expression
            (List.fold_left collect_field modules fields)
            source
      | Comment _ | Module_alias _ | Module_apply _ | Open_module _
      | Include_module _ ->
          modules)
    modules items

let string_attribute name value =
  let payload =
    Parsetree.PStr
      [ Ast_helper.Str.eval
          (Ast_helper.Exp.constant (Ast_helper.Const.string value)) ]
  in
  Ast_helper.Attr.mk (str name) payload

let source_attributes node_id =
  string_attribute "lg.node_id" (Source_node_id.to_string node_id)
  :: (Source_node_id.origins node_id
     |> List.map (fun origin ->
            string_attribute "lg.origin"
              (Source_node_id.origin_to_string origin)))

let record_definition ~emit_set ~emit_nullable_set var_name identity type_id
    type_name type_parameters set_module_name fields values =
  let type_item =
    record_type_definition type_name type_parameters fields None
  in
  let record_type =
    Types.named_record ~type_id ~type_name ~type_parameters ~set_module_name fields
  in
  let type_items =
    [ type_item ]
    @
    (if emit_set && type_parameters = [] then
       [ set_module_definition set_module_name record_type ]
     else [])
    @
    if emit_nullable_set && type_parameters = [] then
      [
        set_module_definition (set_module_name ^ "_nullable")
          (Types.TNullable record_type);
      ]
    else []
  in
  match record_values_to_parsetree var_name values with
  | Error _ as err -> err
  | Ok record_fields ->
      let record_expr = Ast_helper.Exp.record ~loc record_fields None in
      let annotated_expr =
        Ast_helper.Exp.constraint_ ~loc record_expr
          (type_constructor type_name
             (List.map (fun _ -> Ast_helper.Typ.any ~loc ()) type_parameters))
      in
      let value_binding =
        let pattern = Ast_helper.Pat.var ~loc (str var_name) in
        let pattern =
          match identity with
          | None -> pattern
          | Some (node_id, location) ->
              { pattern with
                ppat_loc = location;
                ppat_attributes =
                  source_attributes node_id @ pattern.ppat_attributes;
              }
        in
        Ast_helper.Vb.mk ~loc
          pattern
          annotated_expr
      in
      Ok (type_items @ [ Ast_helper.Str.value ~loc Nonrecursive [ value_binding ] ])

let projected_record_definition ~emit_set ~emit_nullable_set var_name identity
    type_id type_name type_parameters set_module_name fields source =
  let type_item =
    record_type_definition type_name type_parameters fields None
  in
  let record_type =
    Types.named_record ~type_id ~type_name ~type_parameters ~set_module_name fields
  in
  let type_items =
    [ type_item ]
    @
    (if emit_set && type_parameters = [] then
       [ set_module_definition set_module_name record_type ]
     else [])
    @
    if emit_nullable_set && type_parameters = [] then
      [
        set_module_definition (set_module_name ^ "_nullable")
          (Types.TNullable record_type);
      ]
    else []
  in
  match
    Ocaml_ir.to_parsetree ~context:("record source " ^ var_name)
      (Semantic_lowering.expression source)
  with
  | Error _ as err -> err
  | Ok source_expr ->
      let source_name = "__lg_record_source" in
      let source_ident = Ast_helper.Exp.ident ~loc (lid (Longident.Lident source_name)) in
      let projected_fields =
        List.map
          (fun (field : Types.field) ->
            let label = lid (Longident.Lident field.ocaml_name) in
            (label, Ast_helper.Exp.field ~loc source_ident label))
          fields
      in
      let record_expr = Ast_helper.Exp.record ~loc projected_fields None in
      let projected_expr =
        Ast_helper.Exp.let_ ~loc Nonrecursive
          [ Ast_helper.Vb.mk ~loc
              (Ast_helper.Pat.var ~loc (str source_name))
              source_expr ]
          record_expr
        |> fun expression ->
        Ast_helper.Exp.constraint_ ~loc expression
          (type_constructor type_name
             (List.map (fun _ -> Ast_helper.Typ.any ~loc ()) type_parameters))
      in
      let pattern = Ast_helper.Pat.var ~loc (str var_name) in
      let pattern =
        match identity with
        | None -> pattern
        | Some (node_id, location) ->
            { pattern with
              ppat_loc = location;
              ppat_attributes = source_attributes node_id @ pattern.ppat_attributes;
            }
      in
      let value_binding = Ast_helper.Vb.mk ~loc pattern projected_expr in
      Ok (type_items @ [ Ast_helper.Str.value ~loc Nonrecursive [ value_binding ] ])

let rec value_pattern = function
  | Named name -> Ast_helper.Pat.var ~loc (str name)
  | Declared_value (pattern, _) -> value_pattern pattern
  | Unit_pattern ->
      Ast_helper.Pat.construct ~loc (lid (Longident.Lident "()")) None
  | Ignore_pattern -> Ast_helper.Pat.any ~loc ()
  | Located_value (node_id, location, pattern) ->
      let pattern = value_pattern pattern in
      {
        pattern with
        ppat_loc = location;
        ppat_attributes = source_attributes node_id @ pattern.ppat_attributes;
      }

let rec value_pattern_context = function
  | Named name -> "value " ^ name
  | Declared_value (pattern, _) -> value_pattern_context pattern
  | Unit_pattern -> "top-level effect"
  | Ignore_pattern -> "top-level expression"
  | Located_value (_, _, pattern) -> value_pattern_context pattern

let declared_value_constraint ty =
  let type_variables =
    Type_solver.variables ty
    |> List.filter_map (function
         | Type_solver.Declared name -> Some name
         | Type_solver.Metavariable _ -> None)
    |> List.sort_uniq String.compare
  in
  (* Inferred holes are not part of the declared universal contract. Leave
     them anonymous so OCaml applies the value restriction to the expression
     instead of treating omitted source types as promised type variables. *)
  let annotation =
    core_type ~type_variables ty
    |> Ast_helper.Typ.poly ~loc (List.map str type_variables)
  in
  Pvc_constraint { locally_abstract_univars = []; typ = annotation }

let rec value_pattern_constraint = function
  | Declared_value (_, ty) -> Some (declared_value_constraint ty)
  | Located_value (_, _, pattern) -> value_pattern_constraint pattern
  | Named _ | Unit_pattern | Ignore_pattern -> None

let recursive_value_pattern_and_constraint name identity type_annotation =
  let pattern =
    match identity with
    | None -> Named name
    | Some (node_id, location) ->
        Located_value (node_id, location, Named name)
  in
  (value_pattern pattern, Option.map declared_value_constraint type_annotation)

let value_binding pattern expression =
  let context =
    value_pattern_context pattern
  in
  match
    Ocaml_ir.to_parsetree ~context (Semantic_lowering.expression expression)
  with
  | Error _ as err -> err
  | Ok expression ->
      let binding =
        Ast_helper.Vb.mk ~loc ?value_constraint:(value_pattern_constraint pattern)
          (value_pattern pattern) expression |> Gadt_parsetree.binding
      in
      Ok [ Ast_helper.Str.value ~loc Nonrecursive [ binding ] ]

let recursive_value_binding name identity type_annotation semantic_expression =
  match
    Ocaml_ir.to_parsetree ~context:("recursive value " ^ name)
      (Semantic_lowering.expression semantic_expression)
  with
  | Error _ as err -> err
  | Ok expression ->
      let pattern, value_constraint =
        recursive_value_pattern_and_constraint name identity type_annotation
      in
      let binding =
        Ast_helper.Vb.mk ~loc ?value_constraint pattern expression |> Gadt_parsetree.binding
      in
      Ok [ Ast_helper.Str.value ~loc Recursive [ binding ] ]

let recursive_value_bindings bindings =
  let rec compile acc = function
    | [] -> Ok (List.rev acc)
    | (binding : recursive_value) :: rest -> (
        match
          Ocaml_ir.to_parsetree ~context:("recursive value " ^ binding.name)
            (Semantic_lowering.expression binding.expression)
        with
        | Error _ as err -> err
        | Ok expression ->
            let pattern, value_constraint =
              recursive_value_pattern_and_constraint binding.name
                binding.identity binding.type_annotation
            in
            compile
              ((Ast_helper.Vb.mk ~loc ?value_constraint pattern expression |> Gadt_parsetree.binding)
              :: acc)
              rest)
  in
  match compile [] bindings with
  | Error _ as err -> err
  | Ok bindings -> Ok [ Ast_helper.Str.value ~loc Recursive bindings ]

let set_module_requested requested_sets module_path module_name =
  String_map.mem
    (qualify_generated_module module_path module_name)
    requested_sets

let anonymous_type_name = function
  | {
   pstr_desc = Pstr_type (Nonrecursive, [ declaration ]);
   _;
  }
    when let name = declaration.ptype_name.txt in
         String.length name > 1 && name.[0] = 't'
         && String.for_all
              (fun character -> character >= '0' && character <= '9')
              (String.sub name 1 (String.length name - 1)) ->
      Some declaration.ptype_name.txt
  | _ -> None

let referenced_local_types item =
  let references = ref String_map.empty in
  let default = Ast_iterator.default_iterator in
  let iterator =
    {
      default with
      typ =
        (fun iterator ty ->
          (match ty.ptyp_desc with
          | Ptyp_constr ({ txt = Longident.Lident name; _ }, _) ->
              references := String_map.add name () !references
          | _ -> ());
          default.typ iterator ty);
    }
  in
  iterator.structure_item iterator item;
  !references

let remove_unused_anonymous_types structure =
  let candidates, roots =
    List.fold_left
      (fun (candidates, roots) item ->
        let references = referenced_local_types item in
        match anonymous_type_name item with
        | Some name -> (String_map.add name references candidates, roots)
        | None ->
            ( candidates,
              String_map.union (fun _ () () -> Some ()) roots references ))
      (String_map.empty, String_map.empty) structure
  in
  let rec reachable_types reachable pending =
    match pending with
    | [] -> reachable
    | name :: pending when String_map.mem name reachable ->
        reachable_types reachable pending
    | name :: pending ->
        let reachable = String_map.add name () reachable in
        let dependencies =
          String_map.find_opt name candidates
          |> Option.value ~default:String_map.empty
          |> String_map.to_seq |> Seq.map fst |> List.of_seq
        in
        reachable_types reachable (List.rev_append dependencies pending)
  in
  let reachable =
    reachable_types String_map.empty
      (roots |> String_map.to_seq |> Seq.map fst |> List.of_seq)
  in
  List.filter
    (fun item ->
      match anonymous_type_name item with
      | Some name -> String_map.mem name reachable
      | None -> true)
    structure

let rec structure_of_item_with_sets requested_sets module_path = function
  | Foreign_binding foreign ->
      (match foreign.backend with
       | Foreign_binding.Ocaml_primitive symbol ->
           let loc = declaration_location foreign.location in
           Ok [Ast_helper.Str.primitive ~loc
             (Ast_helper.Val.mk ~loc ~prim:[symbol]
               (named_loc foreign.name loc) (core_type foreign.value_type))]
       | Foreign_binding.Native_callback (arguments, result) ->
           value_binding (Named foreign.name)
             (Semantic_ir.Typed (foreign.value_type,
               Semantic_ir.Apply (Semantic_ir.Ident "Lg_ffi.Callback.create",
                 [Foreign_binding.native_signature arguments result])))
       | Foreign_binding.Native_callback_release ->
           value_binding (Named foreign.name)
             (Semantic_ir.Typed (foreign.value_type,
               Semantic_ir.Ident "Lg_ffi.Callback.release"))
       | Foreign_binding.Native_release ->
           value_binding (Named foreign.name)
             (Semantic_ir.Typed (foreign.value_type,
               Semantic_ir.Ident "Lg_ffi.Owned_pointer.release"))
       | Foreign_binding.Native native ->
           value_binding (Named foreign.name)
             (Foreign_binding.native_expression foreign.value_type native)
       | Foreign_binding.JavaScript_object builder ->
           let loc = declaration_location foreign.location in
           let fields = List.mapi (fun index field -> "field" ^ string_of_int index, field) builder.fields in
           let signature = List.fold_right (fun (label, (field : Foreign_binding.object_field)) rest ->
             let ty = core_type field.value_type in
             let ty = {ty with ptyp_attributes = string_attribute "mel.as" field.property :: ty.ptyp_attributes} in
             Ast_helper.Typ.arrow (if field.optional then Optional label else Labelled label) ty rest)
             fields (Ast_helper.Typ.arrow Nolabel (core_type Types.TUnit) (core_type builder.result)) in
           let primitive = Ast_helper.Str.primitive ~loc
             (Ast_helper.Val.mk ~loc ~attrs:[Ast_helper.Attr.mk (str "mel.obj") (PStr [])]
               ~prim:[""] (str "make") signature) in
           let record = Ast_helper.Exp.ident ~loc (lid (Longident.Lident "input")) in
           let arguments = List.map (fun (label, (field : Foreign_binding.object_field)) ->
             (if field.optional then Optional label else Labelled label),
             Ast_helper.Exp.field ~loc record (lid (Longident.Lident field.source.ocaml_name))) fields in
           let body = Ast_helper.Exp.apply ~loc
             (Ast_helper.Exp.ident ~loc (lid (longident_of_string "Builder.make")))
             (arguments @ [Nolabel, Ast_helper.Exp.construct ~loc (lid (Longident.Lident "()")) None]) in
           let parameter = Ast_helper.Pat.constraint_ ~loc
             (Ast_helper.Pat.var ~loc (str "input")) (core_type builder.input) in
           let fn = Ast_helper.Exp.function_ ~loc
             [{pparam_loc = loc; pparam_desc = Pparam_val (Nolabel, None, parameter)}]
             None (Pfunction_body body) in
           let expression = Ast_helper.Exp.struct_item ~loc
             (Ast_helper.Str.module_ ~loc (Ast_helper.Mb.mk ~loc {txt = Some "Builder"; loc}
               (Ast_helper.Mod.structure ~loc [primitive]))) fn in
           Ok [Ast_helper.Str.value ~loc Nonrecursive
             [Ast_helper.Vb.mk ~loc (Ast_helper.Pat.var ~loc (named_loc foreign.name loc)) expression]]
       | Foreign_binding.JavaScript javascript ->
           let location = declaration_location foreign.location in
           let operation_attributes =
             let attribute = match javascript.operation with
               | Foreign_binding.Call -> None
               | New -> Some "mel.new"
               | Send -> Some "mel.send"
               | Get -> Some "mel.get"
               | Set -> Some "mel.set"
               | Get_index -> Some "mel.get_index"
               | Set_index -> Some "mel.set_index"
             in
             Option.to_list (Option.map (fun name -> Ast_helper.Attr.mk (str name) (PStr [])) attribute)
           in
           let adapter_attributes =
             let return_attribute = match javascript.return_adapter with
               | Foreign_binding.Direct -> []
               | adapter ->
                   let name = match adapter with
                     | Nullable -> "nullable" | Null -> "null_to_opt"
                     | Undefined -> "undefined_to_opt" | Direct -> assert false
                   in
                   [Ast_helper.Attr.mk (str "mel.return")
                      (PStr [Ast_helper.Str.eval (Ast_helper.Exp.ident (lid (Longident.Lident name)))])]
             in
             if javascript.variadic then
               Ast_helper.Attr.mk (str "mel.variadic") (PStr []) :: return_attribute
             else return_attribute
           in
           let signature = match foreign.value_type with
             | Types.TFn (arguments, result) ->
                 let arguments = match arguments with [] -> [Types.TUnit] | arguments -> arguments in
                 List.fold_right (fun argument result ->
                   let ty = core_type argument in
                   let ty = match argument with
                     | Types.TFn _ ->
                         { ty with ptyp_attributes = Ast_helper.Attr.mk (str "mel.uncurry") (PStr []) :: ty.ptyp_attributes }
                     | _ -> ty
                   in
                   Ast_helper.Typ.arrow Nolabel ty result)
                   arguments (core_type result)
             | _ -> assert false
           in
           let module_attributes =
             match javascript.module_name with
             | None -> []
             | Some name -> [string_attribute "mel.module" name]
           in
           let scope_attributes =
             match javascript.scope with
             | [] -> []
             | names ->
                 let names = List.map
                   (fun name -> Ast_helper.Exp.constant (Ast_helper.Const.string name)) names in
                 let payload = match names with
                   | [name] -> name
                   | names -> Ast_helper.Exp.tuple (List.map (fun name -> None, name) names)
                 in
                 [Ast_helper.Attr.mk (str "mel.scope") (PStr [Ast_helper.Str.eval payload])]
           in
           Ok [Ast_helper.Str.primitive ~loc:location
             (Ast_helper.Val.mk ~loc:location ~attrs:(module_attributes @ scope_attributes @ operation_attributes @ adapter_attributes)
                ~prim:[javascript.symbol] (named_loc foreign.name location)
                signature)])
  | Value_binding { pattern; expression } ->
      value_binding pattern expression
  | Recursive_value_binding { name; identity; type_annotation; expression } ->
      recursive_value_binding name identity type_annotation expression
  | Recursive_value_bindings bindings -> recursive_value_bindings bindings
  | Deferred_value_binding _ ->
      invalid_arg "deferred value binding was not ordered before lowering"
  | Polymorphic_holder_type
      { type_name; field_name; value_type; type_variables } ->
      Ok
        [ polymorphic_holder_type_definition type_name field_name value_type
            type_variables ]
  | Comment _ -> Ok []
  | Type_def
      {
        type_id = _;
        type_name;
        type_parameters;
        fields;
        nominal;
        location;
      } ->
      let record_type =
        Types.named_record ~nominal ~type_name ~type_parameters
          ~set_module_name:("Set_" ^ type_name) fields
      in
      let type_definition =
        record_type_definition type_name type_parameters fields location
      in
      let definitions =
        let set_module_name = "Set_" ^ type_name in
        [ type_definition ]
        @
        (if
           type_parameters = []
           && set_module_requested requested_sets module_path set_module_name
         then [ set_module_definition set_module_name record_type ]
         else [])
        @
        if
          type_parameters = []
          && set_module_requested requested_sets module_path
               (set_module_name ^ "_nullable")
        then
          [
            set_module_definition (set_module_name ^ "_nullable")
              (Types.TNullable record_type);
          ]
        else []
      in
      Ok definitions
  | Opaque_type { type_name; location } ->
      let location = declaration_location location in
      Ok [Ast_helper.Str.type_ ~loc:location Nonrecursive
            [Ast_helper.Type.mk ~loc:location (named_loc type_name location)]]
  | Type_alias { type_name; type_parameters; manifest; location } ->
      Ok [ type_alias_definition type_name type_parameters manifest location ]
  | Type_variant { type_name; type_parameters; constructors; location } ->
      Ok
        [ type_variant_definition type_name type_parameters constructors location ]
  | Group items ->
      structure_of_items_with_sets ~prune:false requested_sets module_path items
  | Module_def
      { module_name; location; signature_name; signature_location; items } -> (
      match
        structure_of_items_with_sets requested_sets
          (module_path @ [ module_name ]) items
      with
      | Error _ as err -> err
      | Ok body ->
          let module_expr =
            let structure = Ast_helper.Mod.structure ~loc body in
            match signature_name with
            | None -> structure
            | Some signature_name ->
                let signature_loc = declaration_location signature_location in
                Ast_helper.Mod.constraint_ ~loc structure
                  (Ast_helper.Mty.ident ~loc:signature_loc
                     (Location.mkloc (longident_of_string signature_name)
                        signature_loc))
          in
          let module_loc = declaration_location location in
          let module_binding =
            Ast_helper.Mb.mk ~loc:module_loc
              (Location.mkloc (Some module_name) module_loc) module_expr
          in
          Ok [ Ast_helper.Str.module_ ~loc module_binding ])
  | Module_alias { alias_name; location; target_name; target_location } ->
      let alias_loc = declaration_location location in
      let target_loc = declaration_location target_location in
      let module_expr =
        Ast_helper.Mod.ident ~loc:target_loc
          (Location.mkloc (longident_of_string target_name) target_loc)
      in
      let module_binding =
        Ast_helper.Mb.mk ~loc:alias_loc
          (Location.mkloc (Some alias_name) alias_loc) module_expr
      in
      Ok [ Ast_helper.Str.module_ ~loc:alias_loc module_binding ]
  | Module_functor { functor_name; location; parameters; items } -> (
      match
        structure_of_items_with_sets requested_sets
          (module_path @ [ functor_name ]) items
      with
      | Error _ as err -> err
      | Ok body ->
          let module_expr =
            List.fold_right
              (fun parameter body ->
                let parameter_loc =
                  declaration_location parameter.parameter_location
                in
                let signature_loc =
                  declaration_location parameter.signature_location
                in
                let parameter =
                  Parsetree.Named
                    ( Location.mkloc (Some parameter.parameter_name) parameter_loc,
                      Ast_helper.Mty.ident ~loc:signature_loc
                        (Location.mkloc
                           (longident_of_string parameter.signature_name)
                           signature_loc) )
                in
                Ast_helper.Mod.functor_ ~loc:parameter_loc parameter body)
              parameters (Ast_helper.Mod.structure ~loc body)
          in
          let functor_loc = declaration_location location in
          let module_binding =
            Ast_helper.Mb.mk ~loc:functor_loc
              (Location.mkloc (Some functor_name) functor_loc) module_expr
          in
          Ok [ Ast_helper.Str.module_ ~loc:functor_loc module_binding ])
  | Module_apply
      { module_name; location; functor_name; functor_location; arguments } ->
      let functor_loc = declaration_location functor_location in
      let module_expr =
        List.fold_left
          (fun applied_functor argument ->
            let argument_loc = declaration_location argument.location in
            Ast_helper.Mod.apply ~loc:argument_loc applied_functor
              (Ast_helper.Mod.ident ~loc:argument_loc
                 (Location.mkloc (longident_of_string argument.module_name)
                    argument_loc)))
          (Ast_helper.Mod.ident ~loc:functor_loc
             (Location.mkloc (longident_of_string functor_name) functor_loc))
          arguments
      in
      let module_loc = declaration_location location in
      let module_binding =
        Ast_helper.Mb.mk ~loc:module_loc
          (Location.mkloc (Some module_name) module_loc) module_expr
      in
      Ok [ Ast_helper.Str.module_ ~loc:module_loc module_binding ]
  | Module_signature { signature_name; location; items } ->
      let signature_loc = declaration_location location in
      let module_type =
        Ast_helper.Mty.signature ~loc (List.map signature_item items)
      in
      Ok
        [ Ast_helper.Str.modtype ~loc:signature_loc
            (Ast_helper.Mtd.mk ~loc:signature_loc ~typ:module_type
               (named_loc signature_name signature_loc)) ]
  | Open_module { module_name; location } ->
      let module_loc = declaration_location location in
      let module_expr =
        Ast_helper.Mod.ident ~loc:module_loc
          (Location.mkloc (longident_of_string module_name) module_loc)
      in
      Ok
        [ Ast_helper.Str.open_ ~loc:module_loc
            (Ast_helper.Opn.mk ~loc:module_loc module_expr) ]
  | Include_module { module_name; location } ->
      let module_loc = declaration_location location in
      let module_expr =
        Ast_helper.Mod.ident ~loc:module_loc
          (Location.mkloc (longident_of_string module_name) module_loc)
      in
      Ok
        [ Ast_helper.Str.include_ ~loc:module_loc
            (Ast_helper.Incl.mk ~loc:module_loc module_expr) ]
  | Record_def
      {
        var_name;
        identity;
        type_id;
        type_name;
        type_parameters;
        set_module_name;
        fields;
        values;
      } ->
      record_definition
        ~emit_set:
          (set_module_requested requested_sets module_path set_module_name)
        ~emit_nullable_set:
          (set_module_requested requested_sets module_path
             (set_module_name ^ "_nullable"))
        var_name identity type_id type_name type_parameters set_module_name fields
        values
  | Projected_record_def
      {
        var_name;
        identity;
        type_id;
        type_name;
        type_parameters;
        set_module_name;
        fields;
        source;
      } ->
      projected_record_definition
        ~emit_set:
          (set_module_requested requested_sets module_path set_module_name)
        ~emit_nullable_set:
          (set_module_requested requested_sets module_path
             (set_module_name ^ "_nullable"))
        var_name identity type_id type_name type_parameters set_module_name fields
        source

and structure_of_items_with_sets ?(prune = true) requested_sets module_path items =
  let recursive_type_item = function
    | Type_def _ | Type_variant _ -> true
    | _ -> false
  in
  let rec take_recursive_type_items acc = function
    | item :: rest when recursive_type_item item ->
        take_recursive_type_items (item :: acc) rest
    | rest -> (List.rev acc, rest)
  in
  let type_item_name = function
    | Type_def { type_name; _ } | Type_variant { type_name; _ } ->
        type_name
    | _ -> invalid_arg "expected a recursive type item"
  in
  let type_item_references = function
    | Type_def { fields; _ } ->
        List.map (fun (field : Types.field) -> field.ty) fields
    | Type_variant { constructors; _ } ->
        List.concat_map
          (fun (constructor : variant_constructor) ->
            constructor.payload_types @ Option.to_list constructor.result_type)
          constructors
    | _ -> []
  in
  let mutually_recursive_group items =
    let names = List.map type_item_name items in
    let dependencies item =
      let references = type_item_references item in
      List.filter
        (fun name ->
          List.exists (fun reference -> type_mentions name reference) references)
        names
    in
    let graph =
      List.map
        (fun item -> (type_item_name item, dependencies item))
        items
    in
    let rec reachable visited source target =
      if source = target then true
      else if String_set.mem source visited then false
      else
        let visited = String_set.add source visited in
        List.assoc_opt source graph
        |> Option.value ~default:[]
        |> List.exists (fun dependency ->
               reachable visited dependency target)
    in
    match items with
    | [] -> ([], [])
    | first :: rest ->
        let first_name = type_item_name first in
        let mutually_recursive item =
          let name = type_item_name item in
          reachable String_set.empty first_name name
          && reachable String_set.empty name first_name
        in
        let group, remaining = List.partition mutually_recursive rest in
        (first :: group, remaining)
  in
  let compile_recursive_type_group items =
    let rec compile declarations trailing_definitions = function
      | [] ->
          let declaration_loc =
            match declarations with
            | declaration :: _ -> declaration.ptype_loc
            | [] -> loc
          in
          Ok
            (Ast_helper.Str.type_ ~loc:declaration_loc Recursive
               (List.rev declarations)
            :: List.concat (List.rev trailing_definitions))
      | item :: rest -> (
          match structure_of_item_with_sets requested_sets module_path item with
          | Error _ as err -> err
          | Ok ({ pstr_desc = Pstr_type (_, [ declaration ]); _ } :: trailing) ->
              compile (declaration :: declarations)
                (trailing :: trailing_definitions) rest
          | Ok _ ->
              Error.error ~code:Error_code.Internal
                "internal error: recursive type item did not emit one declaration")
    in
    compile [] [] items
  in
  let rec loop acc = function
    | [] ->
        let structure = List.concat (List.rev acc) in
        Ok (if prune then remove_unused_anonymous_types structure else structure)
    | Group grouped_items :: rest ->
        loop acc (grouped_items @ rest)
    | item :: rest when recursive_type_item item ->
        let type_items, rest =
          take_recursive_type_items [] (item :: rest)
        in
        let group, remaining_types =
          mutually_recursive_group type_items
        in
        if List.length group < 2 then
          (match structure_of_item_with_sets requested_sets module_path item with
          | Error _ as err -> err
          | Ok structure ->
              loop (structure :: acc)
                (List.tl type_items @ rest))
        else
          (match compile_recursive_type_group group with
          | Error _ as err -> err
          | Ok structure ->
              loop (structure :: acc) (remaining_types @ rest))
    | item :: rest -> (
        match structure_of_item_with_sets requested_sets module_path item with
        | Error _ as err -> err
        | Ok structure -> loop (structure :: acc) rest)
  in
  loop [] items

let rec root_declared_set_modules modules items =
  List.fold_left
    (fun modules -> function
      | Type_def { type_name; type_parameters = []; _ } ->
          let set_module_name = "Set_" ^ type_name in
          modules
          |> String_map.add set_module_name ()
          |> String_map.add (set_module_name ^ "_nullable") ()
      | Record_def { set_module_name; _ }
      | Projected_record_def { set_module_name; _ } ->
          modules
          |> String_map.add set_module_name ()
          |> String_map.add (set_module_name ^ "_nullable") ()
      | Group items -> root_declared_set_modules modules items
      | Foreign_binding _ | Type_def _ | Value_binding _ | Recursive_value_binding _
      | Recursive_value_bindings _ | Deferred_value_binding _
      | Opaque_type _ | Polymorphic_holder_type _ | Comment _ | Type_alias _ | Type_variant _
      | Module_def _ | Module_alias _ | Module_functor _ | Module_apply _
      | Module_signature _ | Open_module _ | Include_module _ ->
          modules)
    modules items

let missing_root_set_definitions requested_sets items =
  let declared_sets = root_declared_set_modules String_map.empty items in
  String_map.fold
    (fun module_name element_ty definitions ->
      if
        String.contains module_name '.'
        || String_map.mem module_name declared_sets
      then definitions
      else
        match element_ty with
        | Types.TNamed_record _
        | Types.TNullable (Types.TNamed_record _)
        | Types.TOcaml_app ("option", [ Types.TNamed_record _ ]) ->
            set_module_definition module_name element_ty :: definitions
        | _ when String.starts_with ~prefix:"Lg_static_set_" module_name ->
            set_module_definition module_name element_ty :: definitions
        | _ -> definitions)
    requested_sets []

let structure_of_items items =
  let requested_sets =
    collect_set_modules_from_items [] String_map.empty items
  in
  match structure_of_items_with_sets requested_sets [] items with
  | Error _ as error -> error
  | Ok structure ->
      Ok (missing_root_set_definitions requested_sets items @ structure)

let relocate_structure location structure =
  let inherited_location parent current =
    if current.Location.loc_ghost then parent else current
  in
  let rec mapper location =
    { Ast_mapper.default_mapper with
      location = (fun _ current -> inherited_location location current);
      type_declaration = (fun _ declaration ->
        let nested = mapper (inherited_location location declaration.ptype_loc) in
        Ast_mapper.default_mapper.type_declaration nested declaration);
      label_declaration = (fun _ declaration ->
        let nested = mapper (inherited_location location declaration.pld_loc) in
        Ast_mapper.default_mapper.label_declaration nested declaration);
      constructor_declaration = (fun _ declaration ->
        let nested = mapper (inherited_location location declaration.pcd_loc) in
        Ast_mapper.default_mapper.constructor_declaration nested declaration);
    }
  in
  let mapper = mapper location in
  mapper.structure mapper structure

let requested_sets_from_located_items items =
  items
  |> List.map snd
  |> collect_set_modules_from_items [] String_map.empty

let requested_set_modules_from_located_items items =
  requested_sets_from_located_items items
  |> String_map.bindings |> List.map fst

let structure_of_located_items_excluding excluded_sets items =
  let plain_items = List.map snd items in
  let requested_sets =
    collect_set_modules_from_items [] String_map.empty plain_items
    |> String_map.filter (fun module_name _ ->
           not (String_set.mem module_name excluded_sets))
  in
  let prefix = missing_root_set_definitions requested_sets plain_items in
  let rec flatten_group_items = function
    | Group items -> List.concat_map flatten_group_items items
    | item -> [ item ]
  in
  let type_item = function
    | Type_def _ | Type_variant _ -> true
    | _ -> false
  in
  let deferrable_type_region_item = function
    | Type_def _ | Type_variant _ | Value_binding _
    | Recursive_value_binding _ | Recursive_value_bindings _
    | Deferred_value_binding _ | Comment _ ->
        true
    | Opaque_type _ | Foreign_binding _ | Polymorphic_holder_type _ | Type_alias _ | Record_def _
    | Projected_record_def _ | Module_def _ | Module_alias _
    | Module_functor _ | Module_apply _ | Module_signature _
    | Open_module _ | Include_module _ | Group _ ->
        false
  in
  let split_type_region item =
    let items = flatten_group_items item in
    if List.for_all deferrable_type_region_item items then
      let type_items, trailing_items = List.partition type_item items in
      Some (type_items, trailing_items)
    else None
  in
  let recursive_type_items item =
    match split_type_region item with
    | Some (( _ :: _ as type_items), trailing_items) ->
        Some (type_items, trailing_items)
    | Some ([], _) | None -> None
  in
  let rec take_recursive_type_items acc = function
    | (location, item) :: rest -> (
        match split_type_region item with
        | Some (type_items, trailing_items) ->
            take_recursive_type_items
              ((location, type_items, trailing_items) :: acc)
              rest
        | None -> (List.rev acc, (location, item) :: rest))
    | [] -> (List.rev acc, [])
  in
  let rec loop acc = function
    | [] ->
        Ok
          (remove_unused_anonymous_types
             (prefix @ List.concat (List.rev acc)))
    | ((location, item) :: rest) as remaining -> (
        match recursive_type_items item with
        | Some _ ->
            let located_type_items, rest =
              take_recursive_type_items [] remaining
            in
            let type_items =
              List.concat_map
                (fun (_, type_items, _) -> type_items)
                located_type_items
            in
            let trailing_items =
              List.concat_map
                (fun (_, _, trailing_items) -> trailing_items)
                located_type_items
            in
            (match
               structure_of_items_with_sets ~prune:false requested_sets []
                 type_items
             with
            | Error _ as err -> err
            | Ok type_structure -> (
                match
                  structure_of_items_with_sets ~prune:false requested_sets []
                    trailing_items
                with
                | Error _ as err -> err
                | Ok trailing_structure ->
                    loop
                      (relocate_structure location
                         (type_structure @ trailing_structure)
                      :: acc)
                      rest))
        | None -> (
            match structure_of_item_with_sets requested_sets [] item with
            | Error _ as err -> err
            | Ok structure ->
                loop (relocate_structure location structure :: acc)
                  rest))
  in
  loop [] items

let structure_of_located_items items =
  structure_of_located_items_excluding String_set.empty items

let structure_of_incremental_located_items_with_modules
    ~previous_set_modules items =
  structure_of_located_items_excluding
    (String_set.of_list previous_set_modules)
    items

let structure_of_incremental_located_items ~previous_items items =
  structure_of_incremental_located_items_with_modules
    ~previous_set_modules:
      (requested_set_modules_from_located_items previous_items)
    items

let print_implementation ?(reserved_modules = []) structure =
  let mapper =
    {
      Ast_mapper.default_mapper with
      attributes =
        (fun _mapper attributes ->
          List.filter
            (fun attribute ->
              let name = attribute.Parsetree.attr_name.txt in
              name <> "lg.node_id" && name <> "lg.origin")
            attributes);
    }
  in
  let structure = mapper.structure mapper structure in
  let buffer = Buffer.create 4096 in
  let formatter = Format.formatter_of_buffer buffer in
  Format.pp_set_margin formatter 100;
  Format.fprintf formatter "%a@." Pprintast.structure structure;
  Format.pp_print_flush formatter ();
  let source = Buffer.contents buffer in
  let declaration name target =
    "open struct module " ^ name ^ " = " ^ target ^ " end\n"
  in
  let occupied_modules = Hashtbl.create 16 in
  let add name = Hashtbl.replace occupied_modules name () in
  List.iter add reserved_modules;
  let rec path = function
    | Longident.Lident name -> add name
    | Ldot (parent, _) -> path parent.txt
    | Lapply (left, right) -> path left.txt; path right.txt in
  let parameter = function
    | Parsetree.Named (name, _) -> Option.iter add name.txt
    | Unit -> () in
  let base = Ast_iterator.default_iterator in
  let iterator = {base with
    module_binding = (fun self binding -> Option.iter add binding.Parsetree.pmb_name.txt; base.module_binding self binding);
    module_expr = (fun self expression ->
      (match expression.Parsetree.pmod_desc with Pmod_ident name -> path name.txt | Pmod_functor (argument, _) -> parameter argument | _ -> ());
      base.module_expr self expression);
    module_type = (fun self ty ->
      (match ty.Parsetree.pmty_desc with Pmty_ident name | Pmty_alias name -> path name.txt | Pmty_functor (argument, _) -> parameter argument | _ -> ());
      base.module_type self ty);
    expr = (fun self expression ->
      (match expression.Parsetree.pexp_desc with Pexp_ident {txt = Ldot (parent, _); _} | Pexp_construct ({txt = Ldot (parent, _); _}, _) -> path parent.txt | _ -> ());
      base.expr self expression);
    typ = (fun self ty ->
      (match ty.Parsetree.ptyp_desc with Ptyp_constr ({txt = Ldot (parent, _); _}, _) -> path parent.txt | _ -> ());
      base.typ self ty)} in
  iterator.structure iterator structure;
  let aliases =
    [
      (let name = "S" in
       ("Lg_runtime.Lg_seq", name, declaration name "Lg_runtime.Lg_seq"));
      (let name = "M" in
       ("Lg_runtime.Lg_map", name, declaration name "Lg_runtime.Lg_map"));
      (let name = "E" in
       ("Lg_runtime.Lg_exn", name, declaration name "Lg_runtime.Lg_exn"));
      (let name = "T" in
       ("Lg_runtime.Lg_set", name, declaration name "Lg_runtime.Lg_set"));
      (let name = "V" in
       ("Rrbvec", name, declaration name "Rrbvec"));
      (let name = "B" in
       ("Stdlib", name, declaration name "Stdlib"));
    ] |> List.filter (fun (_, alias, _) -> not (Hashtbl.mem occupied_modules alias))
  in
  let identifier_char = function
    | 'a' .. 'z' | 'A' .. 'Z' | '0' .. '9' | '_' | '\'' -> true
    | _ -> false
  in
  let source_length = String.length source in
  let compact = Buffer.create source_length in
  let used_aliases = Hashtbl.create (List.length aliases) in
  let matching_alias index =
    if
      index > 0
      && (identifier_char source.[index - 1] || source.[index - 1] = '.')
    then None
    else
      List.find_opt
        (fun (name, _, _) ->
          let length = String.length name in
          index + length <= source_length
          && String.sub source index length = name
          &&
          let next = index + length in
          next = source_length || not (identifier_char source.[next]))
        aliases
  in
  let rec rewrite index in_string escaped =
    if index >= source_length then Buffer.contents compact
    else
      let current = source.[index] in
      if in_string then (
        Buffer.add_char compact current;
        if escaped then rewrite (index + 1) true false
        else if current = '\\' then rewrite (index + 1) true true
        else rewrite (index + 1) (current <> '"') false)
      else if current = '"' then (
        Buffer.add_char compact current;
        rewrite (index + 1) true false)
      else
        match matching_alias index with
        | Some (name, alias, declaration) ->
            Hashtbl.replace used_aliases alias declaration;
            Buffer.add_string compact alias;
            rewrite (index + String.length name) false false
        | None ->
            Buffer.add_char compact current;
            rewrite (index + 1) false false
  in
  let compact_source = rewrite 0 false false in
  let alias_declarations =
    aliases
    |> List.filter_map (fun (_, alias, declaration) ->
           if Hashtbl.mem used_aliases alias then Some declaration else None)
    |> String.concat ""
  in
  alias_declarations ^ compact_source
