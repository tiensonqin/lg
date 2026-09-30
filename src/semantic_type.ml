type metavariable = { id : int; location : Location.t option }

type ty =
  | TInt
  | TFloat
  | TChar
  | TString
  | TRegex
  | TMap_keys
  | TSymbol
  | TKeyword
  | TBool
  | TUnit
  | TNil
  | TNullable of ty
  | TUnknown
  | TMeta of metavariable
  | TVar of string
  | TOcaml of string
  | TOcaml_app of string * ty list
  | TConstraint of constraint_
  | TTuple of ty list
  | TArray of ty
  | TRef of ty
  | TList of ty
  | TVector of ty
  | TSet of ty
  | TSeq of ty
  | TFn of ty list * ty
  | TOverloaded_fn of fn_arity list
  | TPoly_variant of variant_row
  | TRecord of field list
  | TNamed_record of named_record
  | TCompiler of compiler_marker

(* Closed set of compiler-internal type markers. These replace the
   reserved __lg_* names that used to be smuggled through TOcaml /
   TOcaml_app so user-facing OCaml names can never collide with them. *)
and compiler_marker =
  | Module_package of string
  | Constant_function of ty
  | Reify_self_method of ty
  | Reify_protocol_payload of string * ty * ty
  | Next_seq of ty
  | Reversible_next_seq of ty
  | Maybe_reduced_callback of ty
  | Optional_map_adapter of ty * ty
  | Named_record_marker of string
  | Named_record_app_marker of string * ty list
  | Protocol_marker
  | Date_millis

and row_bound = Exact_row | Lower_row | Upper_row | Bounded_row of string list
and variant_row = { tags : (string * ty option) list; bound : row_bound }
and seqable_requirement = Required | Optional | Optional_sequential

and constraint_ =
  | Seqable_constraint of {
      requirement : seqable_requirement;
      element : ty;
      storage : ty;
    }
  | Contains_constraint of { key : ty; storage : ty }
  | Truthy_constraint of ty
  | Nil_predicate_constraint of ty
  | Printable_constraint of ty
  | Exception_data_constraint of ty
  | Hashable_constraint of ty
  | Comparable_constraint of ty
  | Array_index_constraint of ty
  | Symbol_predicate_constraint of ty
  | Open_boundary_constraint of ty
  | Protocol_constraint of {
      protocol_id : Protocol_id.t;
      witness : ty;
      value : ty;
      guarded : bool;
    }

and field = {
  keyword : string;
  ocaml_name : string;
  ty : ty;
  quantified : string list;
  mutable_ : bool;
  runtime_map : bool;
  location : Location.t option;
}

and named_record = {
  type_id : Type_id.t;
  nominal : bool;
  extensible : bool;
  type_name : string;
  type_parameters : string list;
  type_arguments : ty list;
  set_module_name : string;
  fields : field list;
}

and fn_arity = {
  fixed_params : ty list;
  rest_param : ty option;
  return_ty : ty;
}

type scheme_variable =
  | Declared_variable of string
  | Inferred_variable of { metavariable_id : int; name : string }

type scheme = { quantified : scheme_variable list; body : ty }

let constraint_children = function
  | Seqable_constraint { element; storage; _ } -> [ element; storage ]
  | Contains_constraint { key; storage } -> [ key; storage ]
  | Truthy_constraint value
  | Nil_predicate_constraint value
  | Printable_constraint value
  | Exception_data_constraint value
  | Hashable_constraint value
  | Comparable_constraint value
  | Array_index_constraint value
  | Symbol_predicate_constraint value
  | Open_boundary_constraint value ->
      [ value ]
  | Protocol_constraint { witness; value; _ } -> [ witness; value ]

let map_constraint map constraint_ =
  let map_one build value =
    let mapped = map value in
    if mapped == value then constraint_ else build mapped
  in
  let map_two build left right =
    let mapped_left = map left in
    let mapped_right = map right in
    if mapped_left == left && mapped_right == right then constraint_
    else build mapped_left mapped_right
  in
  match constraint_ with
  | Seqable_constraint ({ element; storage; _ } as seqable) ->
      map_two
        (fun element storage ->
          Seqable_constraint { seqable with element; storage })
        element storage
  | Contains_constraint { key; storage } ->
      map_two
        (fun key storage -> Contains_constraint { key; storage })
        key storage
  | Truthy_constraint value ->
      map_one (fun value -> Truthy_constraint value) value
  | Nil_predicate_constraint value ->
      map_one (fun value -> Nil_predicate_constraint value) value
  | Printable_constraint value ->
      map_one (fun value -> Printable_constraint value) value
  | Exception_data_constraint value ->
      map_one (fun value -> Exception_data_constraint value) value
  | Hashable_constraint value ->
      map_one (fun value -> Hashable_constraint value) value
  | Comparable_constraint value ->
      map_one (fun value -> Comparable_constraint value) value
  | Array_index_constraint value ->
      map_one (fun value -> Array_index_constraint value) value
  | Symbol_predicate_constraint value ->
      map_one (fun value -> Symbol_predicate_constraint value) value
  | Open_boundary_constraint value ->
      map_one (fun value -> Open_boundary_constraint value) value
  | Protocol_constraint ({ witness; value; _ } as protocol) ->
      map_two
        (fun witness value ->
          Protocol_constraint { protocol with witness; value })
        witness value

let map_compiler_marker map marker =
  let map_one build value =
    let mapped = map value in
    if mapped == value then marker else build mapped
  in
  let map_two build left right =
    let mapped_left = map left in
    let mapped_right = map right in
    if mapped_left == left && mapped_right == right then marker
    else build mapped_left mapped_right
  in
  match marker with
  | Module_package _ | Named_record_marker _ | Protocol_marker | Date_millis ->
      marker
  | Named_record_app_marker (name, args) ->
      let mapped = List.map map args in
      if
        List.length mapped = List.length args
        && List.for_all2 ( == ) mapped args
      then marker
      else Named_record_app_marker (name, mapped)
  | Constant_function ty -> map_one (fun ty -> Constant_function ty) ty
  | Reify_self_method ty -> map_one (fun ty -> Reify_self_method ty) ty
  | Reify_protocol_payload (id, methods, rest) ->
      map_two
        (fun methods rest -> Reify_protocol_payload (id, methods, rest))
        methods rest
  | Next_seq ty -> map_one (fun ty -> Next_seq ty) ty
  | Reversible_next_seq ty ->
      map_one (fun ty -> Reversible_next_seq ty) ty
  | Maybe_reduced_callback ty ->
      map_one (fun ty -> Maybe_reduced_callback ty) ty
  | Optional_map_adapter (key, value) ->
      map_two
        (fun key value -> Optional_map_adapter (key, value))
        key value

let replace_compiler_marker_children marker children =
  let remaining = ref children in
  let next _ =
    match !remaining with
    | ty :: rest ->
        remaining := rest;
        ty
    | [] -> invalid_arg "Semantic_type.replace_compiler_marker_children"
  in
  let marker = map_compiler_marker next marker in
  match !remaining with
  | [] -> marker
  | _ :: _ -> invalid_arg "Semantic_type.replace_compiler_marker_children"

let fold_map_compiler_marker f acc = function
  | ( Module_package _ | Named_record_marker _ | Protocol_marker | Date_millis
    ) as marker ->
      (acc, marker)
  | Named_record_app_marker (name, args) ->
      let acc, mapped =
        List.fold_left
          (fun (acc, mapped) arg ->
            let acc, arg = f acc arg in
            (acc, arg :: mapped))
          (acc, []) args
      in
      (acc, Named_record_app_marker (name, List.rev mapped))
  | Constant_function ty ->
      let acc, ty = f acc ty in
      (acc, Constant_function ty)
  | Reify_self_method ty ->
      let acc, ty = f acc ty in
      (acc, Reify_self_method ty)
  | Reify_protocol_payload (id, methods, rest) ->
      let acc, methods = f acc methods in
      let acc, rest = f acc rest in
      (acc, Reify_protocol_payload (id, methods, rest))
  | Next_seq ty ->
      let acc, ty = f acc ty in
      (acc, Next_seq ty)
  | Reversible_next_seq ty ->
      let acc, ty = f acc ty in
      (acc, Reversible_next_seq ty)
  | Maybe_reduced_callback ty ->
      let acc, ty = f acc ty in
      (acc, Maybe_reduced_callback ty)
  | Optional_map_adapter (key, value) ->
      let acc, key = f acc key in
      let acc, value = f acc value in
      (acc, Optional_map_adapter (key, value))

let map_children map = function
  | TPoly_variant row ->
      TPoly_variant
        {
          row with
          tags =
            List.map
              (fun (tag, payload) -> (tag, Option.map map payload))
              row.tags;
        }
  | TNullable ty -> TNullable (map ty)
  | TCompiler marker -> TCompiler (map_compiler_marker map marker)
  | TOcaml_app (name, arguments) -> TOcaml_app (name, List.map map arguments)
  | TConstraint constraint_ -> TConstraint (map_constraint map constraint_)
  | TTuple types -> TTuple (List.map map types)
  | TArray ty -> TArray (map ty)
  | TRef ty -> TRef (map ty)
  | TList ty -> TList (map ty)
  | TVector ty -> TVector (map ty)
  | TSet ty -> TSet (map ty)
  | TSeq ty -> TSeq (map ty)
  | TFn (parameters, result) -> TFn (List.map map parameters, map result)
  | TOverloaded_fn arities ->
      TOverloaded_fn
        (List.map
           (fun arity ->
             {
               fixed_params = List.map map arity.fixed_params;
               rest_param = Option.map map arity.rest_param;
               return_ty = map arity.return_ty;
             })
           arities)
  | TRecord fields ->
      TRecord (List.map (fun field -> { field with ty = map field.ty }) fields)
  | TNamed_record record ->
      TNamed_record
        {
          record with
          type_arguments = List.map map record.type_arguments;
          fields =
            List.map
              (fun field -> { field with ty = map field.ty })
              record.fields;
        }
  | ( TInt | TFloat | TChar | TString | TRegex | TMap_keys | TSymbol | TKeyword
    | TBool | TUnit | TNil | TUnknown | TMeta _ | TVar _ | TOcaml _ ) as ty ->
      ty

(* Two markers share the old __lg_* type name exactly when their
   constructor and embedded names agree. *)
let compiler_marker_same_name left right =
  match (left, right) with
  | Module_package left, Module_package right -> String.equal left right
  | Reify_protocol_payload (left, _, _), Reify_protocol_payload (right, _, _)
    ->
      String.equal left right
  | Named_record_marker left, Named_record_marker right ->
      String.equal left right
  | Named_record_app_marker (left, _), Named_record_app_marker (right, _) ->
      String.equal left right
  | Constant_function _, Constant_function _
  | Reify_self_method _, Reify_self_method _
  | Next_seq _, Next_seq _
  | Reversible_next_seq _, Reversible_next_seq _
  | Maybe_reduced_callback _, Maybe_reduced_callback _
  | Optional_map_adapter _, Optional_map_adapter _
  | Protocol_marker, Protocol_marker
  | Date_millis, Date_millis ->
      true
  | _ -> false

let compiler_marker_children = function
  | Module_package _ | Named_record_marker _ | Protocol_marker | Date_millis ->
      []
  | Constant_function ty | Reify_self_method ty | Next_seq ty
  | Reversible_next_seq ty | Maybe_reduced_callback ty ->
      [ ty ]
  | Reify_protocol_payload (_, methods, rest) -> [ methods; rest ]
  | Optional_map_adapter (key, value) -> [ key; value ]
  | Named_record_app_marker (_, args) -> args
