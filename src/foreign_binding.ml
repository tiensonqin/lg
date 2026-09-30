open Ast

type ownership = Unspecified | Borrowed | Owned of string

type native_type = Int | Double | Bool | Char | String | Void | Pointer of native_type | Optional_pointer of native_type | Owned_pointer of native_type | Callback of native_type list * native_type | Retained_callback of native_type list * native_type

type native = {
  symbol : string;
  library : string option;
  parameters : native_type list;
  result : native_type;
  ownership : ownership;
}

type operation = Call | New | Send | Get | Set | Get_index | Set_index

type return_adapter = Direct | Nullable | Null | Undefined

type javascript = {
  symbol : string;
  module_name : string option;
  scope : string list;
  operation : operation;
  return_adapter : return_adapter;
  variadic : bool;
}

type object_options = { rename : (string * string) list; optional : string list }

type object_field = {
  source : Types.field;
  property : string;
  optional : bool;
  value_type : Types.ty;
}

type object_builder = { input : Types.ty; result : Types.ty; fields : object_field list }

type selection = Native_symbol of string * string option * bool * ownership | Release_selection | Callback_selection | JavaScript_symbol of javascript
  | Object_selection of object_options
  | Ocaml_primitive_selection of string

type backend = Native of native | Native_release | Native_callback_release | Native_callback of native_type list * native_type | JavaScript of javascript | JavaScript_object of object_builder
  | Ocaml_primitive of string

type t = {
  name : string;
  value_type : Types.ty;
  location : Location.t option;
  backend : backend;
}

let ( let* ) = Result.bind

let error form message =
  Error.error ~code:Error_code.Unresolved ~title:"INVALID FOREIGN BINDING"
    ?location:(Source_context.find form) message

let options ~target form =
  match form with
  | FMap entries ->
      let rec collect seen = function
        | [] -> Ok seen
        | (FKeyword key, value) :: rest ->
            if List.mem_assoc key seen then
              error form ("duplicate FFI option " ^ key)
            else if not (List.mem key [ ":native"; ":js"; ":ocaml"; ":library"; ":module"; ":scope"; ":kind"; ":return"; ":variadic"; ":rename"; ":optional"; ":callbacks"; ":ownership"; ":release" ]) then
              error form ("unknown FFI option " ^ key)
            else collect ((key, value) :: seen) rest
        | _ -> error form "FFI option keys must be keywords"
      in
      let* options = collect [] entries in
      let nonempty_string = function
        | FString value when value <> "" && not (String.contains value (Char.chr 0)) -> Ok value
        | _ -> error form "FFI names and library paths must be a nonempty string without NUL"
      in
      let optional_string key =
        match List.assoc_opt key options with
        | None -> Ok None
        | Some value -> Result.map Option.some (nonempty_string value)
      in
      (match List.assoc_opt ":ocaml" options with
       | Some value ->
           if List.mem_assoc ":native" options || List.mem_assoc ":js" options then
             error form "ffi requires exactly one :native, :js, or :ocaml selector"
           else if List.length options <> 1 then
             error form "OCaml primitive FFI does not accept other options"
           else if target <> Target.Native then
             error form "OCaml primitive FFI requires the native target"
           else
             let* symbol = nonempty_string value in
             let identifier_start = function
               | 'a' .. 'z' | 'A' .. 'Z' | '_' -> true | _ -> false in
             let identifier_char ch = identifier_start ch || (ch >= '0' && ch <= '9') in
             if not (identifier_start symbol.[0] && String.for_all identifier_char symbol) then
               error form "OCaml primitive symbol must be a C identifier"
             else Ok (Ocaml_primitive_selection symbol)
       | None ->
      (match List.assoc_opt ":native" options, List.assoc_opt ":js" options with
       | Some (FKeyword ":callback"), None ->
           if target <> Target.Native then error form "callback FFI requires the native target"
           else if List.length options <> 1 then error form "callback FFI does not accept other options"
           else Ok Callback_selection
       | Some (FKeyword ":release"), None ->
           if target <> Target.Native then error form "release FFI requires the native target"
           else if List.length options <> 1 then error form "release FFI does not accept other options"
           else Ok Release_selection
       | Some symbol, None ->
           let* symbol = nonempty_string symbol in
           let* library = optional_string ":library" in
           let* ownership = match List.assoc_opt ":ownership" options, List.assoc_opt ":release" options with
             | None, None -> Ok Unspecified
             | Some (FKeyword ":borrowed"), None -> Ok Borrowed
             | Some (FKeyword ":owned"), Some symbol ->
                 Result.map (fun symbol -> Owned symbol) (nonempty_string symbol)
             | _ -> error form "native FFI ownership requires :borrowed or :owned with a :release symbol"
           in
           let* callbacks = match List.assoc_opt ":callbacks" options with
             | None -> Ok false
             | Some (FKeyword ":call") -> Ok true
             | _ -> error form "native FFI :callbacks supports only :call; retained callbacks require managed handles"
           in
           if List.mem_assoc ":module" options || List.mem_assoc ":scope" options
              || List.mem_assoc ":kind" options || List.mem_assoc ":return" options
              || List.mem_assoc ":variadic" options || List.mem_assoc ":rename" options
              || List.mem_assoc ":optional" options then
             error form "native FFI does not accept JavaScript module or scope options"
           else if target <> Target.Native then
             error form "this FFI binding requires the native target; use reader conditionals for shared source"
           else Ok (Native_symbol (symbol, library, callbacks, ownership))
       | None, Some (FKeyword ":object") ->
           let* () =
             if target <> Target.Melange then
               error form "object FFI requires the Melange target"
             else if List.exists (fun (key, _) ->
               not (List.mem key [":js"; ":rename"; ":optional"])) options then
               error form "object FFI cannot use call, scope, or return adapters"
             else Ok ()
           in
           let* rename = match List.assoc_opt ":rename" options with
             | None -> Ok []
             | Some (FMap fields) ->
                 List.fold_left (fun acc (key, value) ->
                   let* acc = acc in
                   match key, value with
                   | FKeyword key, FString value when value <> "" && not (String.contains value (Char.chr 0)) ->
                       if List.mem_assoc key acc then error form "duplicate object rename field"
                       else Ok ((key, value) :: acc)
                   | _ -> error form "object :rename requires keyword fields and nonempty string names") (Ok []) fields
             | _ -> error form "object :rename must be a map"
           in
           let* optional = match List.assoc_opt ":optional" options with
             | None -> Ok []
             | Some (FVector fields) ->
                 List.fold_left (fun acc field ->
                   let* acc = acc in
                   match field with
                   | FKeyword key when not (List.mem key acc) -> Ok (key :: acc)
                   | _ -> error form "object :optional requires distinct keyword fields") (Ok []) fields
             | _ -> error form "object :optional must be a vector"
           in
           Ok (Object_selection { rename; optional })
       | None, Some selector ->
           let* () = if List.mem_assoc ":ownership" options || List.mem_assoc ":release" options then
             error form ":ownership is only supported by native FFI" else Ok () in
           let* () = if List.mem_assoc ":callbacks" options then
             error form ":callbacks is only supported by native FFI" else Ok () in
           let* () = if List.mem_assoc ":rename" options || List.mem_assoc ":optional" options
             then error form "object field options require :js :object" else Ok () in
           let* symbol, operation =
             match selector with
             | FKeyword (":get-index" | ":set-index" as kind) ->
                 if List.mem_assoc ":kind" options then
                   error form "indexed JS selectors cannot also specify :kind"
                 else Ok ("", if kind = ":get-index" then Get_index else Set_index)
             | _ ->
                 let* symbol = nonempty_string selector in
                 let* operation = match List.assoc_opt ":kind" options with
                   | None | Some (FKeyword ":call") -> Ok Call
                   | Some (FKeyword ":new") -> Ok New
                   | Some (FKeyword ":send") -> Ok Send
                   | Some (FKeyword ":get") -> Ok Get
                   | Some (FKeyword ":set") -> Ok Set
                   | _ -> error form "unsupported JavaScript FFI :kind"
                 in Ok (symbol, operation)
           in
           let* return_adapter = match List.assoc_opt ":return" options with
             | None -> Ok Direct
             | Some (FKeyword ":nullable") -> Ok Nullable
             | Some (FKeyword ":null") -> Ok Null
             | Some (FKeyword ":undefined") -> Ok Undefined
             | _ -> error form "unsupported JavaScript FFI :return adapter"
           in
           let* variadic = match List.assoc_opt ":variadic" options with
             | None -> Ok false
             | Some (FBool value) -> Ok value
             | _ -> error form "JavaScript FFI :variadic must be a boolean"
           in
           let* module_name = optional_string ":module" in
           let* scope =
             match List.assoc_opt ":scope" options with
             | None -> Ok []
             | Some (FVector names) ->
                 let rec loop = function
                   | [] -> Ok []
                   | FString name :: rest when name <> "" && not (String.contains name (Char.chr 0)) ->
                       let* rest = loop rest in Ok (name :: rest)
                   | _ -> error form "FFI scope requires nonempty property name strings"
                 in loop names
             | Some _ -> error form "FFI scope must be a vector of property name strings"
           in
           if List.mem_assoc ":library" options then
             error form ":library is only supported by native FFI"
           else if target <> Target.Melange then
             error form "this FFI binding requires the Melange target; use reader conditionals for shared source"
           else if List.mem operation [Send; Get; Set; Get_index; Set_index]
                   && (Option.is_some module_name || scope <> []) then
             error form "receiver operations cannot select a module or scope"
           else Ok (JavaScript_symbol { symbol; module_name; scope; operation; return_adapter; variadic })
       | _ -> error form "ffi requires exactly one :native, :js, or :ocaml selector"))
  | _ -> error form "ffi options must be a map"

let native_abi_type ~callbacks ~ownership ~callback ~parameter form ty =
  let rec pointee form = function
    | Types.TInt -> Ok Int | Types.TFloat -> Ok Double
    | Types.TBool -> Ok Bool | Types.TChar -> Ok Char | Types.TUnit -> Ok Void
    | Types.TOcaml_app ("Ctypes.ptr", [inner]) ->
        Result.map (fun inner -> Pointer inner) (pointee form inner)
    | _ -> error form "unsupported native pointer pointee type"
  in
  let rec native_type ~callback ~parameter form = function
    | Types.TInt -> Ok Int
    | Types.TFloat -> Ok Double
    | Types.TBool -> Ok Bool
    | Types.TString when parameter -> Ok String
    | Types.TString -> error form "native FFI string result requires an explicit ownership adapter"
    | Types.TUnit when not parameter -> Ok Void
    | Types.TUnit -> error form "native FFI unit parameter is invalid; use [] for zero arguments"
    | Types.TOcaml_app ("Lg_ffi.Owned_pointer.t", [inner]) ->
        if callback then error form "owned pointer callbacks require a separate lifetime adapter"
        else if not parameter && (match ownership with Owned _ -> false | _ -> true) then
          error form "owned pointer result requires :ownership :owned and :release"
        else Result.map (fun inner -> Owned_pointer inner) (pointee form inner)
    | Types.TOcaml_app ("Ctypes.ptr", [inner]) ->
        if not parameter && ownership <> Borrowed then error form "pointer results require :ownership :borrowed"
        else Result.map (fun inner -> Pointer inner) (pointee form inner)
    | Types.TNullable (Types.TOcaml_app ("Ctypes.ptr", [inner]))
    | Types.TOcaml_app ("option", [Types.TOcaml_app ("Ctypes.ptr", [inner])]) ->
        if not parameter && ownership <> Borrowed then error form "pointer results require :ownership :borrowed"
        else Result.map (fun inner -> Optional_pointer inner) (pointee form inner)
    | (Types.TFn (args, result)
      | Types.TOcaml_app ("Lg_ffi.Callback.t", [Types.TFn (args, result)])) as ty
      when parameter && not callback ->
        let retained = match ty with Types.TOcaml_app _ -> true | _ -> false in
        if not callbacks && not retained then error form "native callback parameters require :callbacks :call"
        else
          let* args = List.fold_left (fun acc ty ->
            let* acc = acc in
            let* ty = native_type ~callback:true ~parameter:true form ty in
            Ok (ty :: acc)) (Ok []) args in
          let* result = native_type ~callback:true ~parameter:false form result in
          Ok (if retained then Retained_callback (List.rev args, result)
              else Callback (List.rev args, result))
    | Types.TFn _ when callback -> error form "nested callback types are not supported"
    | ty -> error form ("unsupported native FFI type " ^ Types.source_name ty)

  in native_type ~callback ~parameter form ty


let parse ~target ~resolve_type ~is_opaque ~name ~location parameters result option_form =
  let* selected = options ~target option_form in
  let resolve form =
    match form with
    | FKeyword keyword -> Result.map resolve_type (Type_annotation.of_keyword keyword)
    | _ -> error form "ffi expects a type keyword at every argument and result"
  in
  let rec resolve_arguments = function
    | [] -> Ok []
    | form :: rest ->
        let* ty = resolve form in
        let* rest = resolve_arguments rest in
        Ok (ty :: rest)
  in
  let* parameter_types = resolve_arguments parameters in
  let* result_type = resolve result in
  let* backend = match selected with
    | Ocaml_primitive_selection symbol ->
        let rec closed_type ty =
          if Types.contains_dynamic ty then false
          else match ty with
          | Types.TUnknown | Types.TMeta _ | Types.TVar _ | Types.TConstraint _
          | Types.TOverloaded_fn _ -> false
          | Types.TPoly_variant {bound; _} when bound <> Types.Exact_row -> false
          | _ ->
              let valid = ref true in
              ignore (Semantic_type.map_children (fun child ->
                if not (closed_type child) then valid := false;
                child) ty);
              !valid
        in
        if List.length parameter_types > 5 then
          error option_form "OCaml primitive FFI supports at most five parameters"
        else if List.exists (Types.equal Types.TUnit) parameter_types then
          error option_form "OCaml primitive unit parameter is invalid; use [] for zero arguments"
        else if not (List.for_all closed_type (result_type :: parameter_types)) then
          error option_form "OCaml primitive FFI requires closed static types"
        else Ok (Ocaml_primitive symbol)
    | Callback_selection ->
        (match parameter_types, result_type with
         | [Types.TFn _ as fn], Types.TOcaml_app ("Lg_ffi.Callback.t", [signature])
           when Types.equal fn signature ->
             let* descriptor = native_abi_type ~callbacks:true ~ownership:Unspecified
               ~callback:false ~parameter:true option_form fn in
             (match descriptor with Callback (args, result) -> Ok (Native_callback (args, result))
              | _ -> assert false)
         | _ -> error option_form "callback FFI requires one function and a callback result with the same signature")
    | Release_selection ->
        (match parameter_types, result_type with
         | [Types.TOcaml_app ("Lg_ffi.Owned_pointer.t", [_])], Types.TUnit -> Ok Native_release
         | [Types.TOcaml_app ("Lg_ffi.Callback.t", [Types.TFn _])], Types.TUnit -> Ok Native_callback_release
         | _ -> error option_form "release FFI requires one owned-pointer or callback argument and a unit result")
    | Native_symbol (symbol, library, callbacks, ownership) ->
        let native_type = native_abi_type ~callbacks ~ownership in
        let rec arguments forms types = match forms, types with
          | form :: forms, ty :: types ->
              let* value = native_type ~callback:false ~parameter:true form ty in
              let* rest = arguments forms types in Ok (value :: rest)
          | [], [] -> Ok []
          | _ -> assert false
        in
        let* parameters = arguments parameters parameter_types in
        let* result = native_type ~callback:false ~parameter:false result result_type in
        let* () = match ownership, result with
          | Owned _, Owned_pointer _ -> Ok ()
          | Owned _, _ -> error option_form "owned ownership requires an owned-pointer result"
          | _ -> Ok () in
        Ok (Native { symbol; library; parameters; result; ownership })
    | Object_selection options ->
        let* input, fields = match parameter_types with
          | [Types.TNamed_record _ as input] ->
              (match Types.record_fields input with
               | Some fields -> Ok (input, fields)
               | None -> assert false)
          | _ -> error option_form "object FFI requires one declared record argument"
        in
        let* () = if is_opaque result_type then Ok ()
          else error result "object FFI must return an opaque extern-type" in
        let keys = List.map (fun (field : Types.field) -> field.keyword) fields in
        let* () = if List.for_all (fun key -> List.mem key keys)
          (options.optional @ List.map fst options.rename) then Ok ()
          else error option_form "unknown object field in :rename or :optional" in
        let rec validate ty = match ty with
          | Types.TInt | Types.TFloat | Types.TBool | Types.TString -> true
          | Types.TArray element -> validate element
          | ty -> is_opaque ty
        in
        let* fields = List.fold_left (fun acc (source : Types.field) ->
          let* acc = acc in
          let optional = List.mem source.keyword options.optional in
          let* value_type = match optional, source.ty with
            | true, Types.TNullable element
            | true, Types.TOcaml_app ("option", [element]) -> Ok element
            | true, _ -> error option_form "optional object field must have an option type"
            | false, ty -> Ok ty
          in
          let* () = if validate value_type then Ok ()
            else error option_form "unsupported object field type; option fields require :optional" in
          let property = match List.assoc_opt source.keyword options.rename with
            | Some name -> name
            | None -> String.sub source.keyword 1 (String.length source.keyword - 1)
          in
          if property = "__proto__" then
            error option_form "object property __proto__ has special JavaScript literal semantics"
          else if List.exists (fun field -> field.property = property) acc then
            error option_form "duplicate object property name"
          else Ok ({source; property; optional; value_type} :: acc)) (Ok []) fields in
        Ok (JavaScript_object {input; result = result_type; fields = List.rev fields})
    | JavaScript_symbol binding ->
        let rec validate_value form ty = match ty with
          | Types.TInt | Types.TFloat | Types.TBool | Types.TString -> Ok ()
          | Types.TArray element -> validate_value form element
          | ty when is_opaque ty -> Ok ()
          | ty -> error form ("unsupported JavaScript FFI type " ^ Types.source_name ty)
        in
        let validate_result form = function
          | Types.TUnit -> Ok ()
          | ty -> validate_value form ty
        in
        let validate_parameter form = function
          | Types.TUnit -> error form "JavaScript FFI unit parameter is invalid; use [] for zero arguments"
          | Types.TFn (arguments, result) ->
              let* () = List.fold_left (fun checked ty ->
                let* () = checked in validate_value form ty) (Ok ()) arguments in
              validate_result form result
          | ty -> validate_value form ty
        in
        let* () = List.fold_left2 (fun checked form ty ->
          let* () = checked in validate_parameter form ty)
          (Ok ()) parameters parameter_types in
        let* abi_result_type = match binding.return_adapter, result_type with
          | Direct, ty ->
              let* () = validate_result result ty in Ok ty
          | _, Types.TNullable element
          | _, Types.TOcaml_app ("option", [element]) ->
              let* () = validate_value result element in Ok element
          | _ -> error result "a nullable return adapter requires an option result type"
        in
        let* () =
          if not binding.variadic then Ok ()
          else match binding.operation, List.rev parameter_types with
            | (Call | New), Types.TArray _ :: _ -> Ok ()
            | Send, Types.TArray _ :: _ when List.length parameter_types >= 2 -> Ok ()
            | _ -> error option_form "variadic FFI requires a call and a final array parameter"
        in
        let receiver = function
          | Types.TString | Types.TArray _ -> true
          | ty -> is_opaque ty
        in
        let index = function Types.TInt | Types.TString -> true | _ -> false in
        let unit_result () =
          if Types.equal result_type Types.TUnit then Ok ()
          else error result "foreign setters must return unit"
        in
        let* () = match binding.operation, parameter_types with
          | Call, _ -> Ok ()
          | New, _ ->
              if is_opaque result_type then Ok ()
              else error result "foreign constructors must return an opaque extern-type"
          | Send, first :: _ when receiver first -> Ok ()
          | Get, [first] when receiver first -> Ok ()
          | Set, [first; _] when is_opaque first -> unit_result ()
          | Get_index, [Types.TArray element; Types.TInt] ->
              if Types.equal element abi_result_type then Ok ()
              else error result "indexed array reads must return the array element type"
          | Set_index, [Types.TArray element; Types.TInt; value] ->
              if not (Types.equal element value) then
                error option_form "indexed array writes must preserve the array element type"
              else unit_result ()
          | (Get_index | Set_index), Types.TArray _ :: _ ->
              error option_form "array index must be an int"
          | Get_index, [first; key] when receiver first && index key -> Ok ()
          | Set_index, [first; key; _] when is_opaque first && index key -> unit_result ()
          | (Get_index | Set_index), _ ->
              error option_form "indexed FFI requires a receiver, an int or string index, and a value for writes"
          | _ -> error option_form "invalid foreign receiver operation signature"
        in
        Ok (JavaScript binding)
  in
  Ok { name; value_type = Types.TFn (parameter_types, result_type); location; backend }

let rec native_descriptor (ty : native_type) =
  let open Semantic_ir in
  match ty with
    | Int -> Ident "Ctypes.int"
    | Double -> Ident "Ctypes.double"
    | Bool -> Ident "Ctypes.bool"
    | Char -> Ident "Ctypes.char"
    | Pointer inner -> Apply (Ident "Ctypes.ptr", [native_descriptor inner])
    | Optional_pointer inner -> Apply (Ident "Ctypes.ptr_opt", [native_descriptor inner])
    | Owned_pointer inner -> Apply (Ident "Lg_ffi.Owned_pointer.parameter_type", [native_descriptor inner])
    | String -> Ident "Ctypes.string"
    | Void -> Ident "Ctypes.void"
    | Retained_callback (parameters, result) ->
        Apply (Ident "Lg_ffi.Callback.parameter_type", [native_signature parameters result])
    | Callback (parameters, result) ->
        Apply (Ident "Foreign.funptr", [native_signature parameters result])
and native_signature parameters result =
    let open Semantic_ir in
    let parameters = match parameters with [] -> [Void] | values -> values in
    List.fold_right
      (fun parameter result ->
        Apply (Ident "Ctypes.@->", [native_descriptor parameter; result]))
      parameters (Apply (Ident "Ctypes.returning", [native_descriptor result]))


let native_expression value_type (native : native) =
  let open Semantic_ir in
  let descriptor = native_descriptor in
  let signature = native_signature in
  let from =
    match native.library with
    | None -> []
    | Some filename ->
        [ Some "from",
          Labelled_apply (Ident "Dl.dlopen",
            [ Some "filename", String filename;
              Some "flags", List [Constructor ("Dl.RTLD_NOW", None)] ]) ]
  in
  let result_descriptor = match native.ownership, native.result with
    | Owned symbol, Owned_pointer inner ->
        let release = Labelled_apply (Ident "Foreign.foreign",
          from @ [None, String symbol; None, signature [Pointer inner] Void]) in
        Labelled_apply (Ident "Lg_ffi.Owned_pointer.result_type",
          [Some "release", release; None, descriptor inner])
    | _ -> descriptor native.result
  in
  let parameters = match native.parameters with [] -> [Void] | values -> values in
  let signature = List.fold_right (fun parameter rest ->
    Apply (Ident "Ctypes.@->", [descriptor parameter; rest])) parameters
    (Apply (Ident "Ctypes.returning", [result_descriptor])) in
  Typed (value_type,
    Labelled_apply (Ident "Foreign.foreign",
      from @ [None, String native.symbol; None, signature]))
