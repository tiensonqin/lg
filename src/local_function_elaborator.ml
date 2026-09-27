open Ast
open Types
open Expression_support
module Env = Compiler_environment

type local_function = {
  local_source_name : string;
  local_target_name : string;
  local_params : Ast.form;
  local_body_forms : Ast.form list;
  local_initial_type : Types.ty;
}

let letfn_counter = ref 0
let canonical tys = Type_solver.canonical (TTuple tys)

let resolve_host_alias = function
  | TOcaml name -> (
      match Ocaml_signature.type_manifest name with
      | Ok ((TPoly_variant _ | TRecord _ | TNamed_record _) as manifest) ->
          Some manifest
      | Ok _ | Error _ -> (
          match Ocaml_signature.record_type name with
          | Ok record -> Some record
          | Error _ -> None))
  | _ -> None

let resolve_constraint_type scope env ty =
  let ty = Function_elaborator.infer_named_record scope env
      (Types.constraint_value_type ty) in
  match ty with
  | TOcaml _ -> Option.value (resolve_host_alias ty) ~default:ty
  | TOcaml_app (name, arguments) ->
      let candidates =
        Env.filter_record_bindings
          (fun _ (binding : binding) ->
            match binding.ty with
            | TNamed_record record
              when String.equal record.type_name name
                   && List.length record.type_parameters = List.length arguments ->
                Some record
            | _ -> None)
          env
        |> Function_elaborator.unique_named_records
      in
      (match candidates with
      | [ record ] -> TNamed_record { record with type_arguments = arguments }
      | _ -> ty)
  | _ -> ty

let constraints scope env members types expressions =
  let equations = ref [] in
  let observe_constraint left right =
    (* Capabilities constrain the value; they are not recursive storage. *)
    let resolve = resolve_constraint_type scope env in
    equations := (resolve left, resolve right) :: !equations
  in
  let observe_call name _arguments actuals =
    match
      List.find_index
        (fun (f : local_function) ->
          f.local_source_name = name
          || Names.scoped_key scope f.local_source_name = name)
        members
    with
    | Some index -> (
        match List.nth types index with
        | TFn (parameters, _) when List.length parameters = List.length actuals
          ->
            List.iter2 observe_constraint parameters actuals
        | _ -> ())
    | None -> ()
  in
  let collect =
    List.fold_left2
      (fun result (f : local_function) (expression : typed_expr) ->
        Result.bind result (fun () ->
            Result.bind (Destructure.parse_param_specs f.local_params)
              (fun specs ->
                match expression.ty with
                | TFn (parameters, return_ty) ->
                    let params =
                      List.map2
                        (fun (spec : Destructure.param_spec) ty ->
                          (spec.source_name, ty))
                        specs parameters
                    in
                    Type_inference.infer_params ~expected_return_ty:return_ty
                      ~lookup_call_ty:(Expression_support.lookup_call_ty scope env)
                      ~expand_form:(Macro_expander.expand_all ~scope ~compiler_env:env)
                      ~observe_call ~observe_constraint
                      ~lookup_function_ty:(lookup_function_ty scope env)
                      ~lookup_protocol_constraint:
                        (Protocol.constraint_type scope env)
                      ~lookup_dynamic_key_record_type:
                        (Expression_support.dynamic_key_record_type env)
                      ~lookup_key_record_type:
                        (Expression_support.record_type_for_keyword ~scope env)
                      ~resolve_named_record:
                        (Function_elaborator.infer_named_record scope env)
                      params f.local_body_forms
                    |> Result.map (fun _ -> ())
                | _ -> assert false)))
      (Ok ()) members expressions
  in
  Result.bind collect (fun () ->
      let unify result (expected, actual) =
        Result.bind result (fun substitutions ->
            match Type_solver.unify ~resolve_alias:resolve_host_alias
                    substitutions expected actual with
            | Ok substitutions -> Ok substitutions
            | Error conflict ->
                Error.error
                  ("incompatible recursive types: "
                  ^ Types.source_name conflict.left
                  ^ " and "
                  ^ Types.source_name conflict.right))
      in
      let unified =
        List.fold_left2
          (fun result expected (expression : typed_expr) ->
            unify result (expected, expression.ty))
          (Ok Type_solver.empty) types expressions
        |> fun result -> List.fold_left unify result (List.rev !equations)
      in
      unified)

let refine_function scope env ~name ~target ~params ~body expression =
  let definition =
    {
      local_source_name = name;
      local_target_name = target;
      local_params = params;
      local_body_forms = body;
      local_initial_type = expression.ty;
    }
  in
  let env =
    Env.add
      (Names.scoped_key scope name)
      (Types.binding target expression.ty)
      env
  in
  constraints scope env [ definition ] [ expression.ty ] [ expression ]

let parameter_names params =
  match Destructure.parse_param_specs params with
  | Ok specs -> Function_elaborator.lexical_parameter_names specs
  | Error _ -> []

let rec free_symbols bound = function
  | FSymbol name when not (List.mem name bound) -> [ name ]
  | FList (FSymbol ("quote" | "syntax-quote") :: _) -> []
  | FList (FSymbol "fn" :: FSymbol name :: params :: body) ->
      List.concat_map
        (free_symbols ((name :: parameter_names params) @ bound))
        body
  | FList (FSymbol "fn" :: (FVector _ as params) :: body) ->
      List.concat_map (free_symbols (parameter_names params @ bound)) body
  | FList
      (FSymbol ("let" | "let*" | "loop" | "loop*") :: FVector bindings :: body)
    ->
      let rec collect bound = function
        | pattern :: value :: rest ->
            free_symbols bound value
            @ collect (Destructure.pattern_names pattern @ bound) rest
        | [] -> List.concat_map (free_symbols bound) body
        | forms -> List.concat_map (free_symbols bound) (forms @ body)
      in
      collect bound bindings
  | FList (FSymbol "letfn" :: FVector bindings :: body) ->
      let names =
        List.filter_map
          (function FList (FSymbol name :: _) -> Some name | _ -> None)
          bindings
      in
      let bound = names @ bound in
      List.concat_map
        (function
          | FList (FSymbol _ :: params :: body) ->
              List.concat_map
                (free_symbols (parameter_names params @ bound))
                body
          | form -> free_symbols bound form)
        bindings
      @ List.concat_map (free_symbols bound) body
  | FList forms | FVector forms -> List.concat_map (free_symbols bound) forms
  | FMap pairs ->
      List.concat_map
        (fun (key, value) -> free_symbols bound key @ free_symbols bound value)
        pairs
  | _ -> []

let compile ~compile_named_fn ~prepare_recursive ~compile_body scope env
    bindings body_forms =
  let local_names =
    match bindings with
    | FVector forms ->
        List.filter_map
          (function FList (FSymbol name :: _) -> Some name | _ -> None)
          forms
    | _ -> []
  in
  let env = Env.add_core_exclusions ~scope local_names env in
  let parse_functions forms =
    incr letfn_counter;
    let prefix = "__lg_letfn_" ^ string_of_int !letfn_counter ^ "_" in
    let rec parse names acc = function
      | [] -> Ok (List.rev acc)
      | FList (FSymbol name :: (FVector _ as params) :: (_ :: _ as body))
        :: rest ->
          if List.mem name names then
            Error.error ("duplicate letfn binding " ^ name)
          else
            Result.bind (Destructure.parse_param_specs params) (fun specs ->
                let parameter_types =
                  List.map
                    (fun (spec : Destructure.param_spec) ->
                      Option.value spec.explicit_ty
                        ~default:(Type_solver.fresh ())
                      |> Function_elaborator.infer_named_record scope env)
                    specs
                in
                Result.bind
                  (Macro_expander.expand_all_forms ~scope
                     ~compiler_env:
                       (Env.add_core_exclusions ~scope
                          (Function_elaborator.lexical_parameter_names specs)
                          env)
                     body)
                  (fun body_forms ->
                    let function_ =
                      {
                        local_source_name = name;
                        local_target_name =
                          prefix
                          ^ string_of_int (List.length names)
                          ^ "_" ^ Names.sanitize_name name;
                        local_params = params;
                        local_body_forms = body_forms;
                        local_initial_type =
                          TFn (parameter_types, Type_solver.fresh ());
                      }
                    in
                    parse (name :: names) (function_ :: acc) rest))
      | _ ->
          Error.error
            "letfn binding must be a list of name, parameter vector, and body"
    in
    parse [] [] forms
  in
  let add_function env (function_ : local_function) binding =
    Env.add (Names.scoped_key scope function_.local_source_name) binding env
  in
  let compile_functions functions =
    let components =
      functions
      |> List.map (fun (function_ : local_function) ->
          ({
             name = function_.local_source_name;
             dependencies =
               List.concat_map
                 (free_symbols (parameter_names function_.local_params))
                 function_.local_body_forms;
           }
            : Dependency_graph.node))
      |> Dependency_graph.strongly_connected_components
    in
    let rec compile_components env = function
      | [] -> compile_body scope env "letfn requires a body" body_forms
      | names :: rest -> (
          let members =
            List.filter
              (fun (f : local_function) -> List.mem f.local_source_name names)
              functions
          in
          let complete env bindings recursive =
            let body =
              match compile_components env rest with
              | Ok _ as body -> body
              | Error (error : Error.t) when recursive ->
                  Error
                    {
                      error with
                      message =
                        "incompatible recursive types: " ^ error.message;
                    }
              | Error _ as error -> error
            in
            Result.map
              (fun body ->
                {
                  body with
                  semantic_expr =
                    (if recursive then
                       Semantic_ir.LetRecGroup (bindings, body.semantic_expr)
                     else Semantic_ir.Let (bindings, body.semantic_expr));
                })
              body
          in
          match members with
          | [ function_ ] ->
              Result.bind
                (compile_named_fn scope env function_.local_source_name
                   function_.local_params function_.local_body_forms)
                (fun expression ->
                  let binding =
                    binding_of_expr function_.local_target_name expression
                  in
                  complete
                    (add_function env function_ binding)
                    [
                      ( Semantic_ir.PVar function_.local_target_name,
                        expression.semantic_expr );
                    ]
                    false)
          | [] -> assert false
          | _ ->
              let initial =
                List.map
                  (fun (f : local_function) -> f.local_initial_type)
                  members
              in
              let rec solve seen types =
                let group_env =
                  List.fold_left2
                    (fun env (f : local_function) ty ->
                      add_function env f (Types.binding f.local_target_name ty))
                    env members types
                in
                let preflight_expressions =
                  List.map
                    (fun ty -> typed_ir ty (Semantic_ir.Ident "__lg_letfn_preflight"))
                    types
                in
                Result.bind
                  (constraints scope group_env members types preflight_expressions)
                  (fun preflight_substitutions ->
                let preflight_inferred =
                  List.map (Type_solver.apply preflight_substitutions) types
                in
                let previous = canonical types
                and current = canonical preflight_inferred in
                if not (Types.equal previous current) then
                  if List.exists (Types.equal current) seen then
                    Error.error
                      "letfn recursive type constraints do not converge"
                  else solve (previous :: seen) preflight_inferred
                else
                let rec prepare acc = function
                  | [] -> Ok (List.rev acc)
                  | (f : local_function) :: rest ->
                      Result.bind
                        (prepare_recursive ~ocaml_name:f.local_target_name scope
                           group_env f.local_source_name f.local_params
                           f.local_body_forms) (fun expression ->
                          prepare (expression :: acc) rest)
                in
                let prepared =
                  match prepare [] members with
                  | Ok _ as prepared -> prepared
                  | Error (error : Error.t) ->
                      Error
                        {
                          error with
                          message =
                            "incompatible recursive types: " ^ error.message;
                        }
                in
                Result.bind prepared (fun expressions ->
                    let unified =
                      constraints scope group_env members types expressions
                    in
                    Result.bind unified (fun substitutions ->
                        let inferred =
                          List.map (Type_solver.apply substitutions) types
                        in
                        let expressions =
                          List.map
                            (fun (expression : typed_expr) ->
                              {
                                expression with
                                ty =
                                  Type_solver.apply substitutions expression.ty;
                              })
                            expressions
                        in
                        let previous = canonical types
                        and current = canonical inferred in

                        if Types.equal previous current then
                          let final_env =
                            List.fold_left2
                              (fun env (f : local_function) expression ->
                                add_function env f
                                  (binding_of_expr f.local_target_name
                                     expression))
                              env members expressions
                          in
                          let bindings =
                            List.map2
                              (fun (f : local_function) expression ->
                                ( Semantic_ir.PVar f.local_target_name,
                                  expression.semantic_expr ))
                              members expressions
                          in
                          complete final_env bindings true
                        else if List.exists (Types.equal current) seen then
                          Error.error
                            "letfn recursive type constraints do not converge"
                        else solve (previous :: seen) inferred)))
              in
              solve [] initial)
    in
    compile_components env components
  in
  match (bindings, body_forms) with
  | _, [] -> Error.error "letfn requires a body"
  | FVector [], _ ->
      Error.error "letfn requires at least one local function binding"
  | FVector forms, _ -> Result.bind (parse_functions forms) compile_functions
  | _ -> Error.error "letfn expects a vector of local function bindings"
