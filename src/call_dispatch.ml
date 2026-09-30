(* Registry of exact-name call handlers consulted by
   Call_elaborator.compile_call after its inline match arms.  Names are
   registered with the handler that previously ran at that point in the
   match, so dispatch order is unchanged: the table is only reached by
   names no earlier arm matched. *)

module Env = Compiler_environment

type result = (Types.typed_expr, Error.t) Stdlib.result

type handler = string -> Env.t -> string -> Ast.form list -> result

type t = (string, handler) Hashtbl.t

let create () = Hashtbl.create 64

let register table name handler = Hashtbl.replace table name handler

let register_all table entries =
  List.iter (fun (name, handler) -> register table name handler) entries

let find table name = Hashtbl.find_opt table name

let dispatch table name scope env arg_forms =
  match find table name with
  | Some handler -> handler scope env name arg_forms
  | None ->
      Error.error ~code:Error_code.Semantic (name ^ " is not callable")
