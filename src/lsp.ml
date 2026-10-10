(* Minimal LSP server over stdio JSON-RPC: hover (type at position) and
   definition (goto top-level def). No JSON library — targeted field
   extraction is enough for the methods we serve. *)

type doc = { mutable text : string }

let docs : (string, doc) Hashtbl.t = Hashtbl.create 8

(* --- tiny JSON field extraction --- *)
let jfind key src =
  let pat = "\"" ^ key ^ "\"" in
  let n = String.length src and lp = String.length pat in
  let rec find i =
    if i + lp > n then None
    else if String.sub src i lp = pat then Some i
    else find (i + 1)
  in
  match find 0 with
  | None -> None
  | Some i ->
    let j = ref (i + String.length pat) in
    let n = String.length src in
    while !j < n && (src.[!j] = ' ' || src.[!j] = ':' || src.[!j] = '\t') do incr j done;
    if !j >= n then None else Some !j

let jstr key src =
  match jfind key src with
  | None -> None
  | Some j when src.[j] <> '"' -> None
  | Some j ->
    let b = Buffer.create 16 in
    let rec go i =
      if i >= String.length src then None
      else match src.[i] with
        | '\\' when i + 1 < String.length src ->
          (match src.[i + 1] with
           | 'n' -> Buffer.add_char b '\n' | 't' -> Buffer.add_char b '\t'
           | 'r' -> Buffer.add_char b '\r' | c -> Buffer.add_char b c);
          go (i + 2)
        | '"' -> Some (Buffer.contents b)
        | c -> Buffer.add_char b c; go (i + 1)
    in
    go (j + 1)

let jint key src =
  match jfind key src with
  | None -> None
  | Some j ->
    let n = String.length src in
    let e = ref j in
    while !e < n && ((src.[!e] >= '0' && src.[!e] <= '9') || src.[!e] = '-') do incr e done;
    (try Some (int_of_string (String.sub src j (!e - j))) with _ -> None)

let jesc s =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c -> match c with
       | '"' -> Buffer.add_string b "\\\"" | '\\' -> Buffer.add_string b "\\\\"
       | '\n' -> Buffer.add_string b "\\n" | '\t' -> Buffer.add_string b "\\t" | c -> Buffer.add_char b c)
    s;
  Buffer.contents b

let send s =
  Printf.printf "Content-Length: %d\r\n\r\n%s" (String.length s) s;
  flush stdout

let respond id result = send (Printf.sprintf {|{"jsonrpc":"2.0","id":%d,"result":%s}|} id result)

(* symbol at (line, character) in text *)
let token_at text line0 char0 =
  let lines = String.split_on_char '\n' text in
  match List.nth_opt lines line0 with
  | None -> None
  | Some ln ->
    let n = String.length ln in
    let delim c = match c with ' ' | '\t' | '(' | ')' | '[' | ']' | '{' | '}' | '"' | ';' | '\'' | '^' | '`' | ',' -> true | _ -> false in
    if char0 >= n then None
    else
      let s = ref char0 and e = ref char0 in
      while !s > 0 && not (delim ln.[!s - 1]) do decr s done;
      while !e < n && not (delim ln.[!e]) do incr e done;
      if !e > !s then Some (String.sub ln !s (!e - !s)) else None

(* expr positions -> type strings, and global def locations *)
let expr_types m : (int * int, string) Hashtbl.t =
  let tbl = Hashtbl.create 256 in
  let rec walk (e : Ast.expr) =
    Hashtbl.replace tbl (e.Ast.loc.Syntax.line, e.Ast.loc.Syntax.col) (Typ.string_of_ty e.Ast.ety);
    match e.Ast.desc with
    | Ast.EIf (a, b, c) -> walk a; walk b; walk c
    | Ast.ECall (f, xs) -> walk f; List.iter walk xs
    | Ast.EOCamlCall (f, oas) ->
      walk f; List.iter (fun oa -> walk (Ast.oarg_expr oa)) oas
    | Ast.ELet (bs, x) -> List.iter (fun (_, i) -> walk i) bs; walk x
    | Ast.EFun fn -> walk fn.Ast.body
    | Ast.EDo xs | Ast.ETuple xs | Ast.EVecLit xs | Ast.ESetLit xs | Ast.EListLit xs -> List.iter walk xs
    | Ast.EMapLit kvs -> List.iter (fun (k, v) -> walk k; walk v) kvs
    | Ast.EMatchOpt (s, _, a, b) | Ast.EVariant (s, _, _, a, b) | Ast.EDynVec (s, _, a, b) | Ast.EDynMap (s, _, a, b) -> walk s; walk a; walk b
    | Ast.ETry (b', c, f) ->
      walk b';
      (match c with Some (_, h) -> walk h | None -> ());
      (match f with Some fe -> walk fe | None -> ())
    | Ast.EUnbox (x, _) | Ast.EUnboxOpt (x, _) | Ast.EBox x -> walk x
    | Ast.EOpt (Some x) -> walk x
    | _ -> ()
  in
  List.iter (function Ast.TDef d -> walk d.Ast.texpr | _ -> ()) m.Ast.tops;
  List.iter walk m.Ast.effects;
  tbl

let def_locs m : (string, Syntax.loc) Hashtbl.t =
  let tbl = Hashtbl.create 64 in
  List.iter (function Ast.TDef d -> Hashtbl.replace tbl d.Ast.tname d.Ast.tloc | _ -> ()) m.Ast.tops;
  tbl

let uri_path u =
  if String.length u > 7 && String.sub u 0 7 = "file://" then String.sub u 7 (String.length u - 7) else u

let compile_doc _path text =
  try
    let tmp = Filename.temp_file "lsp" ".lg" in
    let oc = open_out tmp in output_string oc text; close_out oc;
    let mods = Compiler.compile_path ~roots:[ Filename.dirname tmp; "lib" ] tmp in
    List.find_opt (fun (m : Ast.modl) -> m.Ast.mpath = tmp) mods
  with _ -> None

let hover id uri line char =
  let path = uri_path uri in
  match Hashtbl.find_opt docs path with
  | None -> respond id "null"
  | Some d ->
    (match compile_doc path d.text, token_at d.text line char with
     | Some m, Some _tok ->
       let tbl = expr_types m in
       (* nearest expr on the line at-or-before char *)
       let best =
         Hashtbl.fold
           (fun (ln, col) ty acc ->
             if ln = line + 1 && col <= char + 1 then
               match acc with Some (c2, _) when c2 > col -> acc | _ -> Some (col, ty)
             else acc)
           tbl None
       in
       (match best with
        | Some (_, ty) ->
          respond id (Printf.sprintf {|{"contents":{"kind":"markdown","value":"```lg\n%s\n```"}}|} (jesc ty))
        | None -> respond id "null")
     | _ -> respond id "null")

let definition id uri line char =
  let path = uri_path uri in
  match Hashtbl.find_opt docs path, token_at (try (Hashtbl.find docs path).text with _ -> "") line char with
  | Some d, Some tok ->
    (match compile_doc path d.text with
     | Some m ->
       (match Hashtbl.find_opt (def_locs m) tok with
        | Some dl ->
          respond id
            (Printf.sprintf {|{"uri":"file://%s","range":{"start":{"line":%d,"character":%d},"end":{"line":%d,"character":%d}}}|}
               dl.Syntax.file (dl.Syntax.line - 1) (dl.Syntax.col - 1) (dl.Syntax.line - 1) (dl.Syntax.col + String.length tok - 1))
        | None -> respond id "null")
     | None -> respond id "null")
  | _ -> respond id "null"

let rec run () =
  let buf = Buffer.create 4096 in
  (try
     while true do
       let cl = ref 0 and stop = ref false in
       while not !stop do
         let ln = input_line stdin in
         if String.trim ln = "" then stop := true
         else if String.length ln > 16 && String.sub ln 0 16 = "Content-Length: " then
           cl := int_of_string (String.trim (String.sub ln 16 (String.length ln - 16)))
       done;
       if !cl > 0 then (Buffer.clear buf; Buffer.add_channel buf stdin !cl; handle (Buffer.contents buf))
     done
   with End_of_file | Sys.Break -> ())

and handle body =
  match jstr "method" body with
  | None -> ()
  | Some "initialize" ->
    (match jint "id" body with
     | Some id ->
       respond id {|{"capabilities":{"textDocumentSync":1,"hoverProvider":true,"definitionProvider":true}}|}
     | None -> ())
  | Some "textDocument/didOpen" ->
    (match jstr "uri" body, jstr "text" body with
     | Some u, Some t -> Hashtbl.replace docs (uri_path u) { text = t }
     | _ -> ())
  | Some "textDocument/didChange" ->
    (match jstr "uri" body, jstr "text" body with
     | Some u, Some t -> Hashtbl.replace docs (uri_path u) { text = t }
     | _ -> ())
  | Some "textDocument/didClose" -> ()
  | Some ("textDocument/hover" as m) | Some ("textDocument/definition" as m) ->
    (match jint "id" body, jstr "uri" body, jint "line" body, jint "character" body with
     | Some id, Some u, Some ln, Some ch ->
       let p = uri_path u in
       (* fall back to on-disk file if doc not opened *)
       if not (Hashtbl.mem docs p) then
         (try let ic = open_in p in let t = really_input_string ic (in_channel_length ic) in close_in ic;
              Hashtbl.replace docs p { text = t } with _ -> ());
       if m = "textDocument/hover" then hover id u ln ch else definition id u ln ch
     | _ -> ())
  | Some "shutdown" -> (match jint "id" body with Some id -> respond id "null" | None -> ())
  | Some "exit" -> exit 0
  | Some _ -> ()
