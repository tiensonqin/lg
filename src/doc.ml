(* `lg doc` — odoc-style static HTML API site.

   Input: compiled modules (tops carry inferred schemes + docstrings);
   when a module ships an .lgi, that file is the export gate — only
   listed entries render (signatures come from the .lgi itself, so
   docs match what importers actually see). Without an .lgi every
   top-level def/variant/extern/ffi is public.

   Output: <out>/index.html (project title + module index) plus one
   <out>/<mname>.html per module — header, sidebar module tree, and a
   <dl> of entries: def signatures, defvariant constructors with field
   types, extern-types, ffi bindings, each anchored at #<name>.
   `ns/name` tokens inside docstrings link to the owning module page.
   Pure CSS, no JS. *)

let esc s =
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun c ->
      match c with
      | '&' -> Buffer.add_string b "&amp;"
      | '<' -> Buffer.add_string b "&lt;"
      | '>' -> Buffer.add_string b "&gt;"
      | '"' -> Buffer.add_string b "&quot;"
      | _ -> Buffer.add_char b c)
    s;
  Buffer.contents b

(* linkify `ns/name` tokens in a docstring when `ns` names a module in
   the site (a literal qualified reference reads like a link anyway) *)
let linkify ~mods s =
  let names = List.map (fun (m : Ast.modl) -> m.Ast.mname) mods in
  let buf = Buffer.create (String.length s + 64) in
  let n = String.length s in
  let is_tok c = not (List.mem c [ ' '; '\t'; '\n'; '('; ')'; '['; ']'; ','; ';'; '`'; '"'; '\'' ]) in
  let rec scan i =
    if i < n then begin
      if is_tok s.[i] then begin
        let j = ref i in
        while !j < n && is_tok s.[!j] do incr j done;
        let tok = String.sub s i (!j - i) in
        (match String.index_opt tok '/' with
         | Some k ->
           let ns = String.sub tok 0 k in
           let nm = String.sub tok (k + 1) (String.length tok - k - 1) in
           if nm <> "" && List.mem ns names then
             Buffer.add_string buf
               (Printf.sprintf "<a href=\"%s.html#%s\"><code>%s</code></a>" (esc ns) (esc nm) (esc tok))
           else Buffer.add_string buf (esc tok)
         | None -> Buffer.add_string buf (esc tok));
        scan !j
      end else begin
        Buffer.add_string buf (esc (String.make 1 s.[i]));
        scan (i + 1)
      end
    end
  in
  scan 0;
  Buffer.contents buf


(* minimal markdown -> html: #..#### headings, ``` fences, - bullet
   lists, blank-line paragraphs, `code`, **bold**, [text](url) *)
let md_inline s =
  let b = Buffer.create (String.length s + 32) in
  let n = String.length s in
  let rec scan i =
    if i < n then begin
      if s.[i] = '`' then begin
        match String.index_from_opt s (i + 1) '`' with
        | Some j ->
          Buffer.add_string b "<code>";
          Buffer.add_string b (esc (String.sub s (i + 1) (j - i - 1)));
          Buffer.add_string b "</code>";
          scan (j + 1)
        | None -> Buffer.add_char b '`'; scan (i + 1)
      end
      else if i + 1 < n && s.[i] = '*' && s.[i + 1] = '*' then begin
        match
          (let rec find j =
             if j + 1 >= n then None
             else if s.[j] = '*' && s.[j + 1] = '*' then Some j
             else find (j + 1)
           in
           find (i + 2))
        with
        | Some j ->
          Buffer.add_string b "<b>";
          Buffer.add_string b (esc (String.sub s (i + 2) (j - i - 2)));
          Buffer.add_string b "</b>";
          scan (j + 2)
        | None -> Buffer.add_string b "**"; scan (i + 2)
      end
      else if s.[i] = '[' then begin
        match String.index_from_opt s (i + 1) ']' with
        | Some j when j + 1 < n && s.[j + 1] = '(' ->
          (match String.index_from_opt s (j + 2) ')' with
           | Some k ->
             let label = String.sub s (i + 1) (j - i - 1) in
             let url = String.sub s (j + 2) (k - j - 2) in
             Buffer.add_string b (Printf.sprintf "<a href=\"%s\">%s</a>" (esc url) (esc label));
             scan (k + 1)
           | None -> Buffer.add_string b (esc (String.sub s i (j + 1 - i))); scan (j + 1))
        | _ -> Buffer.add_char b '['; scan (i + 1)
      end
      else begin
        Buffer.add_string b (esc (String.make 1 s.[i]));
        scan (i + 1)
      end
    end
  in
  scan 0;
  Buffer.contents b

(* returns (title, html body) — title from the first '# ' line or the slug *)
let md_render ~slug src =
  let title = ref (String.capitalize_ascii slug) in
  let b = Buffer.create (String.length src + 256) in
  let lines = String.split_on_char '\n' src in
  let in_code = ref false in
  let in_list = ref false in
  let close_list () = if !in_list then (Buffer.add_string b "</ul>"; in_list := false) in
  List.iter
    (fun ln ->
      if String.starts_with ~prefix:"```" ln then begin
        close_list ();
        if !in_code then Buffer.add_string b "</code></pre>" else Buffer.add_string b "<pre><code>";
        in_code := not !in_code
      end
      else if !in_code then Buffer.add_string b (esc ln ^ "\n")
      else
        let t = String.trim ln in
        if t = "" then close_list ()
        else if String.starts_with ~prefix:"- " t then begin
          if not !in_list then (Buffer.add_string b "<ul>"; in_list := true);
          Buffer.add_string b ("<li>" ^ md_inline (String.sub t 2 (String.length t - 2)) ^ "</li>")
        end
        else begin
          close_list ();
          let rec hashes i = if i < String.length t && t.[i] = '#' then hashes (i + 1) else i in
          let h = hashes 0 in
          if h > 0 && h <= 4 && String.length t > h + 1 && t.[h] = ' ' then begin
            let txt = String.sub t (h + 1) (String.length t - h - 1) in
            if h = 1 && !title = String.capitalize_ascii slug then title := txt;
            Buffer.add_string b (Printf.sprintf "<h%d>%s</h%d>" h (md_inline txt) h)
          end
          else Buffer.add_string b ("<p>" ^ md_inline t ^ "</p>")
        end)
    lines;
  close_list ();
  if !in_code then Buffer.add_string b "</code></pre>";
  (!title, Buffer.contents b)

type dentry = {
  dname : string;
  dkind : string;            (* def | defvariant | extern-type | ffi *)
  dsig : string;             (* rendered signature or declaration *)
  ddoc : string option;
}

(* normalize scheme tyvars 'aNNN -> 'a, 'b, ... in print order *)
let norm_tvars s =
  let tbl = Hashtbl.create 8 in
  let next = ref 0 in
  let b = Buffer.create (String.length s) in
  let n = String.length s in
  let is_id c = (c >= 'a' && c <= 'z') || (c >= '0' && c <= '9') || c = '_' || c = '?' || c = '-' in
  let rec scan i =
    if i < n then begin
      if s.[i] = '\'' && i + 1 < n && is_id s.[i + 1] then begin
        let j = ref (i + 1) in
        while !j < n && is_id s.[!j] do incr j done;
        let tok = String.sub s i (!j - i) in
        (* only rewrite tyvar-looking tokens: 'xNNN with trailing digits *)
        let is_tv =
          let k = String.length tok in
          k > 2 && tok.[k - 1] >= '0' && tok.[k - 1] <= '9'
        in
        if is_tv then begin
          let nm =
            match Hashtbl.find_opt tbl tok with
            | Some v -> v
            | None ->
              let v = "'" ^ String.make 1 (Char.chr (Char.code 'a' + !next)) in
              incr next; Hashtbl.replace tbl tok v; v
          in
          Buffer.add_string b nm
        end else Buffer.add_string b tok;
        scan !j
      end else begin
        Buffer.add_char b s.[i];
        scan (i + 1)
      end
    end
  in
  scan 0;
  Buffer.contents b

let sig_of (sch : Typ.scheme) = norm_tvars (Typ.string_of_lg_ty sch.Typ.sty)

(* tops indexed by name for docstring lookup *)
let docs_of (m : Ast.modl) =
  let tbl = Hashtbl.create 17 in
  List.iter
    (function
      | Ast.TDef d -> Hashtbl.replace tbl d.Ast.tname d.Ast.tdoc
      | Ast.TVariant (_, n, _, _, d) -> Hashtbl.replace tbl n d
      | _ -> ())
    m.Ast.tops;
  tbl

let doc_ty t = norm_tvars (Typ.string_of_lg_ty t)

let entries_of_tops (m : Ast.modl) : dentry list =
  List.filter_map
    (function
      | Ast.TDef d ->
        Some { dname = d.Ast.tname; dkind = "def"; dsig = sig_of d.Ast.tsch; ddoc = d.Ast.tdoc }
      | Ast.TVariant (_, n, ps, cs, d) ->
        let prm = match ps with [] -> "" | _ -> " " ^ String.concat " " (List.map (fun _ -> "'a") ps) in
        let ctor (cn, flds) =
          match flds with
          | [] -> Printf.sprintf "%s" cn
          | _ ->
            Printf.sprintf "(%s %s)" cn
              (String.concat " " (List.map (fun (fnm, ft) -> "[" ^ fnm ^ " " ^ doc_ty ft ^ "]") flds))
        in
        Some { dname = n; dkind = "defvariant";
               dsig = "(defvariant (" ^ n ^ prm ^ ")\n  " ^ String.concat "\n  " (List.map ctor cs) ^ ")";
               ddoc = d }
      | Ast.TExtern (_, n) -> Some { dname = n; dkind = "extern-type"; dsig = "(extern-type " ^ n ^ ")"; ddoc = None }
      | Ast.TFfi (_, n, args, ret, sel, _) ->
        let sel = match sel with Ast.FOcaml s -> ":ocaml " ^ s | Ast.FNative s -> ":native " ^ s | Ast.FJs j -> ":js " ^ j.jsym in
        Some { dname = n; dkind = "ffi";
               dsig = Printf.sprintf "(ffi %s [%s] %s {%s})" n (String.concat " " (List.map Typ.string_of_lg_ty args)) (Typ.string_of_lg_ty ret) sel;
               ddoc = None }
      | Ast.TEffect _ -> None)
    m.Ast.tops

(* .lgi present: it is the export list — render its entries (with
   docstrings merged from the .lg tops) so docs show only what
   importers get. *)
let entries_of_mod (m : Ast.modl) : dentry list =
  let lgi = Compiler.lgi_path m.Ast.mpath in
  let docs = docs_of m in
  if Sys.file_exists lgi then begin
    let find_doc n = match Hashtbl.find_opt docs n with Some d -> d | None -> None in
    List.filter_map
      (function
        | Compiler.LDef (n, sch, _, _, ldoc) ->
          (* .lgi docstring wins (it documents macros, which have no .lg topdef);
             otherwise fall back to the def's own docstring *)
          let ddoc = match ldoc with Some _ -> ldoc | None -> find_doc n in
          Some { dname = n; dkind = "def"; dsig = sig_of sch; ddoc }
        | Compiler.LExtern n ->
          Some { dname = n; dkind = "extern-type"; dsig = "(extern-type " ^ n ^ ")"; ddoc = find_doc n }
        | Compiler.LVariant (n, ps, cs) ->
          let prm = match ps with [] -> "" | _ -> " " ^ String.concat " " (List.map (fun _ -> "'a") ps) in
          let ctor (cn, flds) =
            match flds with
            | [] -> cn
            | _ -> Printf.sprintf "(%s %s)" cn
                     (String.concat " " (List.map (fun (fnm, ft) -> "[" ^ fnm ^ " " ^ doc_ty ft ^ "]") flds))
          in
          Some { dname = n; dkind = "defvariant";
                 dsig = "(defvariant (" ^ n ^ prm ^ ")\n  " ^ String.concat "\n  " (List.map ctor cs) ^ ")";
                 ddoc = find_doc n }
        | Compiler.LMacro (n, sch, ldoc) ->
          Some { dname = n; dkind = "macro"; dsig = sig_of sch;
                 ddoc = (match ldoc with Some _ -> ldoc | None -> find_doc n) }
        | Compiler.LPrivate _ -> None)
      (Compiler.parse_lgi lgi)
  end else entries_of_tops m

let css = {|<style>
:root { --fg:#222; --mut:#666; --bg:#fff; --side:#f7f7f7; --line:#ddd; --acc:#05c; }
* { box-sizing:border-box; }
body { margin:0; font:15px/1.55 -apple-system,Helvetica,Arial,sans-serif; color:var(--fg); }
nav { position:fixed; top:0; left:0; bottom:0; width:230px; overflow:auto;
      background:var(--side); border-right:1px solid var(--line); padding:14px 16px; }
nav h2 { font-size:13px; text-transform:uppercase; color:var(--mut); margin:4px 0 8px; }
nav ul { list-style:none; margin:0; padding:0; }
nav a { color:var(--acc); text-decoration:none; }
nav li { margin:3px 0; }
nav li.cur a { font-weight:600; color:var(--fg); }
main { margin-left:250px; max-width:860px; padding:24px 36px 60px; }
h1 { font-size:1.6em; margin:0 0 4px; }
.sub { color:var(--mut); font-size:.9em; margin-bottom:22px; }
dl.entries { margin:0; }
dt { border-top:1px solid var(--line); padding:10px 4px 4px; }
dt code { background:#f2f2f4; padding:2px 6px; border-radius:4px; font-size:.92em; }
dt .kind { color:var(--mut); font-size:.8em; margin-left:8px; }
dd { margin:2px 4px 12px; padding-left:14px; }
dd pre { background:#f8f8f9; border:1px solid var(--line); border-radius:4px;
         padding:8px 10px; overflow:auto; font-size:.9em; }
dt:target { background:#fffbe8; }
</style>|}

let sort_mods mods =
  List.sort (fun (a : Ast.modl) (b : Ast.modl) -> compare a.Ast.mname b.Ast.mname) mods

let sidebar ~tutorials mods cur =
  let mods = sort_mods mods in
  let b = Buffer.create 256 in
  if tutorials <> [] then begin
    Buffer.add_string b "<nav><h2>Tutorials</h2><ul>";
    List.iter
      (fun (slug, ttitle, _) ->
        let c = if slug = cur then " class=\"cur\"" else "" in
        Buffer.add_string b (Printf.sprintf "<li%s><a href=\"%s.html\">%s</a></li>" c (esc slug) (esc ttitle)))
      tutorials;
    Buffer.add_string b "</ul></nav>"
  end;
  Buffer.add_string b "<nav><h2>Modules</h2><ul>";
  Buffer.add_string b
    (Printf.sprintf "<li%s><a href=\"core.html\">core</a></li>"
       (if cur = "core" then " class=\"cur\"" else ""));
  List.iter
    (fun (m : Ast.modl) ->
      let c = if m.Ast.mname = cur then " class=\"cur\"" else "" in
      Buffer.add_string b
        (Printf.sprintf "<li%s><a href=\"%s.html\">%s</a></li>" c (esc m.mname) (esc m.mname)))
    mods;
  Buffer.add_string b "</ul></nav>";
  Buffer.contents b

(* strip the cwd prefix so headers show repo-relative paths *)
let rel_path p =
  let cwd = Sys.getcwd () ^ "/" in
  if String.starts_with ~prefix:cwd p then
    String.sub p (String.length cwd) (String.length p - String.length cwd)
  else p

let page ~title ~tutorials ~mods (m : Ast.modl) =
  let b = Buffer.create 2048 in
  Buffer.add_string b "<!DOCTYPE html><html><head><meta charset=\"utf-8\">";
  Buffer.add_string b (Printf.sprintf "<title>%s — %s</title>" (esc m.Ast.mname) (esc title));
  Buffer.add_string b css; Buffer.add_string b "</head><body>";
  Buffer.add_string b (sidebar ~tutorials mods m.Ast.mname);
  Buffer.add_string b "<main>";
  Buffer.add_string b (Printf.sprintf "<h1>%s</h1>" (esc m.mname));
  Buffer.add_string b (Printf.sprintf "<div class=\"sub\">module <code>%s</code> — %s</div>" (esc (rel_path m.mpath)) (esc title));
  (match m.Ast.requires with
   | [] -> ()
   | rs ->
     Buffer.add_string b "<div class=\"sub\">requires ";
     List.iteri
       (fun i (al, ns) ->
         if i > 0 then Buffer.add_string b ", ";
         Buffer.add_string b (Printf.sprintf "<a href=\"%s.html\"><code>%s</code></a> as <code>%s</code>" (esc ns) (esc ns) (esc al)))
       rs;
     Buffer.add_string b "</div>");
  Buffer.add_string b "<dl class=\"entries\">";
  List.iter
    (fun d ->
      Buffer.add_string b (Printf.sprintf "<dt id=\"%s\"><code>%s</code><span class=\"kind\">%s</span></dt>" (esc d.dname) (esc d.dname) d.dkind);
      Buffer.add_string b "<dd>";
      Buffer.add_string b (Printf.sprintf "<pre>%s</pre>" (esc d.dsig));
      (match d.ddoc with
       | Some doc when String.trim doc <> "" ->
         Buffer.add_string b (Printf.sprintf "<p>%s</p>" (linkify ~mods doc))
       | _ -> ());
      Buffer.add_string b "</dd>")
    (entries_of_mod m);
  Buffer.add_string b "</dl></main></body></html>";
  Buffer.contents b

let index ~title ~tutorials ~mods =
  let mods = sort_mods mods in
  let b = Buffer.create 1024 in
  Buffer.add_string b "<!DOCTYPE html><html><head><meta charset=\"utf-8\">";
  Buffer.add_string b (Printf.sprintf "<title>%s</title>" (esc title));
  Buffer.add_string b css; Buffer.add_string b "</head><body>";
  Buffer.add_string b (sidebar ~tutorials mods "");
  Buffer.add_string b "<main>";
  Buffer.add_string b (Printf.sprintf "<h1>%s</h1><div class=\"sub\">API documentation</div>" (esc title));
  if tutorials <> [] then begin
    Buffer.add_string b "<h2>Tutorials</h2><dl class=\"entries\">";
    List.iter
      (fun (slug, ttitle, _) ->
        Buffer.add_string b
          (Printf.sprintf "<dt><a href=\"%s.html\"><code>%s</code></a></dt>" (esc slug) (esc ttitle)))
      tutorials;
    Buffer.add_string b "</dl><h2>Modules</h2>"
  end;
  Buffer.add_string b "<dl class=\"entries\">";
  Buffer.add_string b
    (Printf.sprintf "<dt><a href=\"core.html\"><code>core</code></a><span class=\"kind\">%d builtins + %d special forms</span></dt>"
       (List.length Core_doc.builtins) (List.length Core_doc.special_forms));
  List.iter
    (fun (m : Ast.modl) ->
      let n = List.length (entries_of_mod m) in
      Buffer.add_string b
        (Printf.sprintf "<dt><a href=\"%s.html\"><code>%s</code></a><span class=\"kind\">%d entries</span></dt>"
           (esc m.Ast.mname) (esc m.mname) n))
    mods;
  Buffer.add_string b "</dl></main></body></html>";
  Buffer.contents b

let rec mkdir_p path =
  if path <> "" && not (Sys.file_exists path) then begin
    mkdir_p (Filename.dirname path);
    Unix.mkdir path 0o755
  end

let tut_slug (slug, _, _) = slug

let tut_page ~title ~tutorials (slug, ttitle, body) =
  let b = Buffer.create 2048 in
  Buffer.add_string b "<!DOCTYPE html><html><head><meta charset=\"utf-8\">";
  Buffer.add_string b (Printf.sprintf "<title>%s — %s</title>" (esc ttitle) (esc title));
  Buffer.add_string b css; Buffer.add_string b "</head><body>";
  Buffer.add_string b (sidebar ~tutorials [] slug);
  Buffer.add_string b "<main>";
  Buffer.add_string b body;
  Buffer.add_string b "</main></body></html>";
  Buffer.contents b

let core_page ~title ~tutorials ~mods =
  let b = Buffer.create 8192 in
  Buffer.add_string b "<!DOCTYPE html><html><head><meta charset=\"utf-8\">";
  Buffer.add_string b (Printf.sprintf "<title>%s — core</title>" (esc title));
  Buffer.add_string b css; Buffer.add_string b "</head><body>";
  Buffer.add_string b (sidebar ~tutorials mods "core");
  Buffer.add_string b "<main><h1><code>core</code></h1>";
  Buffer.add_string b "<div class=\"sub\">The lg core library — special forms and builtins available unqualified in every module.</div>";
  let alpha ?(label_of = fun n -> n) entries name_of =
    Buffer.add_string b "<p class=\"alpha\">";
    List.iteri
      (fun i (n, _, _) ->
        if i > 0 then Buffer.add_string b " \xc2\xb7 ";
        Buffer.add_string b (Printf.sprintf "<a href=\"#%s\"><code>%s</code></a>" (esc (name_of n)) (esc (label_of n))))
      entries;
    Buffer.add_string b "</p>"
  in
  Buffer.add_string b "<h2>Special forms</h2>";
  alpha Core_doc.special_forms (fun n -> "sf-" ^ n);
  Buffer.add_string b "<dl class=\"entries\">";
  List.iter
    (fun (n, sig_, doc) ->
      Buffer.add_string b (Printf.sprintf "<dt id=\"sf-%s\"><code>%s</code><span class=\"kind\">special form</span></dt>" (esc n) (esc n));
      Buffer.add_string b (Printf.sprintf "<dd><pre>%s</pre><p>%s</p></dd>" (esc sig_) (esc doc)))
    Core_doc.special_forms;
  Buffer.add_string b "</dl>";
  Buffer.add_string b "<h2>Functions and values</h2>";
  alpha Core_doc.builtins (fun n -> n);
  Buffer.add_string b "<dl class=\"entries\">";
  List.iter
    (fun (n, sig_opt, doc) ->
      let sig_ =
        match sig_opt with
        | Some sg -> sg
        | None ->
          (try doc_ty (Infer.instantiate_builtin_ty n)
           with Not_found -> "(builtin)")
      in
      Buffer.add_string b (Printf.sprintf "<dt id=\"%s\"><code>%s</code><span class=\"kind\">builtin</span></dt>" (esc n) (esc n));
      Buffer.add_string b (Printf.sprintf "<dd><pre>%s</pre><p>%s</p></dd>" (esc sig_) (esc doc)))
    Core_doc.builtins;
  Buffer.add_string b "</dl>";
  (* builtin namespaces: qualified-only entries, e.g. (:require [lg.str :as str]) *)
  List.iter
    (fun (ns, alias, entries) ->
      Buffer.add_string b (Printf.sprintf "<h2><code>%s</code></h2>" (esc ns));
      Buffer.add_string b (Printf.sprintf "<p class=\"sub\">(:require [%s :as %s]) — call as <code>%s/name</code>.</p>" (esc ns) (esc alias) (esc alias));
      alpha ~label_of:(fun n -> alias ^ "/" ^ n) entries (fun n -> alias ^ "-" ^ n);
      Buffer.add_string b "<dl class=\"entries\">";
      List.iter
        (fun (n, sig_opt, doc) ->
          let sig_ =
            match sig_opt with
            | Some sg -> sg
            | None ->
              (try doc_ty (Infer.instantiate_builtin_ty n)
               with Not_found -> "(builtin)")
          in
          Buffer.add_string b
            (Printf.sprintf "<dt id=\"%s-%s\"><code>%s/%s</code><span class=\"kind\">builtin</span></dt>" (esc alias) (esc n) (esc alias) (esc n));
          Buffer.add_string b (Printf.sprintf "<dd><pre>%s</pre><p>%s</p></dd>" (esc sig_) (esc doc)))
        entries;
      Buffer.add_string b "</dl>")
    Core_doc.ns_builtins;
  Buffer.add_string b "</main></body></html>";
  Buffer.contents b

let generate ~title ~out ~tutorials mods =
  mkdir_p out;
  let wr file s =
    let oc = open_out (Filename.concat out file) in
    output_string oc s; close_out oc
  in
  wr "index.html" (index ~title ~tutorials ~mods);
  wr "core.html" (core_page ~title ~tutorials ~mods);
  List.iter (fun t -> wr (tut_slug t ^ ".html") (tut_page ~title ~tutorials t)) tutorials;
  List.iter (fun (m : Ast.modl) -> wr (m.Ast.mname ^ ".html") (page ~title ~tutorials ~mods m)) mods
