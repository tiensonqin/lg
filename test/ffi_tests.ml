let contains text fragment =
  let rec loop index =
    index + String.length fragment <= String.length text
    && (String.sub text index (String.length fragment) = fragment
       || loop (index + 1))
  in
  loop 0

let compile ?(target = Lg.Target.Native) source =
  match Lg.Compiler.compile_string ~target source with
  | Ok output -> output
  | Error error -> failwith error.message

let reject ?(target = Lg.Target.Native) fragment source =
  match Lg.Compiler.compile_string ~target source with
  | Ok _ -> failwith ("accepted invalid FFI declaration: " ^ source)
  | Error error ->
      if not (contains error.message fragment) then
        failwith ("expected " ^ fragment ^ ", got " ^ error.message)

let write path content =
  let channel = open_out path in
  Fun.protect ~finally:(fun () -> close_out channel)
    (fun () -> output_string channel content)

let command value =
  if Sys.command value <> 0 then failwith ("command failed: " ^ value)

let rec remove_tree path =
  if Sys.is_directory path then (
    Sys.readdir path |> Array.iter (fun name -> remove_tree (Filename.concat path name));
    Unix.rmdir path)
  else Sys.remove path

let test_native_execution () =
  let dir = Filename.temp_dir "lg-ffi-" "" in
  let c_path = Filename.concat dir "fixture.c" in
  let library = Filename.concat dir "fixture.so" in
  let ml_path = Filename.concat dir "binding.ml" in
  let executable = Filename.concat dir "binding.exe" in
  Fun.protect
    ~finally:(fun () ->
      Sys.readdir dir
      |> Array.iter (fun name -> Sys.remove (Filename.concat dir name));
      Unix.rmdir dir)
    (fun () ->
      write c_path
        "#include <stdbool.h>\n#include <stdlib.h>\n#include <string.h>\n\
         static int saved = 0;\n\
         int ffi_sub(int a, int b) { return a - b; }\n\
         double ffi_half(double x) { return x / 2.0; }\n\
         bool ffi_not(bool x) { return !x; }\n\
         int ffi_length(const char *s) { return (int)strlen(s); }\n\
         void ffi_save(int x) { saved = x; }\n\
         int ffi_load(void) { return saved; }\n\
         int ffi_call(int (*f)(int,int)) { return f(17, 5); }\n\
         int ffi_zero(int (*f)(void)) { return f(); }\n\
         void ffi_notify(void (*f)(int)) { f(73); }\n\
         double ffi_float(double (*f)(double)) { return f(7.0); }\n\
         int *ffi_address(void) { return &saved; }\n\
         int *ffi_missing(void) { return NULL; }\n\
         int ffi_read(int *p) { return *p; }\n\
         void ffi_write(int *p, int x) { *p = x; }\n\
         int ffi_is_null(int *p) { return p == NULL; }\n\
         int **ffi_slot(void) { static int *p = &saved; return &p; }\n\
         int ffi_read_slot(int **p) { return **p; }\n\
         static int freed = 0;\n\
         int *ffi_alloc(int x) { int *p = malloc(sizeof(int)); if(p) *p=x; return p; }\n\
         void ffi_free(int *p) { freed++; free(p); }\n\
         int ffi_freed(void) { return freed; }\n\
         static int (*retained)(int);\n\
         void ffi_register(int (*f)(int)) { retained = f; }\n\
         int ffi_invoke(int x) { return retained(x); }\n\
         void ffi_unregister(void) { retained = NULL; }\n";
      command (Printf.sprintf "cc -shared -fPIC %s -o %s"
                 (Filename.quote c_path) (Filename.quote library));
      let binding name args result symbol =
        Printf.sprintf "(ffi %s [%s] %s {:native %S :library %S})\n"
          name args result symbol library
      in
      let source =
        binding "subtract" ":int :int" ":int" "ffi_sub"
        ^ binding "half" ":float" ":float" "ffi_half"
        ^ binding "invert" ":bool" ":bool" "ffi_not"
        ^ binding "length" ":string" ":int" "ffi_length"
        ^ binding "save" ":int" ":unit" "ffi_save"
        ^ binding "load" "" ":int" "ffi_load"
        ^ Printf.sprintf "(ffi call [:fn<int;int;int>] :int {:native \"ffi_call\" :library %S :callbacks :call})\n" library
        ^ Printf.sprintf "(ffi zero [:fn<int>] :int {:native \"ffi_zero\" :library %S :callbacks :call})\n" library
        ^ Printf.sprintf "(ffi notify [:fn<int;unit>] :unit {:native \"ffi_notify\" :library %S :callbacks :call})\n" library
        ^ Printf.sprintf "(ffi float-call [:fn<float;float>] :float {:native \"ffi_float\" :library %S :callbacks :call})\n" library
        ^ "(notify (fn [x] (save x))) (def notified (load))\n"
        ^ "(def float-result (float-call (fn [x] (half x))))\n"
        ^ "(def captured 23) (def callback-result (call (fn [a b] (subtract (subtract captured a) b))))\n"
        ^ "(def zero-result (zero (fn [] captured)))\n"
        ^ Printf.sprintf "(ffi address [] :pointer<int> {:native \"ffi_address\" :library %S :ownership :borrowed})\n" library
        ^ Printf.sprintf "(ffi missing [] :option<pointer<int>> {:native \"ffi_missing\" :library %S :ownership :borrowed})\n" library
        ^ binding "read-pointer" ":pointer<int>" ":int" "ffi_read"
        ^ binding "write-pointer" ":pointer<int> :int" ":unit" "ffi_write"
        ^ binding "null-pointer" ":option<pointer<int>>" ":int" "ffi_is_null"
        ^ "(def pointer (address)) (write-pointer pointer 62) (def pointed-value (read-pointer pointer))\n"
        ^ "(def null-value (null-pointer (missing))) (def present-pointer (null-pointer pointer))\n"
        ^ Printf.sprintf "(ffi slot [] :pointer<pointer<int>> {:native \"ffi_slot\" :library %S :ownership :borrowed})\n" library
        ^ binding "read-slot" ":pointer<pointer<int>>" ":int" "ffi_read_slot"
        ^ "(def nested-pointer-value (read-slot (slot)))\n"
        ^ Printf.sprintf "(ffi allocate [:int] :owned-pointer<int> {:native \"ffi_alloc\" :library %S :ownership :owned :release \"ffi_free\"})\n" library
        ^ binding "read-owned" ":owned-pointer<int>" ":int" "ffi_read"
        ^ binding "freed" "" ":int" "ffi_freed"
        ^ "(ffi close [:owned-pointer<int>] :unit {:native :release})\n"
        ^ "(def owned (allocate 81)) (def owned-value (read-owned owned)) (close owned) (close owned) (def freed-count (freed))\n"
        ^ "(ffi retain [:fn<int;int>] :callback<fn<int;int>> {:native :callback})\n"
        ^ "(ffi release-callback [:callback<fn<int;int>>] :unit {:native :release})\n"
        ^ binding "register" ":callback<fn<int;int>>" ":unit" "ffi_register"
        ^ binding "invoke" ":int" ":int" "ffi_invoke"
        ^ binding "unregister" "" ":unit" "ffi_unregister"
        ^ "(def retained (retain (fn [x] (subtract captured x)))) (register retained) (def retained-value (invoke 3)) (unregister) (release-callback retained)\n"
        ^ "(def difference (subtract 17 5))\n"
        ^ "(def fraction (half 7.0))\n"
        ^ "(def flipped (invert false))\n"
        ^ "(def empty-length (length \"\"))\n"
        ^ "(def text-length (length \"hello\"))\n"
        ^ "(save 91)\n(def stored (load))\n"
        ^ "(def alias subtract)\n(def aliased (alias 9 2))\n"
      in
      let output = compile source in
      if contains output "Obj.magic" || contains output "Runtime_dynamic" then
        failwith "FFI generated an erased boundary";
      write ml_path (output ^ "\nlet () =\n\
        assert (difference = 12); assert (fraction = 3.5);\n\
        assert flipped; assert (empty_length = 0); assert (text_length = 5);\n\
        assert (stored = 91); assert (aliased = 7); assert (callback_result = 1); assert (zero_result = 23); assert (notified = 73); assert (pointed_value = 62); assert (retained_value = 20); (match register retained with _ -> failwith \"released callback entered C\" | exception Invalid_argument _ -> ()); assert (owned_value = 81); assert (freed_count = 1); assert (null_value = 1); assert (present_pointer = 0); assert (nested_pointer_value = 62); (match read_owned owned with _ -> failwith \"released owned pointer entered C\" | exception Invalid_argument _ -> ()); assert (float_result = 3.5)\n");
      command (Printf.sprintf
        "ocamlfind ocamlopt -package ctypes-foreign,lg.ffi -linkpkg %s -o %s"
        (Filename.quote ml_path) (Filename.quote executable));
      command (Filename.quote executable))

let test_native_missing_resources () =
  let dir = Filename.temp_dir "lg-ffi-errors-" "" in
  Fun.protect ~finally:(fun () -> remove_tree dir) (fun () ->
    let missing_library = Filename.concat dir "missing-library.so" in
    let cases =
      ["lg_missing_symbol_for_ffi_test", "(ffi unavailable [] :int {:native \"lg_missing_symbol_for_ffi_test\"})";
       missing_library, Printf.sprintf "(ffi unavailable [] :int {:native \"abs\" :library %S})" missing_library] in
    List.iteri (fun index (expected, source) ->
      let ml = Filename.concat dir ("missing" ^ string_of_int index ^ ".ml") in
      let executable = ml ^ ".exe" in
      let body = compile source in
      write ml (Printf.sprintf {|
let contains text fragment =
  let rec loop index =
    index + String.length fragment <= String.length text &&
    (String.sub text index (String.length fragment) = fragment || loop (index + 1))
  in loop 0
let () =
  match (let module Binding = struct
%s
  end in ignore Binding.unavailable) with
  | () -> failwith "missing foreign resource was accepted"
  | exception Dl.DL_error message ->
      if not (contains message %S) then failwith message
|} body expected);
      command (Printf.sprintf "ocamlfind ocamlopt -package ctypes-foreign,lg.ffi -linkpkg %s -o %s"
        (Filename.quote ml) (Filename.quote executable));
      command (Filename.quote executable)) cases)

let test_javascript_execution () =
  let dir = Filename.temp_dir "lg-js-ffi-" "" in
  Fun.protect
    ~finally:(fun () -> remove_tree dir)
    (fun () ->
      let output = compile ~target:Lg.Target.Melange {|
(ffi floor [:float] :float {:js "floor" :scope ["Math"]})
(ffi basename [:string] :string {:js "basename" :module "node:path"})
(ffi scoped-name [:string] :string {:js "basename" :module "node:path" :scope ["posix"]})
(ffi decode [:string] :string {:js "decodeURIComponent"})
(ffi next [] :int {:js "next" :scope ["fixture"]})
(ffi subtract [:int :int] :int {:js "subtract" :scope ["fixture"]})
(ffi invert [:bool] :bool {:js "invert" :scope ["fixture"]})
(ffi save [:int] :unit {:js "save" :scope ["fixture"]})
(ffi load [] :int {:js "load" :scope ["fixture"]})
(extern-type box)
(ffi make-box [:int :string] :box {:js "Box" :kind :new})
(ffi increment [:box :int] :int {:js "increment" :kind :send})
(ffi box-value [:box] :int {:js "value" :kind :get})
(ffi set-value [:box :int] :unit {:js "value" :kind :set})
(ffi box-label [:box] :string {:js "label" :kind :get})
(ffi index-value [:box :string] :int {:js :get-index})
(ffi set-index [:box :string :int] :unit {:js :set-index})
(def instance (make-box 5 "A"))
(def first-value (box-value instance))
(def incremented (increment instance 7))
(set-value instance 30)
(def changed-value (box-value instance))
(def label (box-label instance))
(set-index instance "value" 71)
(def indexed (index-value instance "value"))
(def make-alias make-box)
(def second-object (make-alias 9 "B"))
(def second-value (box-value second-object))
(module Boxes
  (extern-type box)
  (ffi create [:int :string] :box {:js "Box" :kind :new})
  (ffi value [:box] :int {:js "value" :kind :get}))
(type-alias box-alias :Boxes.box)
(ffi alias-value [:box-alias] :int {:js "value" :kind :get})
(def namespaced (Boxes/create 88 "namespaced"))
(def namespaced-value (Boxes/value namespaced))
(def aliased-value (alias-value namespaced))
(ffi call-two [:fn<int;int;int>] :int {:js "callTwo" :scope ["fixture"]})
(ffi call-zero [:fn<int>] :int {:js "callZero" :scope ["fixture"]})
(ffi save-callback [:fn<int;int>] :unit {:js "saveCallback" :scope ["fixture"]})
(ffi invoke-saved [:int] :int {:js "invokeSaved" :scope ["fixture"]})
(def callback-result (call-two (fn [a b] (subtract a b))))
(def zero-callback-result (call-zero (fn [] 9)))
(def captured 23)
(save-callback (fn [value] (subtract captured value)))
(def retained-result (invoke-saved 3))
(ffi maybe-number [:int] :option<int> {:js "maybeNumber" :scope ["fixture"] :return :nullable})
(ffi null-number [] :option<int> {:js "nullNumber" :scope ["fixture"] :return :null})
(ffi undefined-number [] :option<int> {:js "undefinedNumber" :scope ["fixture"] :return :undefined})
(def absent-null (maybe-number 0))
(def absent-undefined (maybe-number 1))
(def present-number (maybe-number 2))
(def null-only (null-number))
(def undefined-only (undefined-number))
(ffi numbers [] :array<int> {:js "numbers" :scope ["fixture"]})
(ffi empty-numbers [] :array<int> {:js "emptyNumbers" :scope ["fixture"]})
(ffi sum [:int :array<int>] :int {:js "sum" :scope ["fixture"] :variadic true})
(ffi array-get [:array<int> :int] :int {:js :get-index})
(ffi array-set [:array<int> :int :int] :unit {:js :set-index})
(def items (numbers))
(def total (sum 10 items))
(def empty-total (sum 10 (empty-numbers)))
(array-set items 0 7)
(def changed-item (array-get items 0))
(ffi array-get? [:array<int> :int] :option<int> {:js :get-index :return :undefined})
(def missing-item (array-get? items 99))
(def present-item (array-get? items 0))
(ffi append-items [:array<int> :array<int>] :int {:js "push" :kind :send :variadic true})
(def destination (empty-numbers))
(def appended-size (append-items destination items))
(def unchanged-size (append-items destination (empty-numbers)))
(extern-type number-map)
(ffi make-map [] :number-map {:js "Map" :kind :new})
(ffi put! [:number-map :string :int] :number-map {:js "set" :kind :send})
(ffi size [:number-map] :int {:js "size" :kind :get})
(ffi lookup [:number-map :string] :option<int> {:js "get" :kind :send :return :undefined})
(def entries (make-map))
(put! entries "answer" 42)
(def map-answer (lookup entries "answer"))
(def map-missing (lookup entries "missing"))
(def map-size (size entries))
(type-record object-input (display-name :string) (count :int) (extra :option<int>))
(extern-type options-object)
(ffi make-options [:object-input] :options-object
  {:js :object :rename {:display-name "displayName"} :optional [:extra]})
(def basic-options (make-options (object-input. "first" 4 nil)))
(def full-options (make-options (object-input. "second" 5 9)))
(def make-options-alias make-options)
(def other-options (make-options-alias (object-input. "first" 4 nil)))
(def rounded (floor 3.8))
(def filename (basename "/tmp/example.txt"))
(def nested (scoped-name "/tmp/nested.txt"))
(def decoded (decode "hello%20world"))
(def ordered (subtract (next) (next)))
(def flipped (invert false))
(save 91)
(def stored (load))
(def alias subtract)
(def aliased (alias 9 2))
(module Arithmetic (ffi absolute [:float] :float {:js "abs" :scope ["Math"]}))
(def absolute (Arithmetic/absolute -4.5))
|} in
      if contains output "Obj.magic" || contains output "Runtime_dynamic" then
        failwith "JavaScript FFI generated an erased boundary";
      let ml = Filename.concat dir "binding.ml" in
      let js = Filename.concat dir "binding.js" in
      let check = Filename.concat dir "check.cjs" in
      write ml output;
      let ppx_dir =
        let channel = Unix.open_process_in "ocamlfind query melange.ppx" in
        let result = input_line channel in
        (match Unix.close_process_in channel with
         | Unix.WEXITED 0 -> () | _ -> failwith "cannot find Melange PPX");
        result
      in
      command (Printf.sprintf "melc --ppx %s --mel-module-type commonjs -o %s %s"
        (Filename.quote (Filename.quote (Filename.concat ppx_dir "ppx.exe") ^ " --as-ppx"))
        (Filename.quote js) (Filename.quote ml));
      let node_modules = Filename.concat dir "node_modules" in
      let runtime = Filename.concat node_modules "melange.js" in
      Unix.mkdir node_modules 0o755;
      Unix.mkdir runtime 0o755;
      (* Emit the actual adapter runtime, as Dune melange.emit does for an application. *)
      List.iter (fun name ->
        command (Printf.sprintf "melc --mel-module-type commonjs -o %s %s"
          (Filename.quote (Filename.concat runtime (name ^ ".js")))
          (Filename.quote (Filename.concat (Filename.dirname ppx_dir)
            ("js/melange/" ^ name ^ ".cmj")))))
        ["caml_option"; "caml_splice_call"];
      write check {|
const assert = require("node:assert/strict");
let calls = 0, saved = 0, savedCallback;
globalThis.fixture = {
  callTwo(callback) { return callback(17, 5); },
  callZero(callback) { return callback(); },
  saveCallback(callback) { savedCallback = callback; },
  invokeSaved(value) { return savedCallback(value); },
  maybeNumber(kind) { return kind === 0 ? null : kind === 1 ? undefined : 17; },
  nullNumber() { return null; }, undefinedNumber() { return undefined; },
  numbers() { return [1, 2]; }, emptyNumbers() { return []; },
  sum(initial, ...items) { return items.reduce((a, b) => a + b, initial); },
  next() { return ++calls; }, subtract(a,b) { return a-b; },
  invert(x) { return !x; }, save(x) { saved = x; }, load() { return saved; }
};
globalThis.Box = class Box {
  constructor(value, label) { this.value = value; this.label = label; }
  increment(amount) { this.value += amount; return this.value; }
};
const binding = require("./binding.js");
assert.equal(binding.namespaced_value, 88);
assert.equal(binding.aliased_value, 88);
assert.equal(binding.callback_result, 12);
assert.equal(binding.zero_callback_result, 9);
assert.equal(binding.retained_result, 20);
assert.equal(binding.absent_null, undefined);
assert.equal(binding.absent_undefined, undefined);
assert.equal(binding.present_number, 17);
assert.equal(binding.null_only, undefined);
assert.equal(binding.undefined_only, undefined);
assert.equal(binding.total, 13);
assert.equal(binding.empty_total, 10);
assert.equal(binding.changed_item, 7);
assert.equal(binding.missing_item, undefined);
assert.equal(binding.present_item, 7);
assert.deepEqual(binding.items, [7, 2]);
assert.deepEqual(binding.destination, [7, 2]);
assert.equal(binding.appended_size, 2);
assert.equal(binding.unchanged_size, 2);
assert.equal(binding.map_answer, 42);
assert.equal(binding.map_missing, undefined);
assert.equal(binding.map_size, 1);
assert.deepEqual(binding.basic_options, {displayName: "first", count: 4});
assert.deepEqual(binding.full_options, {displayName: "second", count: 5, extra: 9});
assert.equal(Object.hasOwn(binding.basic_options, "extra"), false);
assert.notEqual(binding.basic_options, binding.other_options);
assert.equal(binding.first_value, 5);
assert.equal(binding.incremented, 12);
assert.equal(binding.changed_value, 30);
assert.equal(binding.label, "A");
assert.equal(binding.indexed, 71);
assert.equal(binding.instance.value, 71);
assert.equal(binding.second_value, 9);
assert.notEqual(binding.instance, binding.second_object);
assert.equal(binding.rounded, 3);
assert.equal(binding.filename, "example.txt");
assert.equal(binding.nested, "nested.txt");
assert.equal(binding.decoded, "hello world");
assert.equal(binding.ordered, -1);
assert.equal(calls, 2);
assert.equal(binding.flipped, true);
assert.equal(binding.stored, 91);
assert.equal(binding.aliased, 7);
assert.equal(binding.absolute, 4.5);
|};
      command ("node " ^ Filename.quote check))

let test_javascript_validation () =
  let source = "(ffi f [:float] :float {:js \"floor\" :scope [\"Math\"]})" in
  (match Lg.Compiler.required_ocaml_packages ~target:Lg.Target.Melange source with
   | Ok [] -> () | _ -> failwith "JS FFI discovered incorrect packages");
  List.iter (fun target -> reject ~target "requires the Melange target" source)
    [Lg.Target.Native; Lg.Target.Js_of_ocaml];
  List.iter (fun (fragment, source) -> reject ~target:Lg.Target.Melange fragment source)
    [ "nonempty string", "(ffi f [] :int {:js \"\"})";
      "nonempty string", "(ffi f [] :int {:js \"f\" :module 1})";
      "scope", "(ffi f [] :int {:js \"f\" :scope \"Math\"})";
      "scope", "(ffi f [] :int {:js \"f\" :scope [1]})";
      "native", "(ffi f [] :int {:js \"f\" :library \"lib.so\"})";
      "unit parameter", "(ffi f [:unit] :int {:js \"f\"})";
      "JavaScript FFI type", "(ffi f [:vector<int>] :int {:js \"f\"})";
      "JavaScript FFI type", "(ffi f [] :option<int> {:js \"f\"})";
      "JavaScript FFI type", "(ffi f [:unknown-host] :int {:js \"f\"})" ];
  reject ~target:Lg.Target.Melange "argument" (source ^ " (f true)")

let test_javascript_object_rejections () =
  let reject source fragment = reject ~target:Lg.Target.Melange fragment source in
  let box = "(extern-type box) " in
  reject (box ^ "(extern-type box)") "duplicate type";
  reject "(extern-type)" "extern-type expects";
  reject "(ffi f [] :int {:js \"Box\" :kind :new})" "opaque";
  reject (box ^ "(ffi f [] :int {:js \"value\" :kind :get})") "receiver";
  reject (box ^ "(ffi f [:box :int] :int {:js \"value\" :kind :set})") "unit";
  reject (box ^ "(ffi f [:box] :int {:js \"value\" :kind :send :scope [\"x\"]})") "receiver";
  reject (box ^ "(ffi f [:box] :int {:js \"value\" :kind :get :module \"x\"})") "receiver";
  reject (box ^ "(ffi f [:box :bool] :int {:js :get-index})") "index";
  reject (box ^ "(ffi f [:box :string :int] :int {:js :set-index})") "unit";
  reject (box ^ "(ffi f [:box :string] :int {:js :get-index :kind :get})") "kind";
  reject (box ^ "(ffi f [:box] :int {:js \"x\" :kind :unknown})") "kind";
  reject (box ^ "(extern-type other) (ffi make [] :other {:js \"Other\" :kind :new}) (ffi get [:box] :int {:js \"value\" :kind :get}) (get (make))") "box";
  reject (box ^ "(ffi get [:box] :int {:js \"value\" :kind :get}) (get 4)") "box";
  reject "(type-record data (value :int)) (ffi get [:data] :int {:js \"value\" :kind :get})" "JavaScript FFI type";
  let prefix = "(extern-type obj) (type-record input (name :string) (age :option<int>)) " in
  List.iter (fun source -> reject (prefix ^ source) "object")
    [ "(ffi f [:int] :obj {:js :object})";
      "(ffi f [:input] :int {:js :object :optional [:age]})";
      "(ffi f [:input] :obj {:js :object})";
      "(ffi f [:input] :obj {:js :object :optional [:name :age]})";
      "(ffi f [:input] :obj {:js :object :optional [:missing]})";
      "(ffi f [:input] :obj {:js :object :optional [:age :age]})";
      "(ffi f [:input] :obj {:js :object :rename {:missing \"x\"} :optional [:age]})";
      "(ffi f [:input] :obj {:js :object :rename {:name \"age\"} :optional [:age]})";
      "(ffi f [:input] :obj {:js :object :rename {:name \"__proto__\"} :optional [:age]})";
      "(ffi f [:input] :obj {:js :object :scope [\"x\"] :optional [:age]})";
      "(ffi f [:input] :obj {:js :object :variadic true :optional [:age]})" ];
  reject (prefix ^ "(ffi f [:input] :obj {:js \"make\" :optional [:age]})") "object"

let test_javascript_adapter_rejections () =
  let reject source fragment = reject ~target:Lg.Target.Melange fragment source in
  List.iter (fun source -> reject source "variadic")
    [ "(ffi f [] :int {:js \"f\" :variadic true})";
      "(ffi f [:int] :int {:js \"f\" :variadic true})";
      "(ffi f [:array<int>] :int {:js \"f\" :kind :send :variadic true})";
      "(ffi f [:array<int>] :int {:js \"f\" :variadic 1})" ];
  reject "(ffi f [] :int {:js \"f\" :return :nullable})" "option";
  reject "(ffi f [] :option<option<int>> {:js \"f\" :return :nullable})" "JavaScript FFI type";
  reject "(ffi f [] :option<int> {:js \"f\" :return :anything})" "return";
  reject "(ffi f [:fn<option<int>;int>] :int {:js \"f\"})" "JavaScript FFI type";
  reject "(ffi f [:array<int> :int :string] :unit {:js :set-index})" "element";
  reject "(ffi f [:array<int> :int] :string {:js :get-index})" "element";
  reject "(ffi f [:array<int> :string] :int {:js :get-index})" "index"

let test_packages () =
  let source = "(ffi absolute [:int] :int {:native \"abs\"})" in
  List.iter (fun source ->
    match Lg.Compiler.required_ocaml_packages source with
    | Ok packages when List.mem "ctypes-foreign" packages -> ()
    | Ok _ -> failwith "native FFI dependency was not discovered"
    | Error error -> failwith error.message)
    [source; "(module Math " ^ source ^ ")"];
  (match Lg.Compiler.required_ocaml_packages
      "(ffi f [] :int {:ocaml \"app_primitive\"})" with
   | Ok [] -> ()
   | _ -> failwith "OCaml primitive FFI must not add ctypes dependencies");
  match Lg.Compiler.required_ocaml_packages ~target:Lg.Target.Melange
    ("#?(:native " ^ source ^ ")") with
  | Ok [] -> ()
  | _ -> failwith "inactive native binding leaked a package dependency"

let test_integration () =
  List.iter (fun (target, options) ->
    let provider = "(ns ffi.provider) (ffi absolute [:int] :int " ^ options ^ ")" in
    let state, _ = match Lg.Compiler.compile_chunk ~target Lg.Compiler.empty_state provider with
      | Ok value -> value | Error error -> failwith error.message in
    match Lg.Compiler.compile_chunk ~target state
      "(ns ffi.consumer (:require [ffi.provider :as foreign])) (def answer (foreign/absolute -7))" with
    | Ok _ -> () | Error error -> failwith error.message)
    [Lg.Target.Native, "{:native \"abs\"}";
     Lg.Target.Native, "{:ocaml \"app_absolute\"}";
     Lg.Target.Melange, "{:js \"abs\" :scope [\"Math\"]}"];
  let source = "(ffi absolute [:int] :int {:native \"abs\"})" in
  ignore (compile ("(module Math " ^ source ^ ") (def result (Math/absolute -4))"));
  (match Lg.Compiler.infer_interface source with
   | Ok signature when contains signature "int -> int" -> ()
   | Ok signature -> failwith ("incorrect FFI interface: " ^ signature)
   | Error error -> failwith error.message);
  (match Lg.Compiler.compile_chunk Lg.Compiler.empty_state source with
   | Error error -> failwith error.message
   | Ok (state, _) ->
       match Lg.Compiler.compile_chunk state "(def answer (absolute -7))" with
       | Ok _ -> ()
       | Error error -> failwith error.message);
  (match Lg.Compiler.compile_repl_form Lg.Compiler.empty_state source with
   | Ok (_, {kind = Lg.Compiler.Repl_definition {name = "absolute"; _}; _}) -> ()
   | Ok _ -> failwith "FFI REPL form was not classified as a definition"
   | Error error -> failwith error.message)

let test_javascript_incremental_artifact () =
  let target = Lg.Target.Melange in
  (match Lg.Compiler.compile_repl_form ~target Lg.Compiler.empty_state "(extern-type box)" with
   | Ok (_, {kind = Lg.Compiler.Repl_summary _; _}) -> ()
   | Ok _ -> failwith "opaque type was not classified as a declaration"
   | Error error -> failwith ("artifact phase: " ^ error.message));
  let source = "(ffi basename [:string] :string {:js \"basename\" :module \"node:path\"})"
    ^ "(extern-type box) (ffi make-box [:int :string] :box {:js \"Box\" :kind :new})"
    ^ "(ffi box-value [:box] :int {:js \"value\" :kind :get})"
    ^ "(module Objects (type-record input (count :int)) (extern-type object)"
    ^ "(ffi create [:input] :object {:js :object}))" in
  (match Lg.Compiler.infer_interface ~target source with
   | Ok signature when contains signature "string -> string" -> ()
   | Ok signature -> failwith ("incorrect JS FFI interface: " ^ signature)
   | Error error -> failwith ("interface: " ^ error.message));
  let state, output = match Lg.Compiler.compile_chunk ~target Lg.Compiler.empty_state source with
    | Ok result -> result | Error error -> failwith ("chunk: " ^ error.message)
  in
  let path = Filename.temp_file "lg-ffi-state-" ".state" in
  Fun.protect ~finally:(fun () -> Sys.remove path) (fun () ->
    Lg.Compiler_artifact.write ~kind:"ffi-test" ~path (Lg.Compiler.cacheable_state state);
    let restored : Lg.Compiler.state =
      match Lg.Compiler_artifact.read ~kind:"ffi-test" ~path with
      | Ok state -> state | Error message -> failwith message
    in
    let restored =
      match Lg.Compiler.restore_ocaml_environment ~target ~packages:[] restored [ (output, None) ] with
      | Ok state -> state | Error error -> failwith ("restore: " ^ error.message)
    in
    match Lg.Compiler.compile_chunk ~target restored "(def result (box-value (make-box 1 \"one\"))) (def object (Objects/create (Objects/input. 2)))" with
    | Ok _ -> () | Error error -> failwith ("continuation: " ^ error.message))

let test_rejections () =
  List.iter (fun (fragment, source) -> reject fragment source)
    [ "ffi expects", "(ffi abs)";
      "unknown FFI option", "(ffi f [] :int {:native \"abs\" :typo true})";
      "duplicate FFI option", "(ffi f [] :int {:native \"abs\" :native \"labs\"})";
      "nonempty string", "(ffi f [] :int {:native \"\"})";
      "nonempty string", "(ffi f [] :int {:native 1})";
      "nonempty string", "(ffi f [] :int {:native \"abs\" :library false})";
      "exactly one", "(ffi f [] :int {})";
      "exactly one", "(ffi f [] :int {:native \"abs\" :js \"abs\"})";
      "type keyword", "(ffi f [int] :int {:native \"abs\"})";
      "unit parameter", "(ffi f [:unit] :int {:native \"abs\"})";
      "native FFI type", "(ffi f [:vector<int>] :int {:native \"abs\"})";
      "native FFI type", "(ffi f [:option<int>] :int {:native \"abs\"})";
      "string result", "(ffi f [] :string {:native \"getenv\"})";
      "callbacks", "(ffi f [:fn<int>] :int {:native \"f\"})";
      "callbacks", "(ffi f [:fn<int>] :int {:native \"f\" :callbacks :retained})";
      "callback", "(ffi f [:fn<fn<int>;int>] :int {:native \"f\" :callbacks :call})";
      "unit parameter", "(ffi f [:fn<unit;int>] :int {:native \"f\" :callbacks :call})";
      "string result", "(ffi f [:fn<string>] :int {:native \"f\" :callbacks :call})";
      "native FFI type", "(ffi f [] :fn<int> {:native \"f\" :callbacks :call})";
      "owned-pointer", "(ffi close [:pointer<int>] :unit {:native :release})";
      "same signature", "(ffi retain [:fn<int>] :callback<fn<float>> {:native :callback})";
      "same signature", "(ffi retain [:int] :callback<fn<int>> {:native :callback})";
      "native FFI type", "(ffi f [] :callback<fn<int>> {:native \"f\"})";
      "owned-pointer", "(ffi f [] :int {:native \"f\" :ownership :owned :release \"free\"})";
      "ownership", "(ffi f [] :owned-pointer<int> {:native \"f\"})";
      "ownership", "(ffi f [] :pointer<int> {:native \"f\"})";
      "ownership", "(ffi f [] :option<pointer<int>> {:native \"f\"})";
      "ownership", "(ffi f [] :pointer<int> {:native \"f\" :ownership :owned})";
      "pointee", "(ffi f [:pointer<string>] :unit {:native \"f\"})";
      "pointee", "(ffi f [:pointer<fn<int>>] :unit {:native \"f\"})";
      "pointee", "(ffi f [:pointer<vector<int>>] :unit {:native \"f\"})";
      "dynamic is not a source type", "(ffi f [:dynamic] :int {:native \"abs\"})" ];
  reject "argument" "(ffi f [:int] :int {:native \"abs\"}) (f \"x\")";
  reject "float" "(ffi p [] :pointer<int> {:native \"p\" :ownership :borrowed}) (ffi f [:pointer<float>] :unit {:native \"f\"}) (f (p))";
  reject "argument" "(ffi f [:int] :int {:native \"abs\"}) (f)";
  List.iter (fun target ->
    reject ~target "requires the native target"
      "(ffi f [:int] :int {:native \"abs\"})")
    [Lg.Target.Melange; Lg.Target.Js_of_ocaml]

let test_ocaml_primitive_execution () =
  let dir = Filename.temp_dir "lg-ocaml-ffi-" "" in
  Fun.protect ~finally:(fun () -> remove_tree dir) (fun () ->
    let source = {|
(extern-type reader)
(type-record row (addr :int) (content :string) (addresses :option<string>))
(ffi open-reader [:string] :reader {:ocaml "lg_test_reader_open"})
(ffi read-reader [:reader] :string {:ocaml "lg_test_reader_read"})
(ffi first-row [:list<row>] :option<row> {:ocaml "lg_test_first_row"})
(ffi answer [] :int {:ocaml "lg_test_answer"})
|} in
    let generated = compile source in
    if contains generated "Foreign.foreign" || contains generated "Obj.magic" then
      failwith "OCaml primitive must use the typed runtime ABI directly";
    let c = Filename.concat dir "fixture.c" in
    let ml = Filename.concat dir "binding.ml" in
    write c {|
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
CAMLprim value lg_test_reader_open(value text) {
  CAMLparam1(text);
  CAMLlocal1(handle);
  handle = caml_alloc_tuple(1);
  Store_field(handle, 0, text);
  CAMLreturn(handle);
}
CAMLprim value lg_test_reader_read(value handle) {
  CAMLparam1(handle);
  CAMLreturn(Field(handle, 0));
}
CAMLprim value lg_test_first_row(value rows) {
  CAMLparam1(rows);
  CAMLlocal1(result);
  if (rows == Val_emptylist) CAMLreturn(Val_int(0));
  if (Long_val(Field(Field(rows, 0), 0)) < 0) caml_failwith("negative address");
  result = caml_alloc_small(1, 0);
  Field(result, 0) = Field(rows, 0);
  CAMLreturn(result);
}
CAMLprim value lg_test_answer(value unit) { return Val_int(42); }
|};
    write ml (generated ^ {|
let () =
  let text = "abc\000def" in
  let handle = open_reader text in
  Gc.full_major ();
  assert (read_reader handle = text);
  let row = {addr = 7; content = text; addresses = Some "[1,2]"} in
  assert (first_row [row] = Some row);
  assert (first_row [] = None);
  assert (answer () = 42);
  (match first_row [{row with addr = -1}] with
   | exception Failure message -> assert (message = "negative address")
   | _ -> assert false)
|});
    List.iter (fun (compiler, flags) ->
      let executable = Filename.concat dir (compiler ^ ".exe") in
      command (Printf.sprintf "cd %s && %s %s fixture.c binding.ml -o %s"
        (Filename.quote dir) compiler flags (Filename.quote executable));
      command (Filename.quote executable))
      ["ocamlc", "-custom"; "ocamlopt", ""];
    List.iter (fun (fragment, declaration) -> reject fragment declaration)
      ["exactly one", "(ffi f [] :int {:ocaml \"x\" :native \"y\"})";
       "other options", "(ffi f [] :int {:ocaml \"x\" :library \"y\"})";
       "C identifier", "(ffi f [] :int {:ocaml \"%identity\"})";
       "five", "(ffi f [:int :int :int :int :int :int] :int {:ocaml \"x\"})";
       "unit parameter", "(ffi f [:unit] :int {:ocaml \"x\"})"];
    reject "closed static" "(ffi f [:variant-open<Value:int>] :int {:ocaml \"x\"})";
    List.iter (fun target -> reject ~target "native target" source)
      [Lg.Target.Melange; Lg.Target.Js_of_ocaml])


let () =
  List.iter (fun (name, test) ->
    try test (); Printf.printf "ok: %s\n%!" name
    with exn -> Printf.eprintf "FAIL: %s: %s\n%!" name (Printexc.to_string exn); exit 1)
    ["OCaml primitive execution", test_ocaml_primitive_execution;
     "JavaScript execution", test_javascript_execution;
     "JavaScript object validation", test_javascript_object_rejections;
     "JavaScript adapter validation", test_javascript_adapter_rejections;
     "JavaScript validation", test_javascript_validation;
     "JavaScript artifact", test_javascript_incremental_artifact;
     "native execution", test_native_execution;
     "native missing resources", test_native_missing_resources;
     "native dependencies", test_packages;
     "FFI integration", test_integration;
     "FFI rejections", test_rejections]
