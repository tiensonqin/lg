(* Core library reference — special forms and builtin docstrings,
   rendered as core.html by `lg doc`. Signatures are written in lg type
   syntax; entries whose registered type is a placeholder carry an
   explicit signature here. Keep in sync with Infer.builtin_table. *)

(* (name, signature, doc) — reader/infer forms, not builtins *)
let special_forms : (string * string * string) list =
  [ "def", "(def name \"doc\"? expr)",
    "Bind NAME to the value of EXPR at module top level. The type is \
     inferred and generalized; an optional docstring precedes EXPR.";
    "defn", "(defn name \"doc\"? [params] body…)",
    "Define a function. Sugar for (def name (fn [params] body…)). Multi-arity \
     (defn f ([x] …) ([x y] …)) dispatches on argument count.";
    "defmacro", "(defmacro name \"doc\"? [params] body…)",
    "Define a compile-time macro. Receives unevaluated argument forms and \
     returns a form; multi-arity clauses are supported like defn.";
    "defvariant", "(defvariant (name 'a…) \"doc\"? (ctor field…)…)",
    "Define a closed variant type with named constructors. Constructors \
     become functions; `match` on the type warns on missing ctors.";
    "declare", "(declare ^(fn [t…] r) name)",
    "Forward-declare NAME's type for mutual recursion or to pin a concrete \
     signature that inference would widen (e.g. a collection parameter).";
    "extern-type", "(extern-type name)",
    "Declare an opaque handle type for values that cross the ocaml.* interop \
     boundary (e.g. (extern-type conn) for a socket).";
    "ffi", "(ffi name [arg…] ret {:ocaml \"M.f\" | :native \"c\" | :js \"f\"})",
    "Bind an external function directly — no wrapper. The module requires \
     the matching backend (ocaml.pkg/native lib/js).";
    ":require", "(:require [ns :as alias] [ocaml.Mod] [mod :refer (n…)])",
    "Module-level import: lg modules qualify as ns/name, OCaml library \
     modules as ocaml.Mod members (e.g. olist/find).";
    "fn", "(fn name? [params] body…) | (fn ([x] …) ([x y] …))",
    "Anonymous function; an optional name enables self-recursion (named fn \
     compiles to `let rec`, native TCO applies).";
    "let", "(let [name expr …] body…)",
    "Sequential binding pairs; later bindings see earlier names. `name` may \
     destructure a tuple [a b], vector [a & r], or map {k v}.";
    "if", "(if cond then else?)",
    "Two-branch conditional; a missing else yields unit. Branch types join \
     per §4 (unit widens to option).";
    "cond", "(cond test expr … :else expr)",
    "Ordered multi-branch conditional; evaluates tests in order, returns the \
     first matching expr, :else as the default.";
    "case", "(case e (pattern… result)…)",
    "Match an expression against literal values (atoms); arms with several \
     patterns share one result.";
    "match", "(match scrutinee (pattern expr)…)",
    "Structural pattern match: literals, binders, [vec] {map} destructuring, \
     option (Some x)/None, variant ctors, & rest in vector patterns. \
     Non-exhaustive matches warn W401/W402.";
    "do", "(do expr…)",
    "Evaluate expressions in order; the value is the last one.";
    "and", "(and expr…)",
    "Left-to-right short-circuit; returns the first falsy value or the last.";
    "or", "(or expr…)",
    "Left-to-right short-circuit; returns the first truthy value or the last.";
    "when", "(when cond body…)",
    "Evaluate body when cond is truthy; otherwise unit.";
    "when-let", "(when-let [name expr] body…)",
    "Bind NAME to the Some payload of EXPR and run body when it matches \
     (Some name); unit otherwise.";
    "if-let", "(if-let [name expr] then else?)",
    "Like when-let with an else branch taken when EXPR is not (Some name).";
    "try", "(try body… (catch e handler…) (finally f…))",
    "Real OCaml exceptions: BODY runs inside try..with; E binds the opaque \
     exn handle for HANDLER; FINALLY always runs (Fun.protect), its value \
     discarded. The try's value joins body and handler.";
    "quote", "(quote form) | 'form",
    "Return FORM unevaluated as data (symbols, lists, literals).";
    "quasiquote", "`form  with  ~unquote  ~@unquote-splicing",
    "Templated form construction: ` quotes, ~ evaluates a subform, ~@ \
     splices a seqable's elements in place.";
    "->", "(-> x (f a) (g b)) = (g (f x a) b)",
    "Thread-first: insert X as the first argument of each successive form; \
     desugars at read time.";
    "->>", "(->> x (f a) (g b)) = (g b (f x a))",
    "Thread-last: insert X as the last argument of each successive form; \
     desugars at read time.";
    "&", "[a b & rest]",
    "Rest parameter: in fn/defn/defmacro params and vector match patterns, \
     binds the remaining elements as a list.";
    "#_", "#_form",
    "Reader discard: the next form is read and dropped — no value, no \
     evaluation." ]

(* (name, signature override option, doc) — one row per Infer.builtin_table
   entry; overrides cover variadic and per-call-typed builtins whose
   registered scheme is a placeholder. *)
let builtins : (string * string option * string) list =
  [ "*", None, "Product of all arguments. ( * ) = 1";
    "*.", None, "Product as floats.";
    "+", None, "Sum of all arguments. ( + ) = 0";
    "+.", None, "Sum as floats.";
    "-", None, "(x), (x y), or (x y more): negation or left-fold subtraction.";
    "-.", None, "Subtraction as floats.";
    "/", None, "Left-fold integer division; (x) = 1/x.";
    "/.", None, "Division as floats.";
    "<", None, "Ordered comparison; chains pairwise.";
    "<=", None, "Ordered comparison; chains pairwise.";
    "=", None, "Value equality; chains pairwise.";
    ">", None, "Ordered comparison; chains pairwise.";
    ">=", None, "Ordered comparison; chains pairwise.";
    "abs", None, "Absolute value.";
    "apply", Some "(apply f arg… coll)", "Call F with leading args plus the elements of COLL appended.";

    "assoc", Some "(assoc m k v k2 v2…)", "Return M with each key mapped to its value; on vectors, index-position updates.";
    "assoc-in", Some "(assoc-in m [k…] v)", "Nested assoc along the key path, creating maps as needed.";
    "atom", None, "Create a mutable cell holding X. Read with deref, write with reset!/swap!.";

    "bool?", None, "True when the argument is a bool.";
    "butlast", None, "All elements but the last, as a lazy seq.";
    "char?", None, "True when the argument is a char.";
    "coll?", None, "True for vec/list/seq/map/set.";
    "comp", Some "(comp f g …)", "Right-to-left function composition: (comp f g) x = f (g x).";
    "concat", Some "(concat coll…)", "Lazy seq concatenating the elements of each argument.";
    "conj", Some "(conj coll x…)", "Add elements: front for lists, back for vectors, by key for sets/maps.";
    "cons", None, "Prepend X to a seqable; returns a lazy seq.";
    "constantly", None, "A function of any arguments that always returns X.";
    "contains?", Some "(contains? coll k) -> bool", "Membership: map key, set element, or vector index.";
    "count", Some "(count coll) -> int", "Element count of a collection or string length.";
    "cycle", None, "Lazy seq repeating the collection's elements forever.";
    "dec", None, "One less than the argument.";
    "dedupe", None, "Lazy seq with consecutive duplicates removed.";
    "deref", None, "Current value of an atom. `@a` reads the same.";
    "disj", None, "Set without the given elements.";
    "dissoc", None, "Map without the given keys.";
    "distinct", None, "Lazy seq with duplicate elements removed (first occurrence kept).";
    "doall", Some "(doall s) -> (seq 'a)", "Force realization of a lazy seq; returns the seq.";
    "dorun", Some "(dorun s) -> unit", "Force a lazy seq for side effects; returns unit.";
    "drop", None, "Lazy seq without the first N elements.";
    "drop-last", None, "Lazy seq without the last N elements (default 1).";
    "drop-while", Some "(drop-while pred coll)", "Lazy seq starting after the leading run where PRED holds.";
    "empty?", Some "(empty? coll) -> bool", "True for empty collections and strings.";


    "even?", None, "True for even integers.";
    "every?", Some "(every? pred coll)", "True when PRED holds for all elements (vacuously true on empty).";
    "exit", None, "Terminate the process with status N.";
    "exn", Some "(exn msg) -> exn", "Construct an exception value (Stdlib.Failure); raise with throw.";
    "exn-message", None, "Render an exn handle via Printexc.to_string.";

    "filter", Some "(filter pred coll)", "Lazy seq of elements where PRED holds.";
    "filter-map", Some "(filter-map f coll)", "Lazy seq of the Some results of F; alias: keep.";
    "filterv", Some "(filterv pred coll)", "Vector of elements where PRED holds (eager).";
    "first", Some "(first coll) -> (option 'a)", "First element as (option t), or None when empty.";
    "float", None, "Coerce to float.";
    "float?", None, "True when the argument is a float.";
    "fn?", None, "True when the argument is a function.";
    "frequencies", Some "(frequencies coll)", "Map from element to occurrence count.";
    "get", Some "(get m k default?)", "Value at key/index; default (or None-typed miss) when absent. Vectors index by position.";
    "get-in", Some "(get-in m [k…] default?)", "Nested get along the key path.";
    "group-by", Some "(group-by f coll)", "Map from (f x) to the list of elements sharing it.";
    "identity", None, "The argument unchanged.";
    "inc", None, "One more than the argument.";

    "int", None, "Coerce to int (truncates floats).";
    "int?", None, "True when the argument is an int.";
    "interleave", Some "(interleave c1 c2 …)", "Lazy seq alternating elements until any input ends.";
    "interpose", Some "(interpose sep coll)", "Seq of elements with SEP between each pair.";
    "into", Some "(into to from)", "Conj all elements of FROM into TO's collection type.";
    "iterate", Some "(iterate f x)", "Lazy seq x, (f x), (f (f x)), …";

    "juxt", Some "(juxt f g …)", "A function returning a vector of each F's result on its args.";
    "keep", Some "(keep f coll)", "Alias of filter-map.";
    "keys", None, "List of a map's keys.";
    "keyword", None, "Keyword from a string (\":k\" or \"k\").";
    "keyword?", None, "True when the argument is a keyword.";
    "kw-get", Some "(:key m)", "Keywords are functions of maps: (:k m) = (get m :k).";
    "last", Some "(last coll) -> (option 'a)", "Last element as (option t), or None when empty.";
    "lazy-seq", Some "(lazy-seq body)", "Delay a seq-producing computation until the seq is walked.";
    "list", None, "List of the arguments.";
    "list?", None, "True when the argument is a list.";

    "map", Some "(map f coll)", "Lazy seq of (f x) per element. Use mapv for an eager vector.";
    "map-indexed", Some "(map-indexed f coll)", "Lazy seq of (f i x) with zero-based index.";
    "map?", None, "True when the argument is a map.";
    "mapcat", Some "(mapcat f coll)", "Lazy seq concatenating (f x) results.";
    "mapv", Some "(mapv f coll)", "Vector of (f x) per element (eager).";
    "max", None, "Larger of the two arguments.";
    "merge", None, "Left-to-right union of maps; later keys win.";
    "min", None, "Smaller of the two arguments.";
    "mod", None, "Integer remainder (sign of the divisor, like OCaml mod).";
    "name", None, "String name of a keyword or symbol, without the namespace.";
    "neg?", None, "True for negative numbers.";
    "next", Some "(next coll) -> (option (seq 'a))", "Rest of the seqable as (option (seq t)); None at the end.";
    "none?", None, "True for None/() — the absent option or unit.";
    "not", None, "Logical negation of a bool.";
    "not-empty", Some "(not-empty coll) -> (option coll)", "The collection unchanged, or None when empty.";
    "not=", None, "Value inequality; chains pairwise.";

    "nth", Some "(nth coll i not-found?)", "Element at index I; NOT-FOUND (or a crash) when out of range. Seqs index from 0.";
    "nthrest", Some "(nthrest coll n)", "The seq after dropping N elements.";
    "number?", None, "True for int or float.";
    "odd?", None, "True for odd integers.";
    "partial", Some "(partial f arg…)", "F with leading arguments bound: (partial f a) x = f a x.";
    "partition", Some "(partition n coll)", "Lazy seq of n-element groups; a short tail is dropped.";
    "partition-all", Some "(partition-all n coll)", "Lazy seq of n-element groups, final partial group kept.";
    "peek", Some "(peek v) -> (option 'a)", "Last element of a vector as (option t).";
    "pop", Some "(pop v) -> (vec 'a)", "Vector without its last element.";
    "pos?", None, "True for positive numbers.";
    "pr-str", None, "The value printed readably (like `println` without output).";
    "print", Some "(print x…)", "Print arguments without a trailing newline.";
    "println", Some "(println x…)", "Print arguments space-separated with a newline.";
    "range", Some "(range end?) | (range start end step?)", "Lazy seq of ints [start..end) stepping by STEP (defaults 0/end/1).";






    "reduce", Some "(reduce f init? coll)", "Left fold; without INIT uses the first element.";
    "reductions", Some "(reductions f init coll)", "Lazy seq of intermediate reduce results.";
    "remove", Some "(remove pred coll)", "Lazy seq of elements where PRED fails.";
    "repeat", Some "(repeat n? x)", "Lazy seq of X repeated N times (forever without N).";
    "repeatedly", Some "(repeatedly n? f)", "Lazy seq of (f) results, N times (forever without N).";

    "reset!", None, "Set the atom's value; returns the new value.";
    "rest", Some "(rest coll) -> (seq 'a)", "The seqable without its first element.";
    "reverse", None, "Elements in reverse order, realized to the result's collection type.";
    "second", Some "(second coll) -> (option 'a)", "Second element as (option t), or None.";
    "select-keys", Some "(select-keys m [k…])", "Map with only the listed keys.";
    "seq", Some "(seq coll) -> (seq 'a)", "The collection as a lazy seq, or () when empty.";
    "seq?", None, "True when the argument is a seq.";
    "set", None, "Set containing the collection's elements.";
    "set?", None, "True when the argument is a set.";


    "some", Some "(some pred coll)", "First element where PRED holds as (option t), else None.";
    "some?", None, "True for any value except None/().";
    "sort", Some "(sort cmp? coll)", "Lazy seq sorted ascending; optional comparator.";
    "sort-by", Some "(sort-by keyfn coll)", "Lazy seq sorted by (keyfn x).";


    "split-at", Some "(split-at n coll) -> (tuple (seq 'a) (seq 'a))", "First N elements and the rest, as a pair of lazy seqs.";
    "split-with", Some "(split-with pred coll)", "(tuple (seq t) (seq t)) — leading PRED-run and the rest.";

    "str", Some "(str x…)", "Concatenate the arguments' printed forms.";
    "string?", None, "True when the argument is a string.";

    "swap!", Some "(swap! a f arg…)", "Set the atom to (f old arg…); returns the new value.";
    "symbol", None, "Symbol from a string.";
    "symbol?", None, "True when the argument is a symbol.";
    "take", None, "Lazy seq of the first N elements.";
    "take-last", None, "List of the last N elements.";
    "take-nth", Some "(take-nth n coll)", "Lazy seq of every Nth element.";
    "take-while", Some "(take-while pred coll)", "Lazy seq of the leading run where PRED holds.";
    "throw", Some "(throw e)", "Raise an exn handle (see exn); caught by try/catch.";



    "tuple", Some "(tuple x…)", "Fixed-size heterogeneous tuple (emits an OCaml tuple).";

    "unit?", None, "True for the unit value ().";
    "update", Some "(update m k f arg…)", "Map with key K's value replaced by (f old arg…).";
    "update-in", Some "(update-in m [k…] f arg…)", "Nested update along the key path.";

    "vals", None, "List of a map's values.";
    "vec", None, "Vector containing the collection's elements.";
    "vec?", None, "True when the argument is a vector.";
    "zero?", None, "True for numeric zero.";
    "zipmap", Some "(zipmap keys vals)", "Map pairing each key with the value at the same index." ]

(* builtin namespaces — (full ns, conventional alias, entries); keeps in
   sync with Infer.builtin_ns. Entries resolve only qualified:
   (:require [lg.str :as str]) then (str/join ...), or full lg.str/join. *)
let ns_builtins : (string * string * (string * string option * string) list) list =
  [ "lg.str", "str",
    [ "blank?", None, "True for strings that are empty or whitespace-only.";
      "ends-with?", None, "True when the string ends with the suffix.";
      "includes?", None, "True when the string contains the substring.";
      "join", Some "(str/join sep? coll)", "Concatenate elements into a string with optional separator.";
      "lower-case", None, "String lower-cased (ASCII).";
      "re-find", None, "First Str regexp match as (option string), None when absent.";
      "re-matches", None, "Whole-string Str regexp match as (option string).";
      "re-replace", Some "(str/re-replace pattern s replacement)", "Replace every Str match in S; \\1…\\9 refer to \\( \\) groups.";
      "re-seq", None, "List of all Str regexp matches in order.";
      "re-split", None, "Split the string on Str regexp matches.";
      "replace", Some "(str/replace s from to)", "String with every occurrence of FROM substituted.";
      "split", Some "(str/split s sep)", "List of substrings of S around literal SEP.";
      "starts-with?", None, "True when the string starts with the prefix.";
      "subs", Some "(str/subs s start end?)", "Substring [start..end) (to the end without END).";
      "trim", None, "String without leading and trailing whitespace.";
      "triml", None, "String without leading whitespace.";
      "trimr", None, "String without trailing whitespace.";
      "upper-case", None, "String upper-cased (ASCII)." ];
    "lg.io", "io",
    [ "argv", Some "(io/argv) -> (list string)", "Command-line arguments after the program name.";
      "env", Some "(io/env name) -> (option string)", "Process environment variable, or None when unset.";
      "file-exists?", None, "True when the path exists on disk.";
      "now-ms", Some "(io/now-ms) -> int", "Milliseconds since the Unix epoch.";
      "read-line", Some "(io/read-line) -> (option string)", "One line from stdin (empty string at EOF).";
      "sh", Some "(io/sh cmd) -> string", "Run CMD through /bin/sh; returns captured stdout.";
      "slurp", None, "Whole file contents as a string.";
      "spit", None, "Write the string to the file (overwrites)." ];
    "lg.set", "set",
    [ "difference", Some "(set/difference s1 s2)", "Elements of S1 not in S2.";
      "intersection", Some "(set/intersection s1 s2)", "Elements present in both sets.";
      "select", Some "(set/select pred s)", "Set of the elements where PRED holds.";
      "subset?", Some "(set/subset? s1 s2)", "True when every element of S1 is in S2.";
      "superset?", Some "(set/superset? s1 s2)", "True when every element of S2 is in S1.";
      "union", Some "(set/union s1 s2)", "Set union — elements of either set." ] ]
