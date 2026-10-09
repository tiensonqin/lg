#!/usr/bin/env python3
"""Emit-correctness matrix: for each builtin, generate small lg programs
exercising it over the interesting argument-type combinations and verify
`lg build` (i.e. emitted OCaml actually typechecks).

A green `lg check` must imply a green `lg build` — every FAIL here is an
infer/emit hole. Run: python3 test/emit_matrix.py
"""
import subprocess, sys, tempfile, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LG = os.path.join(ROOT, "_build/default/bin/lg.exe")

PRELUDE = """(def i 3)
(def f 2.5)
(def s "hi")
(def k :kw)
(def c \\x)
(def b true)
(def v [1 2 3])
(def l '(1 2 3))
(def st #{1 2 3})
(def m {:a 1 :b 2})
(def am {:a 1 :s "x"})
(def a ^(any) [1 2])
(def g (fn [x] (inc x)))
(def g2 (fn [acc x] (+ acc x)))
(def p (fn [x] (> x 1)))
(def at (atom 0))
(def o (get m :a))
(def om (get am :a))
"""

# each case: (name, call) — {} placeholders are substituted per column
# columns picked per builtin family
CALLS = [
    # scalars
    ("inc", "{i}", "{a}"), ("dec", "{i}", "{a}"), ("abs", "{i}"), ("mod", "{i} 2"),
    ("float", "{i}", "{a}"), ("int", "{f}", "{a}"),
    ("=", "{i} {i}", "{v} {v}", "{m} {m}", "{st} {st}", "{l} {l}", "{a} {a}", "{o} {o}", "{s} {s}", "{g} {g}", "{i} {a}"),
    ("not=", "{i} {i}", "{v} {v}", "{m} {m}", "{a} {a}", "{o} {o}", "{g} {g}"),
    ("<", "{i} {i}", "{f} {f}", "{s} {s}", "{a} {a}"),
    (">", "{i} {i}", "{f} {f}", "{s} {s}", "{a} {a}"),
    ("<=", "{i} {i}", "{s} {s}", "{a} {a}"),
    (">=", "{i} {i}", "{s} {s}", "{a} {a}"),
    ("not", "{b}", "{a}", "{i}"),
    ("identity", "{i}", "{a}", "{v}"),
    ("constantly", "{i} {a}"),
    # literals + conversion
    ("list", "{i} {i} {i}", "{a} {i}"),
    ("vector", "{i} {i}", "{a} {i}"),
    ("hash-set", "{i} {i}", "{a} {i}"),
    ("hash-map", "{k} {i}", "{k} {a}"),
    ("vec", "{l}", "{st}", "{a}", "{s}"),
    ("set", "{l}", "{v}", "{a}"),
    ("cons", "{i} {l}", "{a} {l}", "{i} {a}"),
    ("concat", "{l} {l}", "{v} {v}", "{v} {l}", "{st} {l}", "{a} {a}", "{s} {s}"),
    # collection inspection
    ("empty?", "{v}", "{l}", "{st}", "{m}", "{s}", "{a}"),
    ("count", "{v}", "{l}", "{st}", "{m}", "{s}", "{a}"),
    ("first", "{v}", "{l}", "{st}", "{s}", "{a}"),
    ("second", "{v}", "{l}", "{a}"),
    ("last", "{v}", "{l}", "{a}"),
    ("butlast", "{v}", "{l}", "{a}"),
    ("next", "{v}", "{l}", "{a}"),
    ("rest", "{v}", "{l}", "{a}"),
    ("seq", "{v}", "{l}", "{st}", "{m}", "{s}", "{a}"),
    ("peek", "{v}", "{l}", "{a}"),
    ("pop", "{v}", "{l}", "{a}"),
    ("keys", "{m}", "{am}", "{a}"),
    ("vals", "{m}", "{am}", "{a}"),
    ("contains?", "{v} {i}", "{l} {i}", "{st} {i}", "{m} {k}", "{s} {c}", "{a} {a}"),
    ("get", "{v} 0", "{l} 0", "{m} {k}", "{m} {k} 9", "{st} {i}", "{a} {k}", "{a} {k} {a}", "{am} {k}", "{am} {k} {a}"),
    ("nth", "{v} 0", "{v} 0 9", "{l} 0", "{l} 0 9", "{s} 0", "{a} 0", "{a} 0 {a}"),
    # collection update
    ("conj", "{v} {i}", "{l} {i}", "{st} {i}", "{v} {a}", "{a} {a}", "{v} {i} {i}"),
    ("assoc", "{v} 0 {i}", "{m} {k} {i}", "{am} {k} {a}", "{a} {k} {a}"),
    ("dissoc", "{m} {k}", "{am} {k}", "{a} {k}"),
    ("disj", "{st} {i}", "{a} {a}"),
    ("union", "{st} {st}", "{a} {a}"),
    ("merge", "{m} {m}", "{am} {am}", "{a} {a}"),
    ("into", "{v} {l}", "{l} {v}", "{st} {v}", "{m} [[:a 9]]", "{m} '(([:a 9]))", "{am} {m}", "{a} {a}", "{v} {a}"),
    ("select-keys", "{m} [:a]", "{am} [:a]", "{a} [:a]"),
    ("update", "{m} {k} {g}", "{m} {k} {g} {i}", "{am} {k} {g}"),
    ("get-in", "{m} [:a]", "{m} [:a] 9", "{am} [:a]", "{a} [:a]", "{m} {v}"),
    ("assoc-in", "{m} [:a] {i}", "{am} [:a] {a}", "{a} [:a] {a}"),
    # higher order
    ("map", "{g} {v}", "{g} {l}", "{g} {st}", "{g} {a}", "{p} {a}"),
    ("mapv", "{g} {v}", "{g} {l}", "{g} {a}"),
    ("filter", "{p} {v}", "{p} {l}", "{p} {a}"),
    ("filterv", "{p} {v}", "{p} {a}"),
    ("reduce", "{g2} {i} {v}", "{g2} {i} {l}", "{g2} {i} {a}"),
    ("mapcat", "{g} {v}", "{g} {a}"),
    ("apply", "{g} {v}", "{g} {l}", "{g} {a}", "{g2} {i} {l}"),
    ("comp", "{g} {g}", "{g} {g}"),
    ("juxt", "{g} {g}", "{g} {p}"),
    ("partial", "{g2} {i}", "{g2} {a}"),
    ("every?", "{p} {v}", "{p} {a}"),
    ("some", "{p} {v}", "{p} {a}"),
    ("take-while", "{p} {v}", "{p} {a}"),
    ("drop-while", "{p} {v}", "{p} {a}"),
    # seq ops
    ("take", "1 {v}", "1 {l}", "1 {st}", "1 {s}", "1 {a}"),
    ("drop", "1 {v}", "1 {l}", "1 {st}", "1 {s}", "1 {a}"),
    ("interpose", "{i} {v}", "{i} {a}"),
    ("reverse", "{v}", "{l}", "{a}"),
    ("distinct", "{v}", "{l}", "{a}"),
    ("sort", "{v}", "{l}", "{a}"),
    ("sort-by", "{g} {v}", "{g} {a}"),
    ("group-by", "{p} {v}", "{g} {a}"),
    ("frequencies", "{v}", "{l}", "{a}"),
    ("zipmap", "{v} {v}", "{l} {l}", "{a} {a}"),
    ("min", "{i} {i}", "{a} {a}", "{i} {f}"),
    ("max", "{i} {i}", "{a} {a}", "{i} {f}"),
    ("range", "3", "0 5", "0 5 2"),
    ("vector", "{i} {i}", "{a} {i}"),
    ("hash-map", "{k} {i}", "{k} {a}"),
    ("hash-set", "{i} {i}", "{a} {i}"),
    # atoms
    ("atom", "{i}", "{a}", "{v}"),
    ("deref", "{at}"),
    ("reset!", "{at} {i}", "{at} {a}"),
    ("swap!", "{at} {g}"),
    # printing
    ("str", "{i}", "{s}", "{v}", "{m}", "{a}", "{o}", "{g}", "{i} {s} {a}", "{c}", "{f}"),
    ("name", "{k}", "{a}"),
    ("keyword", "{s}", "{a}"),
    ("symbol", "{s}", "{a}"),
    ("println", "{i}", "{s}", "{v}", "{a}", "{o}", "{g}"),
    ("print", "{i}", "{a}"),
    ("pr-str", "{i}", "{a}"),
    # predicates on everything
    ("int?", "{i}", "{a}", "{v}", "{s}"),
    ("float?", "{f}", "{a}", "{i}"),
    ("bool?", "{b}", "{a}", "{i}"),
    ("char?", "{c}", "{a}", "{i}"),
    ("string?", "{s}", "{a}", "{i}"),
    ("keyword?", "{k}", "{a}", "{i}"),
    ("symbol?", "{a}", "{s}"),
    ("list?", "{l}", "{a}", "{v}"),
    ("vec?", "{v}", "{a}", "{l}"),
    ("set?", "{st}", "{a}", "{v}"),
    ("map?", "{m}", "{a}", "{v}"),
    ("seq?", "{l}", "{a}", "{v}"),
    ("coll?", "{v}", "{a}", "{i}"),
    ("number?", "{i}", "{f}", "{a}", "{s}"),
    ("nil?", "{a}", "{o}", "{i}"),
    ("some?", "{o}", "{a}", "{i}"),
    ("none?", "{o}", "{a}", "{i}"),
    ("fn?", "{g}", "{a}", "{i}"),
    ("zero?", "{i}", "{a}"),
    ("pos?", "{i}", "{a}"),
    ("neg?", "{i}", "{a}"),
    ("even?", "{i}", "{a}"),
    ("odd?", "{i}", "{a}"),
    # special forms as values / tricky positions
    ("if", "{b} 1 2", "{a} 1 2", "{o} 1 2"),
    ("and", "{b} {b}", "{a} {b}", "{b} {a}", "{a} {a}"),
    ("or", "{b} {b}", "{a} {b}", "{a} {a}"),
    ("when", "{b} (println 1)", "{a} (println 1)"),
    ("let", "[x {a}] x", "[x {o}] x"),
    ("match", "{a} [x] x _ 0", "{o} (Some x) x _ 0", "{a} (Some x) x _ 0", "{a} {:a n} n _ 0", "{i} 1 \"one\" _ 0"),
    ("case", "{i} 1 \"one\" 2 \"two\" \"other\"", "{k} :a 1 :b 2 0"),
]

def run_case(name, call):
    import re
    args = re.sub(r"\{(\w+)\}", r"\1", call)
    body = PRELUDE + "(println (str ({} {})))\n(exit 0)\n".format(name, args)
    with tempfile.NamedTemporaryFile("w", suffix=".lg", delete=False) as fh:
        fh.write(body)
        path = fh.name
    out = path + ".bin"
    r = subprocess.run([LG, "check", path, "-I", os.path.join(ROOT, "lib")],
                       capture_output=True, text=True)
    if r.returncode != 0:
        # check-rejected: fine — infer rightly rejects; not an emit hole
        return "reject", r.stderr.strip().splitlines()[-1] if r.stderr.strip() else ""
    r = subprocess.run([LG, "build", path, "-I", os.path.join(ROOT, "lib"), "-o", out],
                       capture_output=True, text=True)
    if r.returncode != 0:
        err = (r.stderr or r.stdout).strip()
        lines = [l for l in err.splitlines() if "Error" in l or "error" in l]
        return "FAIL", (lines[0] if lines else err.splitlines()[-1] if err else "?")
    return "ok", ""

def main():
    fails, checks, oks, rejects = [], 0, 0, 0
    for name, *calls in CALLS:
        for call in calls:
            checks += 1
            status, detail = run_case(name, call)
            tag = "({} {})".format(name, call)
            if status == "FAIL":
                fails.append((tag, detail))
            elif status == "ok":
                oks += 1
            else:
                rejects += 1
    print("matrix: {} cases — {} ok, {} infer-rejected, {} emit FAILs".format(checks, oks, rejects, len(fails)))
    for tag, detail in fails:
        print("  FAIL {:32} {}".format(tag, detail[:100]))
    sys.exit(1 if fails else 0)

if __name__ == "__main__":
    main()
