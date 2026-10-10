#!/usr/bin/env python3
"""Generate the builtin x collection-kind golden matrix (stability.md 4.2).

Emits two artifacts:
  test/collmatrix.lg      — every ALLOWED cell, one tagged println each.
  should_fail/cm_*.lg     — every FORBIDDEN cell: the call must fail
                            `lg check` with a static type error, and the
                            paired .err ERE pins the error class.

Run: python3 test/gen_collmatrix.py   (regenerates all artifacts)
Then build+run test/collmatrix to refresh test/collmatrix.out.
"""
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

PRELUDE = """;; GENERATED FILE — do not edit by hand.
;; Source: test/gen_collmatrix.py (builtin x collection-kind matrix).
;; Regenerate with: python3 test/gen_collmatrix.py
(def v [1 2 3])
(def l (list 1 2 3))
(def sq (take 3 v))
(def st #{1 2 3})
(def m {:a 1 :b 2})
(def dm ^any {:a 1 :b 2})
(def dv ^any [1 2 3])
"""

NEG_PRELUDE = """;; GENERATED FILE — do not edit by hand. See test/gen_collmatrix.py.
(def v [1 2 3])
(def l (list 1 2 3))
(def sq (take 3 v))
(def st #{1 2 3})
(def m {:a 1 :b 2})
(def dm ^any {:a 1 :b 2})
(def dv ^any [1 2 3])
"""

KINDS = ["vec", "list", "seq", "map", "set", "dyn"]

# Allowed cells: builtin -> kind -> call expression (arg baked in).
# Forbidden cells: builtin -> kind -> ERE for the static error.
# A kind absent from both dicts is simply not exercised.
MATRIX = {
    "map": {
        "vec": "(map inc v)",
        "list": "(map inc l)",
        "seq": "(map inc sq)",
        "map": "(map (fn [e] e) m)",            # iterates (k v) entries
        "set": "(sort (map inc st))",
        "dyn": "unsupported collection type any",
    },
    "first": {
        "vec": "(first v)",
        "list": "(first l)",
        "seq": "(first sq)",
        "map": "(first m)",                     # first entry tuple
        "set": "(first (sort st))",
        "dyn": "unsupported collection type any",
    },
    "count": {
        "vec": "(count v)", "list": "(count l)", "seq": "(count sq)",
        "map": "(count m)", "set": "(count st)",
        "dyn": "unsupported collection type any",
    },
    "get": {
        "vec": "(get v 1)", "list": "(get l 1)", "seq": "(get sq 1)",
        "map": "(get m :a)", "set": "(get st 2)",
        "dyn": "unsupported collection type any",
    },
    "conj": {
        "vec": "(conj v 4)", "list": "(conj l 0)", "seq": "(conj sq 0)",
        "map": "(conj m [:c 3])", "set": "(conj st 4)",
        "dyn": "unsupported collection type any",
    },
    "take": {
        "vec": "(take 2 v)", "list": "(take 2 l)", "seq": "(take 2 sq)",
        "map": "(take 1 m)", "set": "(sort (take 2 st))",
        "dyn": "unsupported collection type any",
    },
    "drop": {
        "vec": "(drop 1 v)", "list": "(drop 1 l)", "seq": "(drop 1 sq)",
        "map": "(drop 1 m)", "set": "(sort (drop 1 st))",
        "dyn": "unsupported collection type any",
    },
    "into": {
        "vec": "(into v (list 9))", "list": "(into l [9])",
        "seq": "(into sq (list 9))", "map": "(into m {:c 3})",
        "set": "(into st [4])",
        "dyn": "into expects a collection destination",
    },
    "seq": {
        "vec": "(seq v)", "list": "(seq l)", "seq": "(seq sq)",
        "map": "(seq m)", "set": "(seq st)",
        "dyn": "unsupported collection type any",
    },
    "reverse": {
        "vec": "(reverse v)", "list": "(reverse l)", "seq": "(reverse sq)",
        "map": "(reverse m)", "set": "(sort (reverse st))",
        "dyn": "unsupported collection type any",
    },
    "sort": {
        "vec": "(sort v)", "list": "(sort l)", "seq": "(sort sq)",
        "map": "sort on map", "set": "(sort st)",
        "dyn": "unsupported collection type any",
    },
    "contains?": {
        "vec": "(contains? v 1)", "list": "(contains? l 1)",
        "seq": "(contains? sq 1)", "map": "(contains? m :a)",
        "set": "(contains? st 2)",
        "dyn": "unsupported collection type any",
    },
    # coll-mutating builtins: the allowed/forbidden split differs —
    # assoc rejects list/set/any statically; the dyn-path family
    # (update/merge/select-keys) accepts `any` and dispatches on the
    # runtime tag.
    "assoc": {
        "vec": "(assoc v 0 9)", "map": "(assoc m :c 3)",
        "list": "assoc not supported on list",
        "seq": "assoc not supported",
        "set": "assoc not supported on set",
        "dyn": "unsupported collection type any",
    },
    "update": {
        "map": "(update m :a inc)",
        "dyn": "(update dm :a inc)",
        "vec": "type mismatch: \\(vec int\\) vs \\(map",
        "list": "type mismatch: \\(int list\\) vs \\(map",
        "seq": "type mismatch: int vs \\(tuple",
        "set": "type mismatch: \\(set int\\) vs \\(map",
    },
    "merge": {
        "map": "(merge m {:c 3})",
        "dyn": "(merge dm {:c 3})",
        "vec": "type mismatch: \\(vec int\\) vs \\(map",
        "list": "type mismatch: \\(int list\\) vs \\(map",
        "seq": "type mismatch: int vs \\(tuple",
        "set": "type mismatch: \\(set int\\) vs \\(map",
    },
    "select-keys": {
        "map": "(select-keys m [:a])",
        "dyn": "(select-keys dm [:a])",
        "vec": "type mismatch: \\(vec int\\) vs \\(map",
        "list": "type mismatch: \\(int list\\) vs \\(map",
        "seq": "type mismatch: int vs \\(tuple",
        "set": "type mismatch: \\(set int\\) vs \\(map",
    },
}

# the argument actually tested for each kind inside should_fail files —
# mirror of the allowed-cell calls where the probe runs the same shape
NEG_CALLS = {
    "map":       {"vec": "(map inc dv)", "list": "(map inc dv)", "seq": "(map inc dv)",
                  "map": "(map inc dv)", "set": "(map inc dv)", "dyn": "(map inc dv)"},
    "first":     {"dyn": "(first dv)"},
    "count":     {"dyn": "(count dv)"},
    "get":       {"dyn": "(get dv 0)"},
    "conj":      {"dyn": "(conj dv 9)"},
    "take":      {"dyn": "(take 2 dv)"},
    "drop":      {"dyn": "(drop 1 dv)"},
    "into":      {"dyn": "(into dv [9])"},
    "seq":       {"dyn": "(seq dv)"},
    "reverse":   {"dyn": "(reverse dv)"},
    "sort":      {"map": "(sort m)", "dyn": "(sort dv)"},
    "contains?": {"dyn": "(contains? dv 0)"},
    "assoc":     {"list": "(assoc l 0 9)", "seq": "(assoc sq 0 9)",
                  "set": "(assoc st 1 9)", "dyn": "(assoc dv 0 9)"},
    "update":    {"vec": "(update v 0 inc)", "list": "(update l 0 inc)",
                  "seq": "(update sq 0 inc)", "set": "(update st 1 inc)"},
    "merge":     {"vec": "(merge v [4])", "list": "(merge l [4])",
                  "seq": "(merge sq [4])", "set": "(merge st [4])"},
    "select-keys": {"vec": "(select-keys v [0])", "list": "(select-keys l [0])",
                    "seq": "(select-keys sq [0])", "set": "(select-keys st [1])"},
}


def main():
    out = [PRELUDE]
    neg_files = []
    for bname, cells in MATRIX.items():
        for kind in KINDS:
            if kind not in cells:
                continue
            cell = cells[kind]
            if cell.startswith("("):  # allowed: golden line
                out.append('(println (str "%s|%s " %s))' % (bname, kind, cell))
            else:  # forbidden: static error, pattern is an ERE
                call = NEG_CALLS[bname][kind]
                neg_files.append((bname, kind, call, cell))
    with open(os.path.join(ROOT, "test/collmatrix.lg"), "w") as f:
        f.write("\n".join(out) + "\n")
    for bname, kind, call, err in neg_files:
        name = "cm_%s_%s" % (bname.replace("?", "_p"), kind)
        with open(os.path.join(ROOT, "should_fail/%s.lg" % name), "w") as f:
            f.write(NEG_PRELUDE + ";; forbidden cell: %s x %s must be a static error\n" % (bname, kind)
                    + "(println (str %s))\n" % call)
        with open(os.path.join(ROOT, "should_fail/%s.err" % name), "w") as f:
            f.write(err)
    print("collmatrix.lg: %d allowed cells; %d should_fail files"
          % (sum(1 for c in MATRIX.values() for v in c.values() if v.startswith("(")),
             len(neg_files)))


if __name__ == "__main__":
    main()
