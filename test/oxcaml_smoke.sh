#!/usr/bin/env bash
# OxCaml end-to-end smoke: emit --backend=oxcaml, compile with the real
# OxCaml (flambda2) toolchain inside the `oxcaml` opam switch, run each
# binary and diff against the golden .out.
#
# Requires:
#   - an `oxcaml` opam switch (OCaml 5.4.0+ox):
#       opam switch create oxcaml ocaml-variants.5.4.0+ox \
#         --repos oxcaml=https://github.com/oxcaml/opam-repository.git,default
#   - dune, ocamlfind, and the native deps built under it. clj-core +
#     rrbvec need their `ox` branches (@ local borrow annotations +
#     Seq.*_local variants, melange stanzas stripped):
#       opam pin add -y rrbvec 'git+https://github.com/logseq/rrbvec.git#ox'
#       opam pin add -y clj-core 'git+https://github.com/logseq/clj-core.git#ox'
#
# Run from the repo root: ./test/oxcaml_smoke.sh

set -e
cd "$(dirname "$0")/.."
eval "$(opam env --switch=oxcaml --set-switch)"

LG=./_build/default/bin/lg.exe
fail=0
for f in test/*.lg; do
  n=$(basename "$f" .lg)
  case "$n" in _*|mel*|wasm|ffi*|ffimod) continue;; esac
  extra=""
  case "$n" in props|qclib|testlib) extra="-I lib";; esac
  if ! "$LG" build "$f" -I lib --backend=oxcaml -o "/tmp/ox_$n" 2>/dev/null; then
    echo "BUILD-FAIL $n"; fail=1; continue
  fi
  if [ -f "test/$n.out" ]; then
    if ! diff -q <("/tmp/ox_$n" 2>/dev/null) "test/$n.out" >/dev/null; then
      echo "DIFF-FAIL $n"; fail=1; continue
    fi
  fi
  echo "ok $n"
done
exit $fail
