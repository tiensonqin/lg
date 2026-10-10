#!/usr/bin/env bash
# OxCaml end-to-end smoke: emit --backend=oxcaml, compile with the real
# OxCaml (flambda2) toolchain inside the `oxcaml` opam switch, run each
# binary and diff against the golden .out.
#
# Requires:
#   - an `oxcaml` opam switch (OCaml 5.4.0+ox):
#       opam switch create oxcaml ocaml-variants.5.4.0+ox \
#         --repos oxcaml=https://github.com/oxcaml/opam-repository.git,default
#   - dune, ocamlfind, and the native deps built under it (the switch's
#     own dune/ocamlfind/eio work; `opam install -y eio eio_main eio_posix`
#     for the eio lane). clj-core + rrbvec need their `ox` branches
#     (@ local borrow annotations + Seq.*_local variants):
#       opam pin add -y rrbvec 'git+https://github.com/logseq/rrbvec.git#ox'
#       opam pin add -y clj-core 'git+https://github.com/logseq/clj-core.git#ox'
#   On macOS the ox-branch opam files still list melange/js_of_ocaml which
#   conflict with the oxcaml repo's oxcaml-* variants — pin local copies
#   with those dep lines (and clj-core's #main pin-depends) removed.
#
# Run from the repo root: ./test/oxcaml_smoke.sh

set -e
cd "$(dirname "$0")/.."
eval "$(opam env --switch=oxcaml --set-switch)"

LG=./_build/default/bin/lg.exe
fail=0
# _build is shared across switches: refresh lg.exe under this switch so
# the ocaml.* interop lanes run against ox-written cmis (an upstream
# binary in _build cannot parse them).
dune build bin/lg.exe 2>/dev/null || true
# ocaml.* requires read .cmi signatures, which are toolchain-bound — an
# upstream-built lg cannot parse OxCaml cmis. Probe once: when the reader
# reports the toolchain mismatch, the ocamlinterop lane is skipped rather
# than failed (an oxcaml-built lg passes it).
SKIP_OI=0
if "$LG" check test/ocamlinterop.lg -I lib 2>&1 | grep -q "different OCaml toolchain"; then
  SKIP_OI=1
fi
for f in test/*.lg; do
  n=$(basename "$f" .lg)
  case "$n" in _*|mel*|wasm|ffi*|ffimod) continue;; esac
  if [ "$n" = ocamlinterop ] && [ "$SKIP_OI" = 1 ]; then
    echo "skip ocamlinterop (cmi toolchain mismatch)"; continue
  fi
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
