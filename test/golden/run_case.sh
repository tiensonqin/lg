#!/bin/sh
# Golden compiler test driver.
#
# usage:
#   run_case.sh compile <lg_cli> <stdlib.state> <case.cljc>
#   run_case.sh run     <lg_cli> <stdlib.state> <stdlib.ml> <case.cljc>
#
# Prints the captured output that becomes the case's .actual file:
# rendered diagnostics (stderr) plus an `exit: N` trailer. Run mode appends the
# program's stdout before the trailer.
set -u

mode=$1
cli=$2
state=$3

# Local run artifacts need the runtime's C stubs (dlllg_time) and the
# in-tree findlib packages; derive the build root from the state path.
build_root=$(cd "$(dirname "$state")/.." && pwd)
CAML_LD_LIBRARY_PATH="$build_root/runtime${CAML_LD_LIBRARY_PATH:+:$CAML_LD_LIBRARY_PATH}"
OCAMLPATH="$build_root/../install/default/lib${OCAMLPATH:+:$OCAMLPATH}"
export CAML_LD_LIBRARY_PATH OCAMLPATH

tmp=$(mktemp -d "${TMPDIR:-/tmp}/lg-golden.XXXXXX") || exit 2
trap 'rm -rf "$tmp"' EXIT HUP INT TERM

# Diagnostics echo the path as passed; keep it stable whether dune expands the
# dep as ./case.cljc or case.cljc.
normalize() { printf '%s' "${1#./}"; }

case "$mode" in
compile)
  case_file=$(normalize "$4")
  name=${case_file##*/}
  name=${name%.cljc}
  "$cli" --target native --compile-chunk-from "$state" "$case_file" \
    -o "$tmp/$name.ml" >"$tmp/out" 2>"$tmp/err"
  status=$?
  cat "$tmp/out" "$tmp/err"
  printf 'exit: %d\n' "$status"
  ;;
run)
  stdlib_ml=$4
  case_file=$(normalize "$5")
  "$cli" --target native --run-files-from "$state" "$stdlib_ml" "$case_file" \
    >"$tmp/out" 2>"$tmp/err"
  status=$?
  cat "$tmp/out" "$tmp/err"
  printf 'exit: %d\n' "$status"
  ;;
*)
  echo "run_case.sh: unknown mode $mode" >&2
  exit 2
  ;;
esac
