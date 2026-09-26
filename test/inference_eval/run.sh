#!/usr/bin/env bash
# inference_eval: compile every snippet with the stdlib chunk state and report
# pass rate, failure classification, write amplification, and wall time.
#
# Usage:
#   test/inference_eval/run.sh [--write-baseline] [--out-dir DIR]
#
# Requires: dune build has been run (bin/lg_cli.exe + stdlib state exist),
# and OCAMLPATH includes _build/install/default/lib.
set -u
cd "$(dirname "$0")/../.."
ROOT=$PWD
LG="$ROOT/_build/default/bin/lg_cli.exe"
STATE="$ROOT/_build/default/stdlib/lg_stdlib_native.state"
SNIPPETS="$ROOT/test/inference_eval/snippets"
OUT_DIR="$ROOT/test/inference_eval"
MODE="run"
while [ $# -gt 0 ]; do
  case "$1" in
    --write-baseline) MODE="baseline"; shift ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done
export OCAMLPATH="$ROOT/_build/install/default/lib${OCAMLPATH:+:$OCAMLPATH}"

# The .lg-cache keys do not include the compiler version, so results from a
# stale binary would be replayed. Clear it for a true measurement.
rm -rf "$ROOT/.lg-cache"

[ -x "$LG" ] || { echo "missing $LG — run dune build first" >&2; exit 2; }
[ -f "$STATE" ] || { echo "missing $STATE — run dune build first" >&2; exit 2; }

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

total=0; pass=0
declare -a rows
for f in "$SNIPPETS"/*.cljc; do
  name=$(basename "$f" .cljc)
  total=$((total + 1))
  src_lines=$(wc -l < "$f")
  start=$(date +%s%N)
  out=$("$LG" --compile-files-chunk-from "$STATE" "$f" -o "$tmp/$name.ml" 2>&1)
  rc=$?
  end=$(date +%s%N)
  ms=$(( (end - start) / 1000000 ))
  if [ $rc -eq 0 ]; then
    ml_lines=$(wc -l < "$tmp/$name.ml")
    amp=$(awk "BEGIN{printf \"%.1f\", $ml_lines/$src_lines}")
    class="ok"
    pass=$((pass + 1))
  else
    ml_lines=0; amp="-"
    err=$(printf '%s' "$out" | grep -oE 'LG[0-9]{4}' | head -1)
    err=${err:-other}
    if printf '%s' "$out" | grep -qE 'param/g[0-9]|__lg_|TMeta'; then
      class="internal-name-leak:$err"
    elif printf '%s' "$out" | grep -q 'Runtime_dynamic'; then
      class="dynamic-fallback:$err"
    elif [ "$err" = "LG4000" ]; then
      class="ocaml-illtyped:$err"
    else
      class="reject:$err"
    fi
  fi
  printf '%-6s %-24s %6sms  src=%-4s ml=%-5s amp=%s\n' "$name" "$class" "$ms" "$src_lines" "$ml_lines" "$amp"
  rows+=("$name|$class|$ms|$src_lines|$ml_lines")
done

echo "---"
echo "pass: $pass/$total"

json="$OUT_DIR/results.json"
[ "$MODE" = baseline ] && json="$OUT_DIR/baseline.json"
{
  echo "{"
  echo "  \"total\": $total,"
  echo "  \"pass\": $pass,"
  echo "  \"snippets\": ["
  first=1
  for r in "${rows[@]}"; do
    IFS='|' read -r n c ms sl ml <<< "$r"
    [ $first -eq 0 ] && echo ","
    first=0
    printf '    {"name": "%s", "class": "%s", "ms": %s, "src_lines": %s, "ml_lines": %s}' \
      "$n" "$c" "$ms" "$sl" "$ml"
  done
  echo ""
  echo "  ]"
  echo "}"
} > "$json"
echo "wrote $json"
