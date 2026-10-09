#!/usr/bin/env bash
# Build a release tarball: lg-<ver>-<os>-<arch>.tar.gz with the binary + lib/.
set -euo pipefail
cd "$(dirname "$0")/.."

VER="${1:-0.1.0}"
OS="$(uname -s | tr 'A-Z' 'a-z')"
ARCH="$(uname -m)"

eval "$(opam env --switch=5.5.0 --set-switch 2>/dev/null || opam env)"
dune build bin/lg.exe

DIST="dist/lg-${VER}-${OS}-${ARCH}"
rm -rf "$DIST"
mkdir -p "$DIST"
cp _build/default/bin/lg.exe "$DIST/lg"
cp -r lib "$DIST/lib"
cat > "$DIST/README.txt" <<EOF
lg $VER — Clojure-flavored OCaml
Usage: lg check|build|fmt|repl|doc file.lg   lg init <name>   lg lsp
EOF
mkdir -p dist
tar -czf "dist/lg-${VER}-${OS}-${ARCH}.tar.gz" -C dist "$(basename "$DIST")"
echo "wrote dist/lg-${VER}-${OS}-${ARCH}.tar.gz"
