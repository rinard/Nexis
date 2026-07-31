#!/usr/bin/env bash
# Copyright (c) 2026 Martin Rinard
# Compile every examples/opt/*.src with prophecyc, count real arithmetic ops in the emitted asm
# (a proxy for what LCM/PDCE removed), assemble + link + run, and print a table.
#   Usage:  examples/run.sh              # from the repo root
#           examples/run.sh --show-opt   # also dump the before/after IR for each program
set -u
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/prophecyc
[ -x "$BIN" ] || { echo "building prophecyc..."; lake build prophecyc >/dev/null 2>&1; }
OUT=$(mktemp -d)
show_opt=0; [ "${1:-}" = "--show-opt" ] && show_opt=1

ops () { grep -cE "^  $1 x9," "$2" 2>/dev/null; }

printf '%-28s %-4s %-4s %-4s %-4s  %s\n' TEST add sub mul cmp RESULT
printf '%.0s-' {1..78}; echo
for f in examples/opt/*.src; do
  base=$(basename "$f" .src)
  if ! "$BIN" "$f" > "$OUT/$base.s" 2>/dev/null; then
    printf '%-28s %s\n' "$base" "PARSE ERROR"; continue
  fi
  add=$(ops add "$OUT/$base.s"); sub=$(ops sub "$OUT/$base.s")
  mul=$(ops mul "$OUT/$base.s"); cmp=$(grep -cE '^  cmp ' "$OUT/$base.s")
  if clang -o "$OUT/$base" "$OUT/$base.s" 2>/dev/null; then
    res=$("$OUT/$base" | tr '\n' ' ')
  else
    res="ASM-FAIL"
  fi
  printf '%-28s %-4s %-4s %-4s %-4s  %s\n' "$base" "$add" "$sub" "$mul" "$cmp" "$res"
  if [ "$show_opt" = 1 ]; then "$BIN" --show-opt "$f" 2>/dev/null | sed 's/^/    /'; echo; fi
done
rm -rf "$OUT"
