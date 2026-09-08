#!/usr/bin/env bash
# Copyright (c) 2026 Martin Rinard
# For every examples/opt/*.src, write examples/opt/dumps/<name>.txt with three views of the program:
#   [1/3] the three-address IR before optimization
#   [2/3] the IR after LCM + PDCE + cleanup (the program actually handed to codegen)
#   [3/3] the generated AArch64 assembly
# Regenerate with:  examples/dump.sh
set -u
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/prophecyc
[ -x "$BIN" ] || { echo "building prophecyc..."; lake build prophecyc >/dev/null 2>&1; }
mkdir -p examples/opt/dumps

for f in examples/opt/*.src; do
  base=$(basename "$f" .src)
  full=$("$BIN" --show-opt "$f" 2>/dev/null)
  before=$(printf '%s\n' "$full" | awk '/BEFORE OPTIMIZATION/{f=1;next} /AFTER LCM/{f=0} f')
  after=$( printf '%s\n' "$full" | awk '/AFTER CLEANUP/{f=1;next} f')
  asm=$("$BIN" "$f" 2>/dev/null)
  {
    echo "### $base"
    # strip `//` comment lines so the header does not leak into the one-line source echo
    echo "source: $(grep -v '^[[:space:]]*//' "$f")"
    echo
    echo "========== [1/3] IR — before optimization =========="
    printf '%s\n\n' "$before"
    echo "========== [2/3] IR — after optimization (LCM + PDCE + cleanup), fed to codegen =========="
    printf '%s\n\n' "$after"
    echo "========== [3/3] generated AArch64 assembly =========="
    printf '%s\n' "$asm"
  } > "examples/opt/dumps/$base.txt"
done
echo "wrote $(ls examples/opt/dumps/*.txt | wc -l | tr -d ' ') dumps to examples/opt/dumps/"
