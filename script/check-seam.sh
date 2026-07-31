#!/usr/bin/env bash
# Copyright (c) 2026 Martin Rinard
# Seam invariant: NOTHING outside the Seam interface may import the Solver/ directory.
#
# The compiler (BaseLanguage/, analyses/, Main, test/) is universally quantified over an arbitrary
# valid + extremal solution to the ghost-variable specs. Only Seam/ binds those specs to a concrete
# solver, so Solver/ can be replaced wholesale without touching anything above the seam.
#
# Exempt: Seam/ + Seam.lean (the interface); Solver/ + Solver.lean (the solver library itself);
# Generated/Solver/<name>/Solve.lean (the generated per-analysis solver instantiations, below the seam);
# docs/, scratch/ (not built).
set -uo pipefail
cd "$(dirname "$0")/.."
violators=$(grep -rln --include='*.lean' -E '^import Solver(\.|$)' . 2>/dev/null \
  | grep -vE '^\./(Seam|Solver)/|^\./(Seam|Solver)\.lean$|^\./Generated/Solver/|^\./(docs|scratch)/|/\.lake/' | sort)
if [ -n "$violators" ]; then
  echo "SEAM VIOLATION — these import Solver/ but live outside the Seam interface:"
  echo "$violators" | sed 's/^/  /'
  exit 1
fi
echo "seam ok: only Seam/ imports Solver/"
