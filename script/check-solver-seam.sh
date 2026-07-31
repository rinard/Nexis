#!/usr/bin/env bash
# Copyright (c) 2026 Martin Rinard
# Solver-internal invariant: only Solver/Quadrant.lean (and the two bundles) may import Solver/Impl/.
#
# NOTE: this is NOT the substitution boundary — `Seam/` is, and `check-seam.sh` guards it. Every analysis
# exports its interface (solution + validity + extremality, set-level) from Seam/<a>/ValidExtremal.lean.
#
# Solver/Spec.lean      — vocabulary: MTC, evs, Wf, MTCSpec{,MF,BM,B}. What a valid solution IS.
# Solver/Quadrant.lean — a MECHANISM: resMTC{,MF,BM,B} + resMTC*_correct (valid ∧ extremal).
#                        Implements any MTC-term analysis's interface. NOT the boundary — Seam/ is.
# Solver/Impl/*         — one way to compute one (bitvector worklist fixpoint). Replaceable.
#
# Every analysis — present or future — lands in one of the four quadrants and is emitted against the
# seam alone, so a replacement solver needs no per-analysis work.
#
# Allowed to import Solver.Impl.*:
#   - Solver/Quadrant.lean           the quadrant mechanism
#   - Solver/Impl/*                  internal
#   - Generated/Solver/<name>/Solve.lean   the generated per-analysis bundle: an IMPLEMENTATION of that
#                                    analysis's own interface (Generated/Seam/<name>) — below that seam,
#                                    not through it. Not a leak; routing it through the quadrants costs
#                                    >=240x (see Quadrant.lean).
#   - docs/, scratch/                prose / scratch, not the compiler
set -uo pipefail
cd "$(dirname "$0")/.."
violators=$(grep -rln --include='*.lean' -E '^import Solver\.Impl\.' . 2>/dev/null \
  | grep -vE '^\./Solver/Quadrant\.lean$|^\./Solver/Impl/|^\./Generated/Solver/[^/]+/Solve\.lean$|^\./(docs|scratch)/|/\.lake/' \
  | sort)
if [ -n "$violators" ]; then
  echo "SOLVER SEAM VIOLATION — these reach into Solver/Impl/ but are not the interface:"
  echo "$violators" | sed 's/^/  /'
  exit 1
fi
echo "solver seam ok: only Solver/Quadrant.lean (+ the generated per-analysis bundles) imports Solver/Impl/"
