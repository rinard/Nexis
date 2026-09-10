-- Copyright (c) 2026 Martin Rinard
import Solver.Spec
import Solver.Quadrant
import Solver.Closure

/-!
# `Solver` — the public face of the solution mechanism

Importing this module gives you exactly two things:

* `Solver.Spec`      — the MTC **vocabulary**: the term language, its set-level semantics `MTC.evs`,
                       `MTC.Wf`, and the four quadrant validity predicates `MTCSpec{,MF,BM,B}`.
                       This is *what a valid solution is*. No engine, no bitvectors.
* `Solver.Quadrant`  — a **mechanism**: one solution per quadrant (`resMTC{,MF,BM,B}`) plus its
                       valid + extremal contract (`resMTC*_correct`). Implements any MTC-term analysis's
                       interface outright — but it is NOT the substitution boundary; `Seam/` is.

It deliberately does **not** re-export `Solver.Impl.*` (the bitvector worklist fixpoint). Only
`Solver/Quadrant.lean` imports the implementation; `script/check-solver-seam.sh` enforces it.

The interface every analysis actually exports is in `Seam/<a>/ValidExtremal.lean`: a solution, its
validity against a set-level clause predicate, and its extremality. `Seam/<a>/Adapter.lean` packages
those into the transforms' bundles (`LcmSpec` + `Extremal`, `PdceSpec`, `ReachSpec`, `CPSpec`), and
`BaseLanguage/` is universally quantified over them.

To swap the solution mechanism wholesale: replace `Solver/Impl/` and re-provide the 8 symbols named in
`Solver/Quadrant.lean`. Because the generator emits every MTC-term analysis against exactly those,
**new analysis specs require no new stubs** — the stub count is O(1), not O(analyses).
-/
