-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.StructAvail` — a forward-must **data-dependency availability** analysis.

`avail n` = the definition-nodes whose computed value is available on entry to `n`. A node `z` is available
once **every** node defining one of `z`'s operand variables is available (the `gather` precondition
`structSub(z) ⊆ avail(n)`), plus each node contributes its own definition (`localGen = genDefs`). So a
computation becomes available exactly when all its data-dependencies are — the textbook use of the MTC
`gather` atom on the verified forward-must quadrant (`resMTC_correct`).

Defs are real read-offs of the IR: `localGen n = genDefs n` when `n` is a leaf (`structSub n n` empty),
else `∅` (a computation with data-dependencies is available only via the gather); `structSub P _ z`
= the nodes whose defined variable is an operand of `z` (`z`'s data-dependency set). Authored `Defs`
(surface `StructAvail.gsl`; `_sub` in `StructAvailDefsSub`). The gather's `structSub` needs no `_sub` (its
result is bounded by the universe); only `localGen` carries a `Wf` obligation, discharged by `genDefs_sub`.
-/
namespace BaseLanguage.Analyses.StructAvail
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

-- `allDefs` (universe) comes from `Tac.Locals` via `include Tac.Locals`.
/-- The data-dependency set of `z` (the gather's per-element precondition): every node whose defined
    variable is an operand of the computation at `z`. Empty ⇒ `z` is a **leaf** (its operands are all
    external inputs / immediates — nothing to wait on). -/
def structSub (P : Program) (_n : Node) (z : Node) : Defs := Tac.Locals.dataDeps P z
/-- Locally-generated availability (gen): the definition made at `n`, but **only if `n` is a leaf**
    (`structSub n` empty) — a computation with data-dependencies is available only once they are (via the
    gather), never unconditionally. This is what makes the `gather` load-bearing rather than dominated by
    an unconditional per-node gen. -/
def localGen (P : Program) (n : Node) : Defs :=
  if (structSub P n n).isEmpty then Tac.Locals.genDefs P n else Defs.empty

-- The `StructAvail` clause predicate is **emitted** by GenGeneral (`emitClauses`, evs-form) — not authored here.

end BaseLanguage.Analyses.StructAvail
