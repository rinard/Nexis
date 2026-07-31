-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.BwdSlice` — a backward-may **program slice** analysis (the backward `image` atom).

`slice n` = the variables relevant on entry to `n`. Backward-may (least fixpoint): a variable `z` is
relevant if it is used to compute a variable relevant at the successor — the def→use relation run backward
through the `image` atom (`z ∈ slice(n)` when `∃ y ∈ slice(n'). flowsBack(n)(y,z)`), plus the criterion
the criterion `crit` (the program's observable/output variables) as the floor, minus the variable (re)defined at `n` in the
carry. Exercises the MTC `image` atom on the verified backward-may quadrant (`resMTCB_correct`) — the
backward counterpart of `taint`.

Defs are real read-offs of the IR: `defVars = definedVars` (the def at `n`, the carry's kill);
`flowsBack P n y z` = "at the assignment `d := e` occupying `n`, `y = d` and `z` is an operand of `e`" (so
relevance of `d` flows back to `e`'s operands); `crit` = the program's observable/output variables `P.obs`. Surface
`BwdSlice.gsl`; `_sub` in `BwdSliceDefsSub`.
-/
namespace BaseLanguage.Analyses.BwdSlice
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

-- `allVars` (universe) and `definedVars` (the carry's kill) come from `Tac.Locals` via `include Tac.Locals`.
/-- The backward def→use flow relation `y ↜ z`: at the assignment `d := e` occupying `n`, `y = d` and `z`
    is an operand of `e` — so relevance of the defined `y` flows back to each operand `z`. -/
def flowsBack (P : Program) (n : Node) (y z : Var) : Bool :=
  match Tac.Locals.definedVar P n with
  | some d => decide (y = d) && (Tac.Locals.usedVars P n).has z
  | none   => false
/-- The slicing criterion (floor): the observable/output variables `P.obs`, relevant by definition at
    every node (a constant set, not a per-node read). -/
def crit (P : Program) (_n : Node) : Vars := Vars.ofList P.obs

-- The `BwdSlice` clause predicate (the spelled-out `evs(sliceT, self') ⊆ self`) is **emitted** by
-- GenGeneral (`emitClauses`/`printEvs`) — not authored here.

end BaseLanguage.Analyses.BwdSlice
