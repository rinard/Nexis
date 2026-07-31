-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.Taint` — a forward-may def-use **taint** analysis.

`taint n` = the variables tainted on entry to `n`: the untrusted `source` variables read at the node, plus
the relational `image` of the incoming taint under the node's def→use `flowsTo` relation. A variable is
tainted iff it is (transitively) derived from an original input variable — the textbook use of the MTC
`image` atom on the verified forward-may quadrant (`resMTCMF_correct`).

Defs are real read-offs of the IR (`Tac.Locals`): `source` = the original (non-temporary) operands of
the node; `flowsTo P n y z` = "at the assignment `d := e` occupying `n`, operand `y` of `e` flows to the
defined variable `d`". Authored `Defs` (surface `Taint.gsl`; `_sub` in `TaintDefsSub`). The `update` field
is `evs(taintT) ⊆ taint'` (`source ∪ imageS`), so the `ValidExtremal` bridge is a definitional pass-through
(`flowFwd`, fwd·may).
-/
namespace BaseLanguage.Analyses.Taint
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

-- `allVars` (universe) comes from `Tac.Locals` via `include Tac.Locals`.
/-- Source taint (gen): the original (non-temporary) variables read at `n` — the untrusted inputs. -/
def source (P : Program) (n : Node) : Vars := (Tac.Locals.usedVars P n).filter (fun v => varIsOrig v)
/-- The node's def→use flow relation `y ↝ z`: at the assignment `d := e` occupying `n`, every operand `y`
    of the right-hand side `e` flows to the defined variable `d`. -/
def flowsTo (P : Program) (n : Node) (y z : Var) : Bool :=
  match Tac.Locals.definedVar P n, Tac.Locals.rhsExpr P n with
  | some d, some e => decide (z = d) && exprReadsVar e y
  | _,      _      => false

-- The `Taint` clause predicate is **emitted** by GenGeneral (`emitClauses`, evs-form) — not authored here.

end BaseLanguage.Analyses.Taint
