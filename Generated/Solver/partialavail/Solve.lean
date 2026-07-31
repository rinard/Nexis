-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PartialAvail.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.PartialAvail
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def pavailT (P : Program) : MTC Expr :=
  .union (.const (fun (n, _) => genExprs P n)) (.inter .var (.const (fun (n, _) => transpExprs P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure PartialAvailBitvec (P : Program) where
  pavail : Node → BVExpr P

def solve (P : Program) : PartialAvailBitvec P :=
  let arr_pavail := solveMTCMF P (listExpr P) (pavailT P) (∅)
  let f_pavail : Node → BVExpr P := fun n => if n < P.size then gA (arr_pavail) n else 0
  { pavail := f_pavail }

theorem pavailWf (P : Program) : MTC.Wf (listExpr P) (pavailT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpExprs_sub P n x hx)⟩⟩
def pavailSol (P : Program) : Node → Exprs := decFExpr P (solve P).pavail
theorem pavail_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMF P (listExpr P) (pavailT P) (∅) (pavailSol P) ∧
    ∀ h, MTCSpecMF P (listExpr P) (pavailT P) (∅) h → ∀ n, ∀ x ∈ pavailSol P n, x ∈ h n :=
  resMTCMF_correct wf (listExpr_nodup P) (pavailWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.PartialAvail
