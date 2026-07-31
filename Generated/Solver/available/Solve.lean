-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Available.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.Available
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def availT (P : Program) : MTC Expr :=
  .union (.const (fun (n, _) => genExprs P n)) (.inter .var (.const (fun (n, _) => transpExprs P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure AvailableBitvec (P : Program) where
  avail : Node → BVExpr P

def solve (P : Program) : AvailableBitvec P :=
  let arr_avail := solveMTC P (listExpr P) (availT P) (∅)
  let f_avail : Node → BVExpr P := fun n => (arr_avail)[n]?.getD (topV (widthExpr P))
  { avail := f_avail }

theorem availWf (P : Program) : MTC.Wf (listExpr P) (availT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpExprs_sub P n x hx)⟩⟩
def availSol (P : Program) : Node → Exprs := decFExpr P (solve P).avail
theorem avail_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listExpr P) (availT P) (∅) (availSol P) ∧
    ∀ h, MTCSpec P (listExpr P) (availT P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ availSol P n :=
  resMTC_correct wf (listExpr_nodup P) (availWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.Available
