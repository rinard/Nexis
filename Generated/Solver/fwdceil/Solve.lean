-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdCeil.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.FwdCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def fcT (P : Program) : MTC Expr :=
  .var
def fcLo (P : Program) : Node → Exprs := fun n => ∅
def fcHi (P : Program) : Node → Exprs := fun n => genExprs P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure FwdCeilBitvec (P : Program) where
  fc : Node → BVExpr P

def solve (P : Program) : FwdCeilBitvec P :=
  let arr_fc := solveFMC P (listExpr P) (fcT P) (fcLo P) (fcHi P) (∅)
  let f_fc : Node → BVExpr P := fun n => if n < P.size then gA (arr_fc) n else encode (listExpr P) ((fcHi P) n)
  { fc := f_fc }

theorem fcWf (P : Program) : MTC.Wf (listExpr P) (fcT P) :=
  by trivial
def fcSol (P : Program) : Node → Exprs := decFExpr P (solve P).fc
theorem fc_correct (P : Program) (wf : WellFormed P) :
    MTCSpecC P (listExpr P) (fcT P) (fcLo P) (fcHi P) (∅) (fcSol P) ∧
    ∀ h, MTCSpecC P (listExpr P) (fcT P) (fcLo P) (fcHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ fcSol P n :=
  resFMC_correct (lo := fcLo P) (hi := fcHi P) (sd := ∅) wf (listExpr_nodup P) (fcWf P) (fun n x hx => absurd hx Std.HashSet.not_mem_empty) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx)) (fun n x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.FwdCeil
