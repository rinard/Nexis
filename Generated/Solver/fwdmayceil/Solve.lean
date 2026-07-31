-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMayCeil.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.FwdMayCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def fmcT (P : Program) : MTC Expr :=
  .var
def fmcLo (P : Program) : Node → Exprs := fun n => ∅
def fmcHi (P : Program) : Node → Exprs := fun n => genExprs P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure FwdMayCeilBitvec (P : Program) where
  fmc : Node → BVExpr P

def solve (P : Program) : FwdMayCeilBitvec P :=
  let arr_fmc := solveFmC P (listExpr P) (fmcT P) (fmcLo P) (fmcHi P) (∅)
  let f_fmc : Node → BVExpr P := fun n => if n < P.size then gA (arr_fmc) n else encode (listExpr P) ((fmcLo P) n)
  { fmc := f_fmc }

theorem fmcWf (P : Program) : MTC.Wf (listExpr P) (fmcT P) :=
  by trivial
def fmcSol (P : Program) : Node → Exprs := decFExpr P (solve P).fmc
theorem fmc_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMFC P (listExpr P) (fmcT P) (fmcLo P) (fmcHi P) (∅) (fmcSol P) ∧
    ∀ h, MTCSpecMFC P (listExpr P) (fmcT P) (fmcLo P) (fmcHi P) (∅) h → ∀ n, ∀ x ∈ fmcSol P n, x ∈ h n :=
  resFmC_correct (lo := fmcLo P) (hi := fmcHi P) (sd := ∅) wf (listExpr_nodup P) (fmcWf P) (fun n x hx => absurd hx Std.HashSet.not_mem_empty) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx)) (fun n x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.FwdMayCeil
