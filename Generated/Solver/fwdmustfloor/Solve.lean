-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMustFloor.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.FwdMustFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def fmfT (P : Program) : MTC Expr :=
  .var
def fmfLo (P : Program) : Node → Exprs := fun n => genExprs P n
def fmfHi (P : Program) : Node → Exprs := fun n => allExprs P
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure FwdMustFloorBitvec (P : Program) where
  fmf : Node → BVExpr P

def solve (P : Program) : FwdMustFloorBitvec P :=
  let arr_fmf := solveFMC P (listExpr P) (fmfT P) (fmfLo P) (fmfHi P) (∅)
  let f_fmf : Node → BVExpr P := fun n => if n < P.size then gA (arr_fmf) n else encode (listExpr P) ((fmfHi P) n)
  { fmf := f_fmf }

theorem fmfWf (P : Program) : MTC.Wf (listExpr P) (fmfT P) :=
  by trivial
def fmfSol (P : Program) : Node → Exprs := decFExpr P (solve P).fmf
theorem fmf_correct (P : Program) (wf : WellFormed P) :
    MTCSpecC P (listExpr P) (fmfT P) (fmfLo P) (fmfHi P) (∅) (fmfSol P) ∧
    ∀ h, MTCSpecC P (listExpr P) (fmfT P) (fmfLo P) (fmfHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ fmfSol P n :=
  resFMC_correct (lo := fmfLo P) (hi := fmfHi P) (sd := ∅) wf (listExpr_nodup P) (fmfWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr hx) (fun n x hx => genExprs_sub P n x hx)

end BaseLanguage.Analyses.FwdMustFloor
