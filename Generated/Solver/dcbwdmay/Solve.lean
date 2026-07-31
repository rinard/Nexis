-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcbwdmay.DcBwdMayDefs
import analyses.dcbwdmay.DcBwdMayDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DcBwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def dyT (P : Program) : MTC Expr :=
  .var
def dyLo (P : Program) : Node → Exprs := fun n => dcbmayLo P n
def dyHi (P : Program) : Node → Exprs := fun n => dcbmayHi P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure DcBwdMayBitvec (P : Program) where
  dy : Node → BVExpr P

def solve (P : Program) : DcBwdMayBitvec P :=
  let arr_dy := solveBmC P (listExpr P) (dyT P) (dyLo P) (dyHi P) (∅)
  let f_dy : Node → BVExpr P := fun n => if n < P.size then gA (arr_dy) n else encode (listExpr P) ((dyLo P) n)
  { dy := f_dy }

theorem dyWf (P : Program) : MTC.Wf (listExpr P) (dyT P) :=
  by trivial
def dySol (P : Program) : Node → Exprs := decFExpr P (solve P).dy
theorem dy_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBC P (listExpr P) (dyT P) (dyLo P) (dyHi P) (∅) (dySol P) ∧
    ∀ h, MTCSpecBC P (listExpr P) (dyT P) (dyLo P) (dyHi P) (∅) h → ∀ n, ∀ x ∈ dySol P n, x ∈ h n :=
  resBmC_correct (lo := dyLo P) (hi := dyHi P) (sd := ∅) wf (listExpr_nodup P) (dyWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (dcbmayLo_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (dcbmayHi_sub P n x hx)) (dcbmayLo_sub_dcbmayHi P)

end BaseLanguage.Analyses.DcBwdMay
