-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcfwdmay.DcFwdMayDefs
import analyses.dcfwdmay.DcFwdMayDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DcFwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def dmT (P : Program) : MTC Expr :=
  .var
def dmLo (P : Program) : Node → Exprs := fun n => dcfmayLo P n
def dmHi (P : Program) : Node → Exprs := fun n => dcfmayHi P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure DcFwdMayBitvec (P : Program) where
  dm : Node → BVExpr P

def solve (P : Program) : DcFwdMayBitvec P :=
  let arr_dm := solveFmC P (listExpr P) (dmT P) (dmLo P) (dmHi P) (∅)
  let f_dm : Node → BVExpr P := fun n => if n < P.size then gA (arr_dm) n else encode (listExpr P) ((dmLo P) n)
  { dm := f_dm }

theorem dmWf (P : Program) : MTC.Wf (listExpr P) (dmT P) :=
  by trivial
def dmSol (P : Program) : Node → Exprs := decFExpr P (solve P).dm
theorem dm_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMFC P (listExpr P) (dmT P) (dmLo P) (dmHi P) (∅) (dmSol P) ∧
    ∀ h, MTCSpecMFC P (listExpr P) (dmT P) (dmLo P) (dmHi P) (∅) h → ∀ n, ∀ x ∈ dmSol P n, x ∈ h n :=
  resFmC_correct (lo := dmLo P) (hi := dmHi P) (sd := ∅) wf (listExpr_nodup P) (dmWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (dcfmayLo_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (dcfmayHi_sub P n x hx)) (dcfmayLo_sub_dcfmayHi P)

end BaseLanguage.Analyses.DcFwdMay
