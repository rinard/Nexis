-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMust.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcfwdmust.DcFwdMustDefs
import analyses.dcfwdmust.DcFwdMustDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DcFwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def dfT (P : Program) : MTC Expr :=
  .var
def dfLo (P : Program) : Node → Exprs := fun n => dcfmLo P n
def dfHi (P : Program) : Node → Exprs := fun n => dcfmHi P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure DcFwdMustBitvec (P : Program) where
  df : Node → BVExpr P

def solve (P : Program) : DcFwdMustBitvec P :=
  let arr_df := solveFMC P (listExpr P) (dfT P) (dfLo P) (dfHi P) (∅)
  let f_df : Node → BVExpr P := fun n => if n < P.size then gA (arr_df) n else encode (listExpr P) ((dfHi P) n)
  { df := f_df }

theorem dfWf (P : Program) : MTC.Wf (listExpr P) (dfT P) :=
  by trivial
def dfSol (P : Program) : Node → Exprs := decFExpr P (solve P).df
theorem df_correct (P : Program) (wf : WellFormed P) :
    MTCSpecC P (listExpr P) (dfT P) (dfLo P) (dfHi P) (∅) (dfSol P) ∧
    ∀ h, MTCSpecC P (listExpr P) (dfT P) (dfLo P) (dfHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ dfSol P n :=
  resFMC_correct (lo := dfLo P) (hi := dfHi P) (sd := ∅) wf (listExpr_nodup P) (dfWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (dcfmLo_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (dcfmHi_sub P n x hx)) (dcfmLo_sub_dcfmHi P)

end BaseLanguage.Analyses.DcFwdMust
