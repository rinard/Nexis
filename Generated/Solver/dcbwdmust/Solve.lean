-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMust.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcbwdmust.DcBwdMustDefs
import analyses.dcbwdmust.DcBwdMustDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DcBwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def dbT (P : Program) : MTC Expr :=
  .var
def dbLo (P : Program) : Node → Exprs := fun n => dcbmLo P n
def dbHi (P : Program) : Node → Exprs := fun n => dcbmHi P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure DcBwdMustBitvec (P : Program) where
  db : Node → BVExpr P

def solve (P : Program) : DcBwdMustBitvec P :=
  let arr_db := solveBMC P (listExpr P) (dbT P) (dbLo P) (dbHi P) (∅)
  let f_db : Node → BVExpr P := fun n => if n < P.size then gA (arr_db) n else encode (listExpr P) ((dbHi P) n)
  { db := f_db }

theorem dbWf (P : Program) : MTC.Wf (listExpr P) (dbT P) :=
  by trivial
def dbSol (P : Program) : Node → Exprs := decFExpr P (solve P).db
theorem db_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBMC P (listExpr P) (dbT P) (dbLo P) (dbHi P) (∅) (dbSol P) ∧
    ∀ h, MTCSpecBMC P (listExpr P) (dbT P) (dbLo P) (dbHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ dbSol P n :=
  resBMC_correct (lo := dbLo P) (hi := dbHi P) (sd := ∅) wf (listExpr_nodup P) (dbWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (dcbmLo_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr (dcbmHi_sub P n x hx)) (dcbmLo_sub_dcbmHi P)

end BaseLanguage.Analyses.DcBwdMust
