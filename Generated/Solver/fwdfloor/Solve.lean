-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdFloor.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.FwdFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def ffT (P : Program) : MTC Expr :=
  .var
def ffLo (P : Program) : Node → Exprs := fun n => genExprs P n
def ffHi (P : Program) : Node → Exprs := fun n => allExprs P
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure FwdFloorBitvec (P : Program) where
  ff : Node → BVExpr P

def solve (P : Program) : FwdFloorBitvec P :=
  let arr_ff := solveFmC P (listExpr P) (ffT P) (ffLo P) (ffHi P) (∅)
  let f_ff : Node → BVExpr P := fun n => if n < P.size then gA (arr_ff) n else encode (listExpr P) ((ffLo P) n)
  { ff := f_ff }

theorem ffWf (P : Program) : MTC.Wf (listExpr P) (ffT P) :=
  by trivial
def ffSol (P : Program) : Node → Exprs := decFExpr P (solve P).ff
theorem ff_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMFC P (listExpr P) (ffT P) (ffLo P) (ffHi P) (∅) (ffSol P) ∧
    ∀ h, MTCSpecMFC P (listExpr P) (ffT P) (ffLo P) (ffHi P) (∅) h → ∀ n, ∀ x ∈ ffSol P n, x ∈ h n :=
  resFmC_correct (lo := ffLo P) (hi := ffHi P) (sd := ∅) wf (listExpr_nodup P) (ffWf P) (fun n x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx)) (fun x hx => absurd hx Std.HashSet.not_mem_empty) (fun n x hx => Std.HashSet.mem_toList.mpr hx) (fun n x hx => genExprs_sub P n x hx)

end BaseLanguage.Analyses.FwdFloor
