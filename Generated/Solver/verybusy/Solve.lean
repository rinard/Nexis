-- Copyright (c) 2026 Martin Rinard
-- GENERATED from VeryBusy.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.VeryBusy
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def busyT (P : Program) : MTC Expr :=
  .union (.const (fun (n, _) => genExprs P n)) (.inter .var (.const (fun (n, _) => transpExprs P n)))
def busyHi (P : Program) : Node → Exprs := fun n => (genExprs P n).union (transpExprs P n)
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Exprs := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Exprs := fun n => decodeExpr P (f n)

structure VeryBusyBitvec (P : Program) where
  busy : Node → BVExpr P

def solve (P : Program) : VeryBusyBitvec P :=
  let arr_busy := solveMTCBM P (listExpr P) (busyT P) (busyHi P) (∅)
  let f_busy : Node → BVExpr P := fun n => if n < P.size then gA (arr_busy) n else encode (listExpr P) (busyHi P n)
  { busy := f_busy }

theorem busyWf (P : Program) : MTC.Wf (listExpr P) (busyT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpExprs_sub P n x hx)⟩⟩
def busySol (P : Program) : Node → Exprs := decFExpr P (solve P).busy
theorem busy_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBM P (listExpr P) (busyT P) (busyHi P) (∅) (busySol P) ∧
    ∀ h, MTCSpecBM P (listExpr P) (busyT P) (busyHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ busySol P n :=
  resMTCBM_correct (hi := busyHi P) (sd := ∅) wf (listExpr_nodup P) (busyWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.VeryBusy
