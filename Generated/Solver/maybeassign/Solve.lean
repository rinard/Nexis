-- Copyright (c) 2026 Martin Rinard
-- GENERATED from MaybeAssign.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.MaybeAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allGenVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allGenVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def maT (P : Program) : MTC Var :=
  .union (.const (fun (n, _) => genVars P n)) (.inter .var (.const (fun (n, _) => transpGenVars P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure MaybeAssignBitvec (P : Program) where
  ma : Node → BVVar P

def solve (P : Program) : MaybeAssignBitvec P :=
  let arr_ma := solveMTCMF P (listVar P) (maT P) (∅)
  let f_ma : Node → BVVar P := fun n => if n < P.size then gA (arr_ma) n else 0
  { ma := f_ma }

theorem maWf (P : Program) : MTC.Wf (listVar P) (maT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genVars_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpGenVars_sub P n x hx)⟩⟩
def maSol (P : Program) : Node → Vars := decFVar P (solve P).ma
theorem ma_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMF P (listVar P) (maT P) (∅) (maSol P) ∧
    ∀ h, MTCSpecMF P (listVar P) (maT P) (∅) h → ∀ n, ∀ x ∈ maSol P n, x ∈ h n :=
  resMTCMF_correct wf (listVar_nodup P) (maWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.MaybeAssign
