-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DefiniteAssign.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DefiniteAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allGenVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allGenVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def daT (P : Program) : MTC Var :=
  .union (.const (fun (n, _) => genVars P n)) (.inter .var (.const (fun (n, _) => transpGenVars P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure DefiniteAssignBitvec (P : Program) where
  da : Node → BVVar P

def solve (P : Program) : DefiniteAssignBitvec P :=
  let arr_da := solveMTC P (listVar P) (daT P) (∅)
  let f_da : Node → BVVar P := fun n => (arr_da)[n]?.getD (topV (widthVar P))
  { da := f_da }

theorem daWf (P : Program) : MTC.Wf (listVar P) (daT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genVars_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpGenVars_sub P n x hx)⟩⟩
def daSol (P : Program) : Node → Vars := decFVar P (solve P).da
theorem da_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listVar P) (daT P) (∅) (daSol P) ∧
    ∀ h, MTCSpec P (listVar P) (daT P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ daSol P n :=
  resMTC_correct wf (listVar_nodup P) (daWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.DefiniteAssign
