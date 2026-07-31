-- Copyright (c) 2026 Martin Rinard
-- GENERATED from ConstProp.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.ConstProp
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listCPair (P : Program) : List CPair := (allConst P).toList
theorem listCPair_nodup (P : Program) : (listCPair P).Nodup := (allConst P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def cpT (P : Program) : MTC CPair :=
  .union (.const (fun (n, _) => genConst P n)) (.inter .var (.const (fun (n, _) => transpConst P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthCPair (P : Program) : Nat := (listCPair P).length
abbrev BVCPair (P : Program) := BitVec (widthCPair P)
def decodeCPair (P : Program) (bv : BVCPair P) : ConstPairs := decode (listCPair P) bv
@[noinline] def decFCPair (P : Program) (f : Node → BVCPair P) : Node → ConstPairs := fun n => decodeCPair P (f n)

structure ConstPropBitvec (P : Program) where
  cp : Node → BVCPair P

def solve (P : Program) : ConstPropBitvec P :=
  let arr_cp := solveMTC P (listCPair P) (cpT P) (∅)
  let f_cp : Node → BVCPair P := fun n => (arr_cp)[n]?.getD (topV (widthCPair P))
  { cp := f_cp }

theorem cpWf (P : Program) : MTC.Wf (listCPair P) (cpT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genConst_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpConst_sub P n x hx)⟩⟩
def cpSol (P : Program) : Node → ConstPairs := decFCPair P (solve P).cp
theorem cp_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listCPair P) (cpT P) (∅) (cpSol P) ∧
    ∀ h, MTCSpec P (listCPair P) (cpT P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ cpSol P n :=
  resMTC_correct wf (listCPair_nodup P) (cpWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.ConstProp
