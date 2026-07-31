-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DemoGate.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.DemoGate
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def dgT (P : Program) : MTC Var :=
  .union (.gate (fun (n, _) => definedVars P n) (fun (n, _) => rhsVars P n)) (.union (.const (fun (n, _) => definedVars P n)) (.inter .var (.const (fun (n, _) => condVars P n))))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure DemoGateBitvec (P : Program) where
  dg : Node → BVVar P

def solve (P : Program) : DemoGateBitvec P :=
  let arr_dg := solveMTCB P (listVar P) (dgT P) (condVars P) (∅)
  let f_dg : Node → BVVar P := fun n => if n < P.size then gA (arr_dg) n else encode (listVar P) ((condVars P) n)
  { dg := f_dg }

theorem dgWf (P : Program) : MTC.Wf (listVar P) (dgT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (definedVars_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (rhsVars_sub P n x hx)⟩, ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (definedVars_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (condVars_sub P n x hx)⟩⟩⟩
def dgSol (P : Program) : Node → Vars := decFVar P (solve P).dg
theorem dg_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listVar P) (dgT P) (condVars P) (∅) (dgSol P) ∧
    ∀ h, MTCSpecB P (listVar P) (dgT P) (condVars P) (∅) h → ∀ n, ∀ x ∈ dgSol P n, x ∈ h n :=
  resMTCB_correct (lo := condVars P) (sd := ∅) wf (listVar_nodup P) (dgWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (condVars_sub P n x hx))
    (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.DemoGate
