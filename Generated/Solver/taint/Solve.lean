-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Taint.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.taint.TaintDefs
import analyses.taint.TaintDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.Taint
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def taintT (P : Program) : MTC Var :=
  .union (.union .var (.const (fun (n, _) => source P n))) (.image (allVars P) (fun (n, _) => flowsTo P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure TaintBitvec (P : Program) where
  taint : Node → BVVar P

def solve (P : Program) : TaintBitvec P :=
  let arr_taint := solveMTCMF P (listVar P) (taintT P) (∅)
  let f_taint : Node → BVVar P := fun n => if n < P.size then gA (arr_taint) n else 0
  { taint := f_taint }

theorem taintWf (P : Program) : MTC.Wf (listVar P) (taintT P) :=
  ⟨⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (source_sub P n x hx)⟩, fun x hx => Std.HashSet.mem_toList.mpr hx⟩
def taintSol (P : Program) : Node → Vars := decFVar P (solve P).taint
theorem taint_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMF P (listVar P) (taintT P) (∅) (taintSol P) ∧
    ∀ h, MTCSpecMF P (listVar P) (taintT P) (∅) h → ∀ n, ∀ x ∈ taintSol P n, x ∈ h n :=
  resMTCMF_correct wf (listVar_nodup P) (taintWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.Taint
