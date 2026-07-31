-- Copyright (c) 2026 Martin Rinard
-- GENERATED from GatedLive.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.GatedLive
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def gliveT (P : Program) : MTC Var :=
  .union (.gate (fun (n, _) => definedVars P n) (fun (n, _) => rhsVars P n)) (.diffc .var (fun (n, _) => definedVars P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure GatedLiveBitvec (P : Program) where
  glive : Node → BVVar P

def solve (P : Program) : GatedLiveBitvec P :=
  let arr_glive := solveMTCB P (listVar P) (gliveT P) (condVars P) (∅)
  let f_glive : Node → BVVar P := fun n => if n < P.size then gA (arr_glive) n else encode (listVar P) ((condVars P) n)
  { glive := f_glive }

theorem gliveWf (P : Program) : MTC.Wf (listVar P) (gliveT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (definedVars_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (rhsVars_sub P n x hx)⟩, ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (definedVars_sub P n x hx)⟩⟩
def gliveSol (P : Program) : Node → Vars := decFVar P (solve P).glive
theorem glive_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listVar P) (gliveT P) (condVars P) (∅) (gliveSol P) ∧
    ∀ h, MTCSpecB P (listVar P) (gliveT P) (condVars P) (∅) h → ∀ n, ∀ x ∈ gliveSol P n, x ∈ h n :=
  resMTCB_correct (lo := condVars P) (sd := ∅) wf (listVar_nodup P) (gliveWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (condVars_sub P n x hx))
    (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.GatedLive
