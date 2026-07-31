-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Live.gsl by `lake exe gen` — do not edit.
import analyses.live.LiveDefs
import analyses.live.LiveDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.Live
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def liveT (P : Program) : MTC Var :=
  .union (.gate (fun (n, _) => defVars P n) (fun (n, _) => rhsVars P n)) (.diffc .var (fun (n, _) => defVars P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure LiveBitvec (P : Program) where
  live : Node → BVVar P

def solve (P : Program) : LiveBitvec P :=
  let arr_live := solveMTCB P (listVar P) (liveT P) (condVars P) (liveSeed P)
  let f_live : Node → BVVar P := fun n => if n < P.size then gA (arr_live) n else encode (listVar P) ((condVars P) n)
  { live := f_live }

theorem liveWf (P : Program) : MTC.Wf (listVar P) (liveT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (rhsVars_sub P n x hx)⟩, ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx)⟩⟩
def liveSol (P : Program) : Node → Vars := decFVar P (solve P).live
theorem live_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listVar P) (liveT P) (condVars P) (liveSeed P) (liveSol P) ∧
    ∀ h, MTCSpecB P (listVar P) (liveT P) (condVars P) (liveSeed P) h → ∀ n, ∀ x ∈ liveSol P n, x ∈ h n :=
  resMTCB_correct (lo := condVars P) (sd := liveSeed P) wf (listVar_nodup P) (liveWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (condVars_sub P n x hx))
    (fun x hx => Std.HashSet.mem_toList.mpr (liveSeed_sub P x hx))

end BaseLanguage.Analyses.Live
