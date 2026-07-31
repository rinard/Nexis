-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdSlice.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdslice.BwdSliceDefs
import analyses.bwdslice.BwdSliceDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.BwdSlice
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def sliceT (P : Program) : MTC Var :=
  .union (.image (allVars P) (fun (n, _) => flowsBack P n)) (.diffc .var (fun (n, _) => definedVars P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Vars := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Vars := fun n => decodeVar P (f n)

structure BwdSliceBitvec (P : Program) where
  slice : Node → BVVar P

def solve (P : Program) : BwdSliceBitvec P :=
  let arr_slice := solveMTCB P (listVar P) (sliceT P) (crit P) (∅)
  let f_slice : Node → BVVar P := fun n => if n < P.size then gA (arr_slice) n else encode (listVar P) ((crit P) n)
  { slice := f_slice }

theorem sliceWf (P : Program) : MTC.Wf (listVar P) (sliceT P) :=
  ⟨fun x hx => Std.HashSet.mem_toList.mpr hx, ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (definedVars_sub P n x hx)⟩⟩
def sliceSol (P : Program) : Node → Vars := decFVar P (solve P).slice
theorem slice_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listVar P) (sliceT P) (crit P) (∅) (sliceSol P) ∧
    ∀ h, MTCSpecB P (listVar P) (sliceT P) (crit P) (∅) h → ∀ n, ∀ x ∈ sliceSol P n, x ∈ h n :=
  resMTCB_correct (lo := crit P) (sd := ∅) wf (listVar_nodup P) (sliceWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (crit_sub P n x hx))
    (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.BwdSlice
