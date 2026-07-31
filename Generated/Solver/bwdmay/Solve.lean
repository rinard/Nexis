-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdmay.BwdMayDefs
import analyses.bwdmay.BwdMayDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.BwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def mT (P : Program) : MTC Node :=
  .union (.union (.const (fun (n, _) => genDefs P n)) (.inter .var (.const (fun (n, _) => transpDefs P n)))) (.const (fun (n, _) => extraM P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure BwdMayBitvec (P : Program) where
  m : Node → BVNode P

def solve (P : Program) : BwdMayBitvec P :=
  let arr_m := solveMTCB P (listNode P) (mT P) (floorM P) (∅)
  let f_m : Node → BVNode P := fun n => if n < P.size then gA (arr_m) n else encode (listNode P) ((floorM P) n)
  { m := f_m }

theorem mWf (P : Program) : MTC.Wf (listNode P) (mT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genDefs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpDefs_sub P n x hx)⟩⟩, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (extraM_sub P n x hx)⟩
def mSol (P : Program) : Node → Defs := decFNode P (solve P).m
theorem m_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listNode P) (mT P) (floorM P) (∅) (mSol P) ∧
    ∀ h, MTCSpecB P (listNode P) (mT P) (floorM P) (∅) h → ∀ n, ∀ x ∈ mSol P n, x ∈ h n :=
  resMTCB_correct (lo := floorM P) (sd := ∅) wf (listNode_nodup P) (mWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (floorM_sub P n x hx))
    (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.BwdMay
