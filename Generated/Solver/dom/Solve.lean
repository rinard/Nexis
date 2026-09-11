-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Dom.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.Dom
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allNodes P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allNodes P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def sdomT (P : Program) : MTC Node :=
  .union (.const (fun (n, _) => genNode P n)) .var
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure DomBitvec (P : Program) where
  sdom : Node → BVNode P

def solve (P : Program) : DomBitvec P :=
  let arr_sdom := solveMTC P (listNode P) (sdomT P) (∅)
  let f_sdom : Node → BVNode P := fun n => (arr_sdom)[n]?.getD (topV (widthNode P))
  { sdom := f_sdom }

theorem sdomWf (P : Program) : MTC.Wf (listNode P) (sdomT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genNode_sub P n x hx), by trivial⟩
def sdomSol (P : Program) : Node → Defs := decFNode P (solve P).sdom
theorem sdom_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listNode P) (sdomT P) (∅) (sdomSol P) ∧
    ∀ h, MTCSpec P (listNode P) (sdomT P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ sdomSol P n :=
  resMTC_correct wf (listNode_nodup P) (sdomWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.Dom
