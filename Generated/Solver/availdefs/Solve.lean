-- Copyright (c) 2026 Martin Rinard
-- GENERATED from AvailDefs.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.AvailDefs
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def availT (P : Program) : MTC Node :=
  .union (.const (fun (n, _) => genDefs P n)) (.inter .var (.const (fun (n, _) => transpDefs P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure AvailDefsBitvec (P : Program) where
  avail : Node → BVNode P

def solve (P : Program) : AvailDefsBitvec P :=
  let arr_avail := solveMTC P (listNode P) (availT P) (∅)
  let f_avail : Node → BVNode P := fun n => (arr_avail)[n]?.getD (topV (widthNode P))
  { avail := f_avail }

theorem availWf (P : Program) : MTC.Wf (listNode P) (availT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genDefs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpDefs_sub P n x hx)⟩⟩
def availSol (P : Program) : Node → Defs := decFNode P (solve P).avail
theorem avail_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listNode P) (availT P) (∅) (availSol P) ∧
    ∀ h, MTCSpec P (listNode P) (availT P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ availSol P n :=
  resMTC_correct wf (listNode_nodup P) (availWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.AvailDefs
