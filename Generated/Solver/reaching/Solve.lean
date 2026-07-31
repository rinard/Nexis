-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Reaching.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.Reaching
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def reachT (P : Program) : MTC Node :=
  .union (.const (fun (n, _) => genDefs P n)) (.inter .var (.const (fun (n, _) => transpDefs P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure ReachingBitvec (P : Program) where
  reach : Node → BVNode P

def solve (P : Program) : ReachingBitvec P :=
  let arr_reach := solveMTCMF P (listNode P) (reachT P) (∅)
  let f_reach : Node → BVNode P := fun n => if n < P.size then gA (arr_reach) n else 0
  { reach := f_reach }

theorem reachWf (P : Program) : MTC.Wf (listNode P) (reachT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genDefs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpDefs_sub P n x hx)⟩⟩
def reachSol (P : Program) : Node → Defs := decFNode P (solve P).reach
theorem reach_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMF P (listNode P) (reachT P) (∅) (reachSol P) ∧
    ∀ h, MTCSpecMF P (listNode P) (reachT P) (∅) h → ∀ n, ∀ x ∈ reachSol P n, x ∈ h n :=
  resMTCMF_correct wf (listNode_nodup P) (reachWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.Reaching
