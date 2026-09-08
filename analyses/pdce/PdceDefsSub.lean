-- Copyright (c) 2026 Martin Rinard
import analyses.pdce.PdceDefs
import BaseLanguage.IR.SubPeeler

/-!
# `PDCE.PdceDefsSub` — the node-local `_sub` (⊆ universe) domain lemmas.

For every own node-local def `f`, the fact `f P n ⊆ <universe> P` (needed for the `MTC.Wf` obligation).
These are **domain facts** authored alongside `PdceDefs`, exactly as the base-family `_sub` lemmas are
authored once in `BaseLanguage/IR/LocalsSub.lean`. The general generator (`GenGeneral`) references them by
the mechanical name `<fam>_sub`. Each is axiom-clean; the proofs are the generic universe-membership
peeler (`foldl_union_contrib`) instantiated per def.
-/

namespace BaseLanguage.Analyses.PDCE
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem born_sub (P : Program) (n : Node) : (born P n).Subset (allAsgns P) := by
  fold_sub born P n into allAsgns set Assignments close [Assignments.empty]

theorem pass_sub (P : Program) (n : Node) : (pass P n).Subset (allAsgns P) := fun x hx => (Analysis.SetOps.mem_filter'.mp hx).1

theorem sinkSeed_sub (P : Program) : (sinkSeed P).Subset (allAsgns P) := by
  intro x hx; simp [sinkSeed, Assignments.empty] at hx

theorem condVars_sub (P : Program) (n : Node) : (condVars P n).Subset (allVars P) := by
  fold_sub condVars P n into allVars set Variables close [defV, Variables.empty]

theorem defVars_sub (P : Program) (n : Node) : (defVars P n).Subset (allVars P) := by
  fold_sub defVars P n into allVars set Variables close [defV, Variables.empty]

theorem rhsVars_sub (P : Program) (n : Node) : (rhsVars P n).Subset (allVars P) := by
  fold_sub rhsVars P n into allVars set Variables close [defV, Variables.empty]

/-- The fault-preserving floor is bounded by the universe: both halves are. -/
theorem faultingRhsVars_sub (P : Program) (n : Node) :
    (faultingRhsVars P n).Subset (allVars P) := by
  intro x hx
  unfold faultingRhsVars at hx
  cases hf : P.fetch n with
  | none => rw [hf] at hx; exact absurd hx Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign y e nx =>
          rw [hf] at hx
          simp only at hx
          by_cases hff : e.faultFree = true
          · rw [if_pos hff] at hx; exact absurd hx Std.HashSet.not_mem_empty
          · rw [if_neg hff] at hx
            exact rhsVars_sub P n x (by unfold rhsVars; rw [hf]; exact hx)
      | _ => rw [hf] at hx; exact absurd hx Std.HashSet.not_mem_empty

theorem liveFloorF_sub (P : Program) (n : Node) : (liveFloorF P n).Subset (allVars P) := by
  intro x hx
  rcases Variables.mem_union.mp hx with h | h
  · exact condVars_sub P n x h
  · exact faultingRhsVars_sub P n x h

theorem liveSeed_sub (P : Program) : (liveSeed P).Subset (allVars P) := by
  intro x hx; unfold allVars; exact Variables.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.PDCE
