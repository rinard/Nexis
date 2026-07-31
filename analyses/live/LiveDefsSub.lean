-- Copyright (c) 2026 Martin Rinard
import analyses.live.LiveDefs
import BaseLanguage.IR.SubPeeler

/-!
# `Live.LiveDefsSub` — the node-local `_sub` (⊆ universe) domain lemmas.

For every own def `f`, the fact `f P n ⊆ allVars P` (needed for the `MTC.Wf`/floor/seed obligations).
Authored domain facts (like `BaseLanguage/IR/LocalsSub.lean` and the `{Pdce,Lcm}DefsSub` companions), so the
general generator (`GenGeneral`) references them by the mechanical name `<fam>_sub`. Each is axiom-clean.
-/

namespace BaseLanguage.Analyses.Live
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem condVars_sub (P : Program) (n : Node) : (condVars P n).Subset (allVars P) := by
  fold_sub condVars P n into allVars set Vars close [defV, Vars.empty]

theorem defVars_sub (P : Program) (n : Node) : (defVars P n).Subset (allVars P) := by
  fold_sub defVars P n into allVars set Vars close [defV, Vars.empty]

theorem rhsVars_sub (P : Program) (n : Node) : (rhsVars P n).Subset (allVars P) := by
  fold_sub rhsVars P n into allVars set Vars close [defV, Vars.empty]

theorem liveSeed_sub (P : Program) : (liveSeed P).Subset (allVars P) := by
  intro x hx; unfold allVars; exact Vars.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.Live
