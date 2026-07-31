-- Copyright (c) 2026 Martin Rinard
import analyses.structavail.StructAvailDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.StructAvail.StructAvailDefsSub` — the `_sub` (⊆ universe) domain lemmas.

`localGen(n) ⊆ allDefs P` (the `MTC.Wf` obligation for the `const` gen) and the empty-seed fact.
`localGen = genDefs`, so its containment reuses the base `genDefs_sub`. (The `gather` atom's precondition
def `structSub` needs no `_sub`: its result is bounded by the universe `allDefs`, and the gather's
universe `Wf` is `∀ x ∈ allDefs, x ∈ allDefs` = `mem_toList`.) Each is axiom-clean.
-/
namespace BaseLanguage.Analyses.StructAvail
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem localGen_sub (P : Program) (n : Node) : (localGen P n).Subset (allDefs P) := by
  intro x hx; unfold localGen at hx; split at hx
  · exact Tac.Locals.genDefs_sub P n x hx
  · simp [Defs.empty] at hx

end BaseLanguage.Analyses.StructAvail
