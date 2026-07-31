-- Copyright (c) 2026 Martin Rinard
import analyses.bwdslice.BwdSliceDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.BwdSlice.BwdSliceDefsSub` — the `_sub` (⊆ universe) domain lemmas.

The term `image ∪ (var ∖ defVars)` needs `defVars_sub` (the carry's `diffc` leaf); the floor clamp needs
`crit_sub` (the empty `∅` seed is discharged inline by the emitter). `defVars = definedVars` reuses the base fact; `crit` is a filter
of `usedVars`. (The `image` atom's universe `Wf` is `mem_toList`, so `flowsBack` needs no `_sub`.)
Axiom-clean.
-/
namespace BaseLanguage.Analyses.BwdSlice
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

-- `definedVars_sub` (the carry's `diffc` leaf) comes from `LocalsSub` via `include Tac.Locals`.
theorem crit_sub (P : Program) (n : Node) : (crit P n).Subset (allVars P) := by
  intro x hx; unfold Tac.Locals.allVars; exact Vars.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.BwdSlice
