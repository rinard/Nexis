-- Copyright (c) 2026 Martin Rinard
import analyses.taint.TaintDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.Taint.TaintDefsSub` — the `_sub` (⊆ universe) domain lemmas.

`source(n) ⊆ allVars P` (the `MTC.Wf` obligation for the `const` summand) and the empty-seed fact.
`source` is a filter of `usedVars`, so its containment reuses the base `usedVars_sub`. (The `image` atom's
universe `Wf` is `∀ x ∈ allVars, x ∈ allVars` = `mem_toList`, so `flowsTo` needs no `_sub`.) Axiom-clean.
-/
namespace BaseLanguage.Analyses.Taint
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem source_sub (P : Program) (n : Node) : (source P n).Subset (allVars P) :=
  fun x hx => Tac.Locals.usedVars_sub P n x (Analysis.SetOps.mem_filter'.mp hx).1

end BaseLanguage.Analyses.Taint
