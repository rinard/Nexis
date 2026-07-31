-- Copyright (c) 2026 Martin Rinard
import analyses.bwdmay.BwdMayDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.BwdMay.BwdMayDefsSub` — the `_sub` (⊆ universe) domain lemmas.

Only the analysis's own additions need `_sub`s: `extraM`/`floorM` (both `= Tac.Locals.obsDefs`, so both
reduce to `obsDefs_sub`). The base `genDefs_sub`/`transpDefs_sub` come from `LocalsSub` via
`include Tac.Locals`; the empty `∅` seed is discharged inline by the correctness combinator. Axiom-clean.
-/
namespace BaseLanguage.Analyses.BwdMay
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem extraM_sub (P : Program) (n : Node) : (extraM P n).Subset (allDefs P) :=
  Tac.Locals.obsDefs_sub P
theorem floorM_sub (P : Program) (n : Node) : (floorM P n).Subset (allDefs P) :=
  Tac.Locals.obsDefs_sub P

end BaseLanguage.Analyses.BwdMay
