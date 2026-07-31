-- Copyright (c) 2026 Martin Rinard
import analyses.bwdchain.BwdChainDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.BwdChain.BwdChainDefsSub` — the `_sub` (⊆ universe) domain lemmas.

Only the analysis's own addition needs a `_sub`: `extraN` (`= Tac.Locals.obsDefs`, so `obsDefs_sub`). The
base `genDefs_sub`/`transpDefs_sub` come from `LocalsSub` via `include Tac.Locals`; the `ceilN` ceiling
needs none (`resMTCBM_correct` takes only the seed sub, and the empty `∅` seed is discharged inline).
Axiom-clean.
-/
namespace BaseLanguage.Analyses.BwdChain
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem extraN_sub (P : Program) (n : Node) : (extraN P n).Subset (allDefs P) :=
  Tac.Locals.obsDefs_sub P

end BaseLanguage.Analyses.BwdChain
