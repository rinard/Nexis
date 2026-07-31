-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdChain.gsl by `lake exe gen` — do not edit.
import Generated.Seam.bwdchain.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdChain
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `g` (`BwdChain`). -/

def gR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => (π.Subset (((((genDefs P c.node).union (((π').filter (fun y => (transpDefs P c.node).contains y))))).union (extraN P c.node)))) ∧ (π.Subset (ceilN P c.node))

theorem g_drives (P : Program) (wf : WellFormed P) : Drives P (gR P) (gSol P) :=
  fun c c' hstep => ⟨(gSol_valid P wf).predict c c' hstep, (gSol_valid P wf).check c.node⟩

theorem g_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (gR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem g_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (gR P) ⟨c, gSol P c.node⟩ ⟨c', gSol P c'.node⟩ := progress (g_drives P wf) hs

theorem g_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (gR P) ⟨c, gSol P c.node⟩ ⟨c', gSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (gR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (g_drives P wf)

#assert_clean_axioms g_drives
#assert_clean_axioms g_progress

end BaseLanguage.Analyses.BwdChain
