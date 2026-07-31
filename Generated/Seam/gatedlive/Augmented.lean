-- Copyright (c) 2026 Martin Rinard
-- GENERATED from GatedLive.gsl by `lake exe gen` — do not edit.
import Generated.Seam.gatedlive.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.GatedLive
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `glive` (`GatedLive`). -/

def gliveR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => (π'.Subset (π.union (definedVars P c.node))) ∧ ((∃ x ∈ definedVars P c.node, x ∈ π') → (rhsVars P c.node).Subset π) ∧ ((condVars P c.node).Subset π)

theorem glive_drives (P : Program) (wf : WellFormed P) : Drives P (gliveR P) (gliveSol P) :=
  fun c c' hstep => ⟨(gliveSol_valid P wf).predict c c' hstep, (gliveSol_valid P wf).gate c c' hstep, (gliveSol_valid P wf).check c.node⟩

theorem glive_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (gliveR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem glive_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (gliveR P) ⟨c, gliveSol P c.node⟩ ⟨c', gliveSol P c'.node⟩ := progress (glive_drives P wf) hs

theorem glive_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (gliveR P) ⟨c, gliveSol P c.node⟩ ⟨c', gliveSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (gliveR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (glive_drives P wf)

#assert_clean_axioms glive_drives
#assert_clean_axioms glive_progress

end BaseLanguage.Analyses.GatedLive
