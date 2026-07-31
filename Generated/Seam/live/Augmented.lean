-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Live.gsl by `lake exe gen` — do not edit.
import Generated.Seam.live.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Live
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedVariables false

/-! ## `live` (`Live`). -/

def liveR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => (π'.Subset (π.union (defVars P c.node))) ∧ ((∃ x ∈ defVars P c.node, x ∈ π') → (rhsVars P c.node).Subset π) ∧ ((condVars P c.node).Subset π)

theorem live_drives (P : Program) (wf : WellFormed P) : Drives P (liveR P) (liveSol P) :=
  fun c c' hstep => ⟨(liveSol_valid P wf).predict c c' hstep, (liveSol_valid P wf).gate c c' hstep, (liveSol_valid P wf).check c.node⟩

theorem live_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (liveR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem live_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (liveR P) ⟨c, liveSol P c.node⟩ ⟨c', liveSol P c'.node⟩ := progress (live_drives P wf) hs

theorem live_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (liveR P) ⟨c, liveSol P c.node⟩ ⟨c', liveSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (liveR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (live_drives P wf)

#assert_clean_axioms live_drives
#assert_clean_axioms live_progress

end BaseLanguage.Analyses.Live
