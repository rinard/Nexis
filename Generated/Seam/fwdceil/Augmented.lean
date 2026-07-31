-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdCeil.gsl by `lake exe gen` — do not edit.
import Generated.Seam.fwdceil.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `fc` (`FwdCeil`). -/

def fcR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ π', x ∈ MTC.evs (c.node, c'.node) (fcT P) π ∨ x ∈ fcLo P c'.node

theorem fc_drives (P : Program) (wf : WellFormed P) : Drives P (fcR P) (fcSol P) :=
  fun c c' hstep => (fcSol_valid P wf).predict c c' hstep

theorem fc_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (fcR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem fc_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (fcR P) ⟨c, fcSol P c.node⟩ ⟨c', fcSol P c'.node⟩ := progress (fc_drives P wf) hs

theorem fc_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (fcR P) ⟨c, fcSol P c.node⟩ ⟨c', fcSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (fcR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (fc_drives P wf)

#assert_clean_axioms fc_drives
#assert_clean_axioms fc_progress

end BaseLanguage.Analyses.FwdCeil
