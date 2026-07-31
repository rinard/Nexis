-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMustFloor.gsl by `lake exe gen` — do not edit.
import Generated.Seam.fwdmustfloor.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdMustFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `fmf` (`FwdMustFloor`). -/

def fmfR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ π', x ∈ MTC.evs (c.node, c'.node) (fmfT P) π ∨ x ∈ fmfLo P c'.node

theorem fmf_drives (P : Program) (wf : WellFormed P) : Drives P (fmfR P) (fmfSol P) :=
  fun c c' hstep => (fmfSol_valid P wf).predict c c' hstep

theorem fmf_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (fmfR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem fmf_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (fmfR P) ⟨c, fmfSol P c.node⟩ ⟨c', fmfSol P c'.node⟩ := progress (fmf_drives P wf) hs

theorem fmf_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (fmfR P) ⟨c, fmfSol P c.node⟩ ⟨c', fmfSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (fmfR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (fmf_drives P wf)

#assert_clean_axioms fmf_drives
#assert_clean_axioms fmf_progress

end BaseLanguage.Analyses.FwdMustFloor
