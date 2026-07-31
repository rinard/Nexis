-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMayCeil.gsl by `lake exe gen` — do not edit.
import Generated.Seam.fwdmayceil.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdMayCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `fmc` (`FwdMayCeil`). -/

def fmcR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ MTC.evs (c.node, c'.node) (fmcT P) π, x ∈ fmcHi P c'.node → x ∈ π'

theorem fmc_drives (P : Program) (wf : WellFormed P) : Drives P (fmcR P) (fmcSol P) :=
  fun c c' hstep => (fmcSol_valid P wf).predict c c' hstep

theorem fmc_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (fmcR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem fmc_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (fmcR P) ⟨c, fmcSol P c.node⟩ ⟨c', fmcSol P c'.node⟩ := progress (fmc_drives P wf) hs

theorem fmc_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (fmcR P) ⟨c, fmcSol P c.node⟩ ⟨c', fmcSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (fmcR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (fmc_drives P wf)

#assert_clean_axioms fmc_drives
#assert_clean_axioms fmc_progress

end BaseLanguage.Analyses.FwdMayCeil
