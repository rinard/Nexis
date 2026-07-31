-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdSlice.gsl by `lake exe gen` — do not edit.
import Generated.Seam.bwdslice.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdSlice
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `slice` (`BwdSlice`). -/

def sliceR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => (Vars.Subset ((((MTC.imageS (allVars P) (flowsBack P c.node) (π'))).union (((π').filter (fun y => !(definedVars P c.node).contains y))))) π) ∧ ((crit P c.node).Subset π)

theorem slice_drives (P : Program) (wf : WellFormed P) : Drives P (sliceR P) (sliceSol P) :=
  fun c c' hstep => ⟨(sliceSol_valid P wf).predict c c' hstep, (sliceSol_valid P wf).check c.node⟩

theorem slice_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (sliceR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem slice_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (sliceR P) ⟨c, sliceSol P c.node⟩ ⟨c', sliceSol P c'.node⟩ := progress (slice_drives P wf) hs

theorem slice_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (sliceR P) ⟨c, sliceSol P c.node⟩ ⟨c', sliceSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (sliceR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (slice_drives P wf)

#assert_clean_axioms slice_drives
#assert_clean_axioms slice_progress

end BaseLanguage.Analyses.BwdSlice
