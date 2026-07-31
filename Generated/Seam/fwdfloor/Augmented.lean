-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdFloor.gsl by `lake exe gen` — do not edit.
import Generated.Seam.fwdfloor.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `ff` (`FwdFloor`). -/

def ffR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ MTC.evs (c.node, c'.node) (ffT P) π, x ∈ ffHi P c'.node → x ∈ π'

theorem ff_drives (P : Program) (wf : WellFormed P) : Drives P (ffR P) (ffSol P) :=
  fun c c' hstep => (ffSol_valid P wf).predict c c' hstep

theorem ff_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (ffR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem ff_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (ffR P) ⟨c, ffSol P c.node⟩ ⟨c', ffSol P c'.node⟩ := progress (ff_drives P wf) hs

theorem ff_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (ffR P) ⟨c, ffSol P c.node⟩ ⟨c', ffSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (ffR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (ff_drives P wf)

#assert_clean_axioms ff_drives
#assert_clean_axioms ff_progress

end BaseLanguage.Analyses.FwdFloor
