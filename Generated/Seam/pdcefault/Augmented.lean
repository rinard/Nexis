-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PDCEFault.gsl by `lake exe gen` — do not edit.
import Generated.Seam.pdcefault.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PDCEFault
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedVariables false

/-! ## `π` (`Live`). -/

def πR (P : Program) : Config → Variables → Config → Variables → Prop :=
  fun c π c' π' => (π'.Subset (π.union (defVars P c.node))) ∧ ((∃ x ∈ defVars P c.node, x ∈ π') → (rhsVars P c.node).Subset π) ∧ ((liveFloorF P c.node).Subset π)

theorem π_drives (P : Program) (wf : WellFormed P) : Drives P (πR P) (πSol P) :=
  fun c c' hstep => ⟨(πSol_valid P wf).predict c c' hstep, (πSol_valid P wf).gate c c' hstep, (πSol_valid P wf).check c.node⟩

theorem π_preservation (P : Program) (a a' : Aug Variables) (h : AugStep P (πR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem π_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (πR P) ⟨c, πSol P c.node⟩ ⟨c', πSol P c'.node⟩ := progress (π_drives P wf) hs

theorem π_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (πR P) ⟨c, πSol P c.node⟩ ⟨c', πSol P c'.node⟩) ∧
    (∀ a a' : Aug Variables, AugStep P (πR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (π_drives P wf)

#assert_clean_axioms π_drives
#assert_clean_axioms π_progress

/-! ## `η` (`Sink`). -/

def ηR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => π'.Subset ((born P c.node).union (π.inter (pass P c.node)))

theorem η_drives (P : Program) (wf : WellFormed P) : Drives P (ηR P) (ηSol P) :=
  fun c c' hstep => (ηSol_valid P wf).update c c' hstep

theorem η_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (ηR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem η_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (ηR P) ⟨c, ηSol P c.node⟩ ⟨c', ηSol P c'.node⟩ := progress (η_drives P wf) hs

theorem η_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (ηR P) ⟨c, ηSol P c.node⟩ ⟨c', ηSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (ηR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (η_drives P wf)

#assert_clean_axioms η_drives
#assert_clean_axioms η_progress

end BaseLanguage.Analyses.PDCEFault
