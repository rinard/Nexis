-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Reachable.gsl by `lake exe gen` — do not edit.
import Generated.Seam.reachable.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Reachable
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `reach` (`Reachable`). -/

def reachR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => ((genNode P c.node).union (π.inter (transpAllNodes P c.node))).Subset π'

theorem reach_drives (P : Program) (wf : WellFormed P) : Drives P (reachR P) (reachSol P) :=
  fun c c' hstep => (reachSol_valid P wf).update c c' hstep

theorem reach_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (reachR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem reach_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (reachR P) ⟨c, reachSol P c.node⟩ ⟨c', reachSol P c'.node⟩ := progress (reach_drives P wf) hs

theorem reach_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (reachR P) ⟨c, reachSol P c.node⟩ ⟨c', reachSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (reachR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (reach_drives P wf)

#assert_clean_axioms reach_drives
#assert_clean_axioms reach_progress

end BaseLanguage.Analyses.Reachable
