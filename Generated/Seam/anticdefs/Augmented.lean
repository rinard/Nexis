-- Copyright (c) 2026 Martin Rinard
-- GENERATED from AnticDefs.gsl by `lake exe gen` — do not edit.
import Generated.Seam.anticdefs.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.AnticDefs
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `antic` (`AnticDefs`). -/

def anticR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => ((π.sdiff (genDefs P c.node)).Subset π') ∧ (π.Subset ((genDefs P c.node).union (transpDefs P c.node)))

theorem antic_drives (P : Program) (wf : WellFormed P) : Drives P (anticR P) (anticSol P) :=
  fun c c' hstep => ⟨(anticSol_valid P wf).predict c c' hstep, (anticSol_valid P wf).check c.node⟩

theorem antic_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (anticR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem antic_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (anticR P) ⟨c, anticSol P c.node⟩ ⟨c', anticSol P c'.node⟩ := progress (antic_drives P wf) hs

theorem antic_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (anticR P) ⟨c, anticSol P c.node⟩ ⟨c', anticSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (anticR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (antic_drives P wf)

#assert_clean_axioms antic_drives
#assert_clean_axioms antic_progress

end BaseLanguage.Analyses.AnticDefs
