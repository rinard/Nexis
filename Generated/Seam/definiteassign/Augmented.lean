-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DefiniteAssign.gsl by `lake exe gen` — do not edit.
import Generated.Seam.definiteassign.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DefiniteAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `da` (`DefiniteAssign`). -/

def daR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => π'.Subset ((genVars P c.node).union (π.inter (transpGenVars P c.node)))

theorem da_drives (P : Program) (wf : WellFormed P) : Drives P (daR P) (daSol P) :=
  fun c c' hstep => (daSol_valid P wf).update c c' hstep

theorem da_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (daR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem da_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (daR P) ⟨c, daSol P c.node⟩ ⟨c', daSol P c'.node⟩ := progress (da_drives P wf) hs

theorem da_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (daR P) ⟨c, daSol P c.node⟩ ⟨c', daSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (daR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (da_drives P wf)

#assert_clean_axioms da_drives
#assert_clean_axioms da_progress

end BaseLanguage.Analyses.DefiniteAssign
