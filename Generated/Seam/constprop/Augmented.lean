-- Copyright (c) 2026 Martin Rinard
-- GENERATED from ConstProp.gsl by `lake exe gen` — do not edit.
import Generated.Seam.constprop.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.ConstProp
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `cp` (`ConstProp`). -/

def cpR (P : Program) : Config → ConstPairs → Config → ConstPairs → Prop :=
  fun c π c' π' => π'.Subset ((genConst P c.node).union (π.inter (transpConst P c.node)))

theorem cp_drives (P : Program) (wf : WellFormed P) : Drives P (cpR P) (cpSol P) :=
  fun c c' hstep => (cpSol_valid P wf).update c c' hstep

theorem cp_preservation (P : Program) (a a' : Aug ConstPairs) (h : AugStep P (cpR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem cp_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (cpR P) ⟨c, cpSol P c.node⟩ ⟨c', cpSol P c'.node⟩ := progress (cp_drives P wf) hs

theorem cp_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (cpR P) ⟨c, cpSol P c.node⟩ ⟨c', cpSol P c'.node⟩) ∧
    (∀ a a' : Aug ConstPairs, AugStep P (cpR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (cp_drives P wf)

#assert_clean_axioms cp_drives
#assert_clean_axioms cp_progress

end BaseLanguage.Analyses.ConstProp
