-- Copyright (c) 2026 Martin Rinard
-- GENERATED from MaybeAssign.gsl by `lake exe gen` — do not edit.
import Generated.Seam.maybeassign.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.MaybeAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `ma` (`MaybeAssign`). -/

def maR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => ((genVars P c.node).union (π.inter (transpGenVars P c.node))).Subset π'

theorem ma_drives (P : Program) (wf : WellFormed P) : Drives P (maR P) (maSol P) :=
  fun c c' hstep => (maSol_valid P wf).update c c' hstep

theorem ma_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (maR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem ma_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (maR P) ⟨c, maSol P c.node⟩ ⟨c', maSol P c'.node⟩ := progress (ma_drives P wf) hs

theorem ma_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (maR P) ⟨c, maSol P c.node⟩ ⟨c', maSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (maR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (ma_drives P wf)

#assert_clean_axioms ma_drives
#assert_clean_axioms ma_progress

end BaseLanguage.Analyses.MaybeAssign
