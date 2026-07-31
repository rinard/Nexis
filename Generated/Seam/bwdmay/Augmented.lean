-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdMay.gsl by `lake exe gen` — do not edit.
import Generated.Seam.bwdmay.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `m` (`BwdMay`). -/

def mR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => (Defs.Subset (((((genDefs P c.node).union (((π').filter (fun y => (transpDefs P c.node).contains y))))).union (extraM P c.node))) π) ∧ ((floorM P c.node).Subset π)

theorem m_drives (P : Program) (wf : WellFormed P) : Drives P (mR P) (mSol P) :=
  fun c c' hstep => ⟨(mSol_valid P wf).predict c c' hstep, (mSol_valid P wf).check c.node⟩

theorem m_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (mR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem m_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (mR P) ⟨c, mSol P c.node⟩ ⟨c', mSol P c'.node⟩ := progress (m_drives P wf) hs

theorem m_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (mR P) ⟨c, mSol P c.node⟩ ⟨c', mSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (mR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (m_drives P wf)

#assert_clean_axioms m_drives
#assert_clean_axioms m_progress

end BaseLanguage.Analyses.BwdMay
