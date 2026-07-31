-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMay.gsl by `lake exe gen` — do not edit.
import Generated.Seam.dcfwdmay.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcFwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `dm` (`DcFwdMay`). -/

def dmR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ MTC.evs (c.node, c'.node) (dmT P) π, x ∈ dmHi P c'.node → x ∈ π'

theorem dm_drives (P : Program) (wf : WellFormed P) : Drives P (dmR P) (dmSol P) :=
  fun c c' hstep => (dmSol_valid P wf).predict c c' hstep

theorem dm_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (dmR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem dm_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (dmR P) ⟨c, dmSol P c.node⟩ ⟨c', dmSol P c'.node⟩ := progress (dm_drives P wf) hs

theorem dm_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (dmR P) ⟨c, dmSol P c.node⟩ ⟨c', dmSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (dmR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (dm_drives P wf)

#assert_clean_axioms dm_drives
#assert_clean_axioms dm_progress

end BaseLanguage.Analyses.DcFwdMay
