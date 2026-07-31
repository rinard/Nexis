-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMay.gsl by `lake exe gen` — do not edit.
import Generated.Seam.dcbwdmay.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcBwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `dy` (`DcBwdMay`). -/

def dyR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => (∀ x ∈ MTC.evs (c.node, c'.node) (dyT P) π', x ∈ dyHi P c.node → x ∈ π) ∧ (∀ x ∈ dyLo P c.node, x ∈ π)

theorem dy_drives (P : Program) (wf : WellFormed P) : Drives P (dyR P) (dySol P) :=
  fun c c' hstep => ⟨(dySol_valid P wf).predict c c' hstep, (dySol_valid P wf).floor c.node⟩

theorem dy_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (dyR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem dy_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (dyR P) ⟨c, dySol P c.node⟩ ⟨c', dySol P c'.node⟩ := progress (dy_drives P wf) hs

theorem dy_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (dyR P) ⟨c, dySol P c.node⟩ ⟨c', dySol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (dyR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (dy_drives P wf)

#assert_clean_axioms dy_drives
#assert_clean_axioms dy_progress

end BaseLanguage.Analyses.DcBwdMay
