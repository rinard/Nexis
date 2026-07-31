-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMust.gsl by `lake exe gen` — do not edit.
import Generated.Seam.dcfwdmust.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcFwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `df` (`DcFwdMust`). -/

def dfR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ∀ x ∈ π', x ∈ MTC.evs (c.node, c'.node) (dfT P) π ∨ x ∈ dfLo P c'.node

theorem df_drives (P : Program) (wf : WellFormed P) : Drives P (dfR P) (dfSol P) :=
  fun c c' hstep => (dfSol_valid P wf).predict c c' hstep

theorem df_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (dfR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem df_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (dfR P) ⟨c, dfSol P c.node⟩ ⟨c', dfSol P c'.node⟩ := progress (df_drives P wf) hs

theorem df_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (dfR P) ⟨c, dfSol P c.node⟩ ⟨c', dfSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (dfR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (df_drives P wf)

#assert_clean_axioms df_drives
#assert_clean_axioms df_progress

end BaseLanguage.Analyses.DcFwdMust
