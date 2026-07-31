-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMust.gsl by `lake exe gen` — do not edit.
import Generated.Seam.dcbwdmust.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcBwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `db` (`DcBwdMust`). -/

def dbR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => (∀ x ∈ π, x ∈ MTC.evs (c.node, c'.node) (dbT P) π' ∨ x ∈ dbLo P c.node) ∧ (∀ x ∈ π, x ∈ dbHi P c.node)

theorem db_drives (P : Program) (wf : WellFormed P) : Drives P (dbR P) (dbSol P) :=
  fun c c' hstep => ⟨(dbSol_valid P wf).predict c c' hstep, (dbSol_valid P wf).check c.node⟩

theorem db_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (dbR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem db_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (dbR P) ⟨c, dbSol P c.node⟩ ⟨c', dbSol P c'.node⟩ := progress (db_drives P wf) hs

theorem db_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (dbR P) ⟨c, dbSol P c.node⟩ ⟨c', dbSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (dbR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (db_drives P wf)

#assert_clean_axioms db_drives
#assert_clean_axioms db_progress

end BaseLanguage.Analyses.DcBwdMust
