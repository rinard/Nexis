-- Copyright (c) 2026 Martin Rinard
-- GENERATED from VeryBusy.gsl by `lake exe gen` — do not edit.
import Generated.Seam.verybusy.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.VeryBusy
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `busy` (`VeryBusy`). -/

def busyR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ((π.sdiff (genExprs P c.node)).Subset π') ∧ (π.Subset ((genExprs P c.node).union (transpExprs P c.node)))

theorem busy_drives (P : Program) (wf : WellFormed P) : Drives P (busyR P) (busySol P) :=
  fun c c' hstep => ⟨(busySol_valid P wf).predict c c' hstep, (busySol_valid P wf).check c.node⟩

theorem busy_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (busyR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem busy_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (busyR P) ⟨c, busySol P c.node⟩ ⟨c', busySol P c'.node⟩ := progress (busy_drives P wf) hs

theorem busy_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (busyR P) ⟨c, busySol P c.node⟩ ⟨c', busySol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (busyR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (busy_drives P wf)

#assert_clean_axioms busy_drives
#assert_clean_axioms busy_progress

end BaseLanguage.Analyses.VeryBusy
