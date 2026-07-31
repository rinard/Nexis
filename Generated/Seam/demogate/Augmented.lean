-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DemoGate.gsl by `lake exe gen` — do not edit.
import Generated.Seam.demogate.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DemoGate
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `dg` (`DemoGate`). -/

def dgR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => (Vars.Subset ((((if (π').toList.any (fun w => (definedVars P c.node).contains w) then rhsVars P c.node else (∅ : Vars))).union (((definedVars P c.node).union (((π').filter (fun y => (condVars P c.node).contains y))))))) π) ∧ ((condVars P c.node).Subset π)

theorem dg_drives (P : Program) (wf : WellFormed P) : Drives P (dgR P) (dgSol P) :=
  fun c c' hstep => ⟨(dgSol_valid P wf).predict c c' hstep, (dgSol_valid P wf).check c.node⟩

theorem dg_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (dgR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem dg_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (dgR P) ⟨c, dgSol P c.node⟩ ⟨c', dgSol P c'.node⟩ := progress (dg_drives P wf) hs

theorem dg_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (dgR P) ⟨c, dgSol P c.node⟩ ⟨c', dgSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (dgR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (dg_drives P wf)

#assert_clean_axioms dg_drives
#assert_clean_axioms dg_progress

end BaseLanguage.Analyses.DemoGate
