-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Taint.gsl by `lake exe gen` — do not edit.
import Generated.Seam.taint.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Taint
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `taint` (`Taint`). -/

def taintR (P : Program) : Config → Vars → Config → Vars → Prop :=
  fun c π c' π' => Vars.Subset (((((π).union (source P c.node))).union ((MTC.imageS (allVars P) (flowsTo P c.node) (π))))) π'

theorem taint_drives (P : Program) (wf : WellFormed P) : Drives P (taintR P) (taintSol P) :=
  fun c c' hstep => (taintSol_valid P wf).update c c' hstep

theorem taint_preservation (P : Program) (a a' : Aug Vars) (h : AugStep P (taintR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem taint_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (taintR P) ⟨c, taintSol P c.node⟩ ⟨c', taintSol P c'.node⟩ := progress (taint_drives P wf) hs

theorem taint_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (taintR P) ⟨c, taintSol P c.node⟩ ⟨c', taintSol P c'.node⟩) ∧
    (∀ a a' : Aug Vars, AugStep P (taintR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (taint_drives P wf)

#assert_clean_axioms taint_drives
#assert_clean_axioms taint_progress

end BaseLanguage.Analyses.Taint
