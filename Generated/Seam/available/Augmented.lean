-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Available.gsl by `lake exe gen` — do not edit.
import Generated.Seam.available.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Available
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `avail` (`Available`). -/

def availR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => π'.Subset ((genExprs P c.node).union (π.inter (transpExprs P c.node)))

theorem avail_drives (P : Program) (wf : WellFormed P) : Drives P (availR P) (availSol P) :=
  fun c c' hstep => (availSol_valid P wf).update c c' hstep

theorem avail_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (availR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem avail_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (availR P) ⟨c, availSol P c.node⟩ ⟨c', availSol P c'.node⟩ := progress (avail_drives P wf) hs

theorem avail_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (availR P) ⟨c, availSol P c.node⟩ ⟨c', availSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (availR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (avail_drives P wf)

#assert_clean_axioms avail_drives
#assert_clean_axioms avail_progress

end BaseLanguage.Analyses.Available
