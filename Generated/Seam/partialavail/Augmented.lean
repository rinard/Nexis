-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PartialAvail.gsl by `lake exe gen` — do not edit.
import Generated.Seam.partialavail.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PartialAvail
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `pavail` (`PartialAvail`). -/

def pavailR (P : Program) : Config → Exprs → Config → Exprs → Prop :=
  fun c π c' π' => ((genExprs P c.node).union (π.inter (transpExprs P c.node))).Subset π'

theorem pavail_drives (P : Program) (wf : WellFormed P) : Drives P (pavailR P) (pavailSol P) :=
  fun c c' hstep => (pavailSol_valid P wf).update c c' hstep

theorem pavail_preservation (P : Program) (a a' : Aug Exprs) (h : AugStep P (pavailR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem pavail_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (pavailR P) ⟨c, pavailSol P c.node⟩ ⟨c', pavailSol P c'.node⟩ := progress (pavail_drives P wf) hs

theorem pavail_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (pavailR P) ⟨c, pavailSol P c.node⟩ ⟨c', pavailSol P c'.node⟩) ∧
    (∀ a a' : Aug Exprs, AugStep P (pavailR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (pavail_drives P wf)

#assert_clean_axioms pavail_drives
#assert_clean_axioms pavail_progress

end BaseLanguage.Analyses.PartialAvail
