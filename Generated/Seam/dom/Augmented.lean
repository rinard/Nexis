-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Dom.gsl by `lake exe gen` — do not edit.
import Generated.Seam.dom.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Dom
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `sdom` (`Dom`). -/

def sdomR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => π'.Subset (((genNode P c.node).union (π)))

theorem sdom_drives (P : Program) (wf : WellFormed P) : Drives P (sdomR P) (sdomSol P) :=
  fun c c' hstep => (sdomSol_valid P wf).update c c' hstep

theorem sdom_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (sdomR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem sdom_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (sdomR P) ⟨c, sdomSol P c.node⟩ ⟨c', sdomSol P c'.node⟩ := progress (sdom_drives P wf) hs

theorem sdom_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (sdomR P) ⟨c, sdomSol P c.node⟩ ⟨c', sdomSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (sdomR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (sdom_drives P wf)

#assert_clean_axioms sdom_drives
#assert_clean_axioms sdom_progress

end BaseLanguage.Analyses.Dom
