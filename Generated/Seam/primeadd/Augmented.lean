-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PrimeAdd.gsl by `lake exe gen` — do not edit.
import Generated.Seam.primeadd.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PrimeAdd
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedVariables false

/-! ## `g` (`PrimeAdd`). -/

def gR (P : Program) : Config → Defs → Config → Defs → Prop :=
  fun c π c' π' => Defs.Subset (((((π).union (obsGen P c.node))).union ((((MTC.gatherS (allDefs P) (fun z => below P c.node z) (π))).filter (fun y => ((if (π).toList.any (fun w => (primes P c.node).contains w) then allDefs P else (∅ : Defs))).contains y))))) π'

theorem g_drives (P : Program) (wf : WellFormed P) : Drives P (gR P) (gSol P) :=
  fun c c' hstep => (gSol_valid P wf).update c c' hstep

theorem g_preservation (P : Program) (a a' : Aug Defs) (h : AugStep P (gR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem g_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (gR P) ⟨c, gSol P c.node⟩ ⟨c', gSol P c'.node⟩ := progress (g_drives P wf) hs

theorem g_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (gR P) ⟨c, gSol P c.node⟩ ⟨c', gSol P c'.node⟩) ∧
    (∀ a a' : Aug Defs, AugStep P (gR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (g_drives P wf)

#assert_clean_axioms g_drives
#assert_clean_axioms g_progress

end BaseLanguage.Analyses.PrimeAdd
