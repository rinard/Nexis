-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DefiniteAssign.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.definiteassign.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DefiniteAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DefiniteAssign (P : Program) (da : Node → Vars) : Prop where
  update : ∀ c c', Step P c c' → (da c'.node).Subset ((genVars P c.node).union ((da c.node).inter (transpGenVars P c.node)))
  seed   : (da P.entry).Subset (∅)
  within : ∀ n, (da n).Subset (allGenVars P)

theorem da_iff_flow (P : Program) (h : Node → Vars) :
    DefiniteAssign P h ↔ MTCSpec P (listVar P) (daT P) (∅) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hs.update c c' hstep x hx
    · intro x hx; exact hs.seed x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · intro hf
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hf.1 c c' hstep x hx
    · intro x hx; exact hf.2.1 x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hf.2.2 n x hx)

theorem daSol_valid (P : Program) (wf : WellFormed P) : DefiniteAssign P (daSol P) :=
  (da_iff_flow P _).mpr (da_correct P wf).1
theorem da_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, DefiniteAssign P g → ∀ n, (g n).Subset (daSol P n) :=
  fun g hg n x hx => (da_correct P wf).2 g ((da_iff_flow P g).mp hg) n x hx

#assert_clean_axioms daSol_valid
#assert_clean_axioms da_greatest

end BaseLanguage.Analyses.DefiniteAssign
