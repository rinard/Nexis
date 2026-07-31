-- Copyright (c) 2026 Martin Rinard
-- GENERATED from AvailDefs.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.availdefs.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.AvailDefs
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure AvailDefs (P : Program) (avail : Node → Defs) : Prop where
  update : ∀ c c', Step P c c' → (avail c'.node).Subset ((genDefs P c.node).union ((avail c.node).inter (transpDefs P c.node)))
  seed   : (avail P.entry).Subset (∅)
  within : ∀ n, (avail n).Subset (allDefs P)

theorem avail_iff_flow (P : Program) (h : Node → Defs) :
    AvailDefs P h ↔ MTCSpec P (listNode P) (availT P) (∅) h := by
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

theorem availSol_valid (P : Program) (wf : WellFormed P) : AvailDefs P (availSol P) :=
  (avail_iff_flow P _).mpr (avail_correct P wf).1
theorem avail_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, AvailDefs P g → ∀ n, (g n).Subset (availSol P n) :=
  fun g hg n x hx => (avail_correct P wf).2 g ((avail_iff_flow P g).mp hg) n x hx

#assert_clean_axioms availSol_valid
#assert_clean_axioms avail_greatest

end BaseLanguage.Analyses.AvailDefs
