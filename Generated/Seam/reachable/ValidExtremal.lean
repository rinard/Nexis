-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Reachable.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.reachable.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Reachable
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Reachable (P : Program) (reach : Node → Defs) : Prop where
  update : ∀ c c', Step P c c' → ((genNode P c.node).union ((reach c.node).inter (transpAllNodes P c.node))).Subset (reach c'.node)
  seed   : Defs.Subset (∅) (reach P.entry)
  within : ∀ n, (reach n).Subset (allNodes P)

theorem reach_iff_flow (P : Program) (h : Node → Defs) :
    Reachable P h ↔ MTCSpecMF P (listNode P) (reachT P) (∅) h := by
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

theorem reachSol_valid (P : Program) (wf : WellFormed P) : Reachable P (reachSol P) :=
  (reach_iff_flow P _).mpr (reach_correct P wf).1
theorem reach_least (P : Program) (wf : WellFormed P) :
    ∀ g, Reachable P g → ∀ n, (reachSol P n).Subset (g n) :=
  fun g hg n x hx => (reach_correct P wf).2 g ((reach_iff_flow P g).mp hg) n x hx

#assert_clean_axioms reachSol_valid
#assert_clean_axioms reach_least

end BaseLanguage.Analyses.Reachable
