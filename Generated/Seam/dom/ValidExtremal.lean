-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Dom.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.dom.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Dom
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Dom (P : Program) (sdom : Node → Defs) : Prop where
  update : ∀ c c', Step P c c' → (sdom c'.node).Subset (((genNode P c.node).union ((sdom c.node))))
  seed   : (sdom P.entry).Subset (∅)
  within : ∀ n, (sdom n).Subset (allNodes P)

theorem sdom_iff_flow (P : Program) (h : Node → Defs) :
    Dom P h ↔ MTCSpec P (listNode P) (sdomT P) (∅) h := by
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

theorem sdomSol_valid (P : Program) (wf : WellFormed P) : Dom P (sdomSol P) :=
  (sdom_iff_flow P _).mpr (sdom_correct P wf).1
theorem sdom_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Dom P g → ∀ n, (g n).Subset (sdomSol P n) :=
  fun g hg n x hx => (sdom_correct P wf).2 g ((sdom_iff_flow P g).mp hg) n x hx

#assert_clean_axioms sdomSol_valid
#assert_clean_axioms sdom_greatest

end BaseLanguage.Analyses.Dom
