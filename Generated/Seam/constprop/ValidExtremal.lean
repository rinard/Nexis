-- Copyright (c) 2026 Martin Rinard
-- GENERATED from ConstProp.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.constprop.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.ConstProp
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure ConstProp (P : Program) (cp : Node → ConstPairs) : Prop where
  update : ∀ c c', Step P c c' → (cp c'.node).Subset ((genConst P c.node).union ((cp c.node).inter (transpConst P c.node)))
  seed   : (cp P.entry).Subset (∅)
  within : ∀ n, (cp n).Subset (allConst P)

theorem cp_iff_flow (P : Program) (h : Node → ConstPairs) :
    ConstProp P h ↔ MTCSpec P (listCPair P) (cpT P) (∅) h := by
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

theorem cpSol_valid (P : Program) (wf : WellFormed P) : ConstProp P (cpSol P) :=
  (cp_iff_flow P _).mpr (cp_correct P wf).1
theorem cp_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, ConstProp P g → ∀ n, (g n).Subset (cpSol P n) :=
  fun g hg n x hx => (cp_correct P wf).2 g ((cp_iff_flow P g).mp hg) n x hx

#assert_clean_axioms cpSol_valid
#assert_clean_axioms cp_greatest

end BaseLanguage.Analyses.ConstProp
