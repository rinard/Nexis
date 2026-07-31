-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PartialAvail.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.partialavail.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PartialAvail
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure PartialAvail (P : Program) (pavail : Node → Exprs) : Prop where
  update : ∀ c c', Step P c c' → ((genExprs P c.node).union ((pavail c.node).inter (transpExprs P c.node))).Subset (pavail c'.node)
  seed   : Exprs.Subset (∅) (pavail P.entry)
  within : ∀ n, (pavail n).Subset (allExprs P)

theorem pavail_iff_flow (P : Program) (h : Node → Exprs) :
    PartialAvail P h ↔ MTCSpecMF P (listExpr P) (pavailT P) (∅) h := by
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

theorem pavailSol_valid (P : Program) (wf : WellFormed P) : PartialAvail P (pavailSol P) :=
  (pavail_iff_flow P _).mpr (pavail_correct P wf).1
theorem pavail_least (P : Program) (wf : WellFormed P) :
    ∀ g, PartialAvail P g → ∀ n, (pavailSol P n).Subset (g n) :=
  fun g hg n x hx => (pavail_correct P wf).2 g ((pavail_iff_flow P g).mp hg) n x hx

#assert_clean_axioms pavailSol_valid
#assert_clean_axioms pavail_least

end BaseLanguage.Analyses.PartialAvail
