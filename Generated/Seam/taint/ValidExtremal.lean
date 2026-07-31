-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Taint.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.taint.TaintDefs
import analyses.taint.TaintDefsSub
import Generated.Solver.taint.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Taint
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Taint (P : Program) (taint : Node → Vars) : Prop where
  update : ∀ c c', Step P c c' → Vars.Subset ((((((taint c.node)).union (source P c.node))).union ((MTC.imageS (allVars P) (flowsTo P c.node) (taint c.node))))) (taint c'.node)
  seed   : Vars.Subset (∅) (taint P.entry)
  within : ∀ n, (taint n).Subset (allVars P)

theorem taint_iff_flow (P : Program) (h : Node → Vars) :
    Taint P h ↔ MTCSpecMF P (listVar P) (taintT P) (∅) h := by
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

theorem taintSol_valid (P : Program) (wf : WellFormed P) : Taint P (taintSol P) :=
  (taint_iff_flow P _).mpr (taint_correct P wf).1
theorem taint_least (P : Program) (wf : WellFormed P) :
    ∀ g, Taint P g → ∀ n, (taintSol P n).Subset (g n) :=
  fun g hg n x hx => (taint_correct P wf).2 g ((taint_iff_flow P g).mp hg) n x hx

#assert_clean_axioms taintSol_valid
#assert_clean_axioms taint_least

end BaseLanguage.Analyses.Taint
