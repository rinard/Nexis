-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DemoGate.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.demogate.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DemoGate
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DemoGate (P : Program) (dg : Node → Vars) : Prop where
  predict : ∀ c c', Step P c c' → Vars.Subset ((((if (dg c'.node).toList.any (fun w => (definedVars P c.node).contains w) then rhsVars P c.node else (∅ : Vars))).union (((definedVars P c.node).union ((((dg c'.node)).filter (fun y => (condVars P c.node).contains y))))))) (dg c.node)
  check   : ∀ n, (condVars P n).Subset (dg n)
  seed    : ∀ c, Final P c → Vars.Subset (∅) (dg c.node)
  within : ∀ n, (dg n).Subset (allVars P)

theorem dg_iff_flow (P : Program) (h : Node → Vars) :
    DemoGate P h ↔ MTCSpecB P (listVar P) (dgT P) (condVars P) (∅) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hs.predict c c' hstep x hx
    · intro n x hx; exact hs.check n x hx
    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · rintro ⟨hp, hcl, hseed, hbound⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hp c c' hstep x hx
    · intro n x hx; exact hcl n x hx
    · intro c hhalt x hx; exact hseed c hhalt x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem dgSol_valid (P : Program) (wf : WellFormed P) : DemoGate P (dgSol P) :=
  (dg_iff_flow P _).mpr (dg_correct P wf).1
theorem dg_least (P : Program) (wf : WellFormed P) :
    ∀ g, DemoGate P g → ∀ n, (dgSol P n).Subset (g n) :=
  fun g hg n x hx => (dg_correct P wf).2 g ((dg_iff_flow P g).mp hg) n x hx

#assert_clean_axioms dgSol_valid
#assert_clean_axioms dg_least

end BaseLanguage.Analyses.DemoGate
