-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdmay.BwdMayDefs
import analyses.bwdmay.BwdMayDefsSub
import Generated.Solver.bwdmay.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure BwdMay (P : Program) (m : Node → Defs) : Prop where
  predict : ∀ c c', Step P c c' → Defs.Subset (((((genDefs P c.node).union ((((m c'.node)).filter (fun y => (transpDefs P c.node).contains y))))).union (extraM P c.node))) (m c.node)
  check   : ∀ n, (floorM P n).Subset (m n)
  seed    : ∀ c, Final P c → Defs.Subset (∅) (m c.node)
  within : ∀ n, (m n).Subset (allDefs P)

theorem m_iff_flow (P : Program) (h : Node → Defs) :
    BwdMay P h ↔ MTCSpecB P (listNode P) (mT P) (floorM P) (∅) h := by
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

theorem mSol_valid (P : Program) (wf : WellFormed P) : BwdMay P (mSol P) :=
  (m_iff_flow P _).mpr (m_correct P wf).1
theorem m_least (P : Program) (wf : WellFormed P) :
    ∀ g, BwdMay P g → ∀ n, (mSol P n).Subset (g n) :=
  fun g hg n x hx => (m_correct P wf).2 g ((m_iff_flow P g).mp hg) n x hx

#assert_clean_axioms mSol_valid
#assert_clean_axioms m_least

end BaseLanguage.Analyses.BwdMay
