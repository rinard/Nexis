-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdChain.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdchain.BwdChainDefs
import analyses.bwdchain.BwdChainDefsSub
import Generated.Solver.bwdchain.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdChain
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure BwdChain (P : Program) (g : Node → Defs) : Prop where
  predict : ∀ c c', Step P c c' → (g c.node).Subset (((((genDefs P c.node).union ((((g c'.node)).filter (fun y => (transpDefs P c.node).contains y))))).union (extraN P c.node)))
  check : ∀ n, (g n).Subset (ceilN P n)
  seed    : ∀ c, Final P c → (g c.node).Subset (∅)
  within : ∀ n, (g n).Subset (allDefs P)

theorem g_iff_flow (P : Program) (h : Node → Defs) :
    BwdChain P h ↔ MTCSpecBM P (listNode P) (gT P) (gHi P) (∅) h := by
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

theorem gSol_valid (P : Program) (wf : WellFormed P) : BwdChain P (gSol P) :=
  (g_iff_flow P _).mpr (g_correct P wf).1
theorem g_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, BwdChain P g → ∀ n, (g n).Subset (gSol P n) :=
  fun g hg n x hx => (g_correct P wf).2 g ((g_iff_flow P g).mp hg) n x hx

#assert_clean_axioms gSol_valid
#assert_clean_axioms g_greatest

end BaseLanguage.Analyses.BwdChain
