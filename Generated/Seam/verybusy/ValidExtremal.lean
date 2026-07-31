-- Copyright (c) 2026 Martin Rinard
-- GENERATED from VeryBusy.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.verybusy.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.VeryBusy
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure VeryBusy (P : Program) (busy : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ((busy c.node).sdiff (genExprs P c.node)).Subset (busy c'.node)
  check : ∀ n, (busy n).Subset ((genExprs P n).union (transpExprs P n))
  seed    : ∀ c, Final P c → (busy c.node).Subset (∅)
  within : ∀ n, (busy n).Subset (allExprs P)

theorem busy_iff_flow (P : Program) (h : Node → Exprs) :
    VeryBusy P h ↔ MTCSpecBM P (listExpr P) (busyT P) (busyHi P) (∅) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      by_cases hue : x ∈ genExprs P c.node
      · exact Exprs.mem_union.mpr (Or.inl hue)
      · refine Exprs.mem_union.mpr (Or.inr ?_)
        refine Exprs.mem_inter.mpr ⟨hs.predict c c' hstep x (Exprs.mem_sdiff.mpr ⟨hx, hue⟩), ?_⟩
        rcases Exprs.mem_union.mp (hs.check c.node x hx) with h1 | h2
        · exact absurd h1 hue
        · exact h2
    · intro n x hx; exact hs.check n x hx
    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · rintro ⟨hupd, hcheck, hseed, hbound⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      obtain ⟨hxin, hxnue⟩ := Exprs.mem_sdiff.mp hx
      rcases Exprs.mem_union.mp (hupd c c' hstep x hxin) with hue | hi
      · exact absurd hue hxnue
      · exact (Exprs.mem_inter.mp hi).1
    · intro n x hx; exact hcheck n x hx
    · intro c hhalt x hx; exact hseed c hhalt x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem busySol_valid (P : Program) (wf : WellFormed P) : VeryBusy P (busySol P) :=
  (busy_iff_flow P _).mpr (busy_correct P wf).1
theorem busy_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, VeryBusy P g → ∀ n, (g n).Subset (busySol P n) :=
  fun g hg n x hx => (busy_correct P wf).2 g ((busy_iff_flow P g).mp hg) n x hx

#assert_clean_axioms busySol_valid
#assert_clean_axioms busy_greatest

end BaseLanguage.Analyses.VeryBusy
