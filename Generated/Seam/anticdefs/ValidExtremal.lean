-- Copyright (c) 2026 Martin Rinard
-- GENERATED from AnticDefs.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.anticdefs.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.AnticDefs
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure AnticDefs (P : Program) (antic : Node → Defs) : Prop where
  predict : ∀ c c', Step P c c' → ((antic c.node).sdiff (genDefs P c.node)).Subset (antic c'.node)
  check : ∀ n, (antic n).Subset ((genDefs P n).union (transpDefs P n))
  seed    : ∀ c, Final P c → (antic c.node).Subset (∅)
  within : ∀ n, (antic n).Subset (allDefs P)

theorem antic_iff_flow (P : Program) (h : Node → Defs) :
    AnticDefs P h ↔ MTCSpecBM P (listNode P) (anticT P) (anticHi P) (∅) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      by_cases hue : x ∈ genDefs P c.node
      · exact Defs.mem_union.mpr (Or.inl hue)
      · refine Defs.mem_union.mpr (Or.inr ?_)
        refine Defs.mem_inter.mpr ⟨hs.predict c c' hstep x (Defs.mem_sdiff.mpr ⟨hx, hue⟩), ?_⟩
        rcases Defs.mem_union.mp (hs.check c.node x hx) with h1 | h2
        · exact absurd h1 hue
        · exact h2
    · intro n x hx; exact hs.check n x hx
    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · rintro ⟨hupd, hcheck, hseed, hbound⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      obtain ⟨hxin, hxnue⟩ := Defs.mem_sdiff.mp hx
      rcases Defs.mem_union.mp (hupd c c' hstep x hxin) with hue | hi
      · exact absurd hue hxnue
      · exact (Defs.mem_inter.mp hi).1
    · intro n x hx; exact hcheck n x hx
    · intro c hhalt x hx; exact hseed c hhalt x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem anticSol_valid (P : Program) (wf : WellFormed P) : AnticDefs P (anticSol P) :=
  (antic_iff_flow P _).mpr (antic_correct P wf).1
theorem antic_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, AnticDefs P g → ∀ n, (g n).Subset (anticSol P n) :=
  fun g hg n x hx => (antic_correct P wf).2 g ((antic_iff_flow P g).mp hg) n x hx

#assert_clean_axioms anticSol_valid
#assert_clean_axioms antic_greatest

end BaseLanguage.Analyses.AnticDefs
