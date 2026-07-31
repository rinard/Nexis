-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdSlice.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdslice.BwdSliceDefs
import analyses.bwdslice.BwdSliceDefsSub
import Generated.Solver.bwdslice.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.BwdSlice
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure BwdSlice (P : Program) (slice : Node → Vars) : Prop where
  predict : ∀ c c', Step P c c' → Vars.Subset ((((MTC.imageS (allVars P) (flowsBack P c.node) (slice c'.node))).union ((((slice c'.node)).filter (fun y => !(definedVars P c.node).contains y))))) (slice c.node)
  check   : ∀ n, (crit P n).Subset (slice n)
  seed    : ∀ c, Final P c → Vars.Subset (∅) (slice c.node)
  within : ∀ n, (slice n).Subset (allVars P)

theorem slice_iff_flow (P : Program) (h : Node → Vars) :
    BwdSlice P h ↔ MTCSpecB P (listVar P) (sliceT P) (crit P) (∅) h := by
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

theorem sliceSol_valid (P : Program) (wf : WellFormed P) : BwdSlice P (sliceSol P) :=
  (slice_iff_flow P _).mpr (slice_correct P wf).1
theorem slice_least (P : Program) (wf : WellFormed P) :
    ∀ g, BwdSlice P g → ∀ n, (sliceSol P n).Subset (g n) :=
  fun g hg n x hx => (slice_correct P wf).2 g ((slice_iff_flow P g).mp hg) n x hx

#assert_clean_axioms sliceSol_valid
#assert_clean_axioms slice_least

end BaseLanguage.Analyses.BwdSlice
