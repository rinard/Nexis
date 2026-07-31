-- Copyright (c) 2026 Martin Rinard
-- GENERATED from Live.gsl by `lake exe gen` — do not edit.
import analyses.live.LiveDefs
import analyses.live.LiveDefsSub
import Generated.Solver.live.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.Live
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Live (P : Program) (live : Node → Vars) : Prop where
  predict : ∀ c c', Step P c c' → (live c'.node).Subset ((live c.node).union (defVars P c.node))
  check   : ∀ n, (condVars P n).Subset (live n)
  gate    : ∀ c c', Step P c c' → (∃ x ∈ defVars P c.node, x ∈ live c'.node) → (rhsVars P c.node).Subset (live c.node)
  seed    : ∀ c, Final P c → Vars.Subset (liveSeed P) (live c.node)
  within : ∀ n, (live n).Subset (allVars P)

theorem live_iff_flow (P : Program) (h : Node → Vars) :
    Live P h ↔ MTCSpecB P (listVar P) (liveT P) (condVars P) (liveSeed P) h := by
  constructor
  · intro hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      rcases Vars.mem_union.mp hx with hg | hdf
      · simp only [MTC.evs] at hg
        by_cases hguard : (h c'.node).toList.any (fun y => (defVars P c.node).contains y) = true
        · rw [if_pos hguard] at hg
          obtain ⟨y, hyl, hyc⟩ := List.any_eq_true.mp hguard
          exact hl.gate c c' hstep ⟨y, Std.HashSet.contains_iff_mem.mp hyc, Std.HashSet.mem_toList.mp hyl⟩ x hg
        · rw [if_neg hguard] at hg; simp [Vars.empty] at hg
      · simp only [MTC.evs] at hdf
        rw [Analysis.SetOps.mem_filter'] at hdf
        obtain ⟨hxin, hxnd⟩ := hdf
        rcases Vars.mem_union.mp (hl.predict c c' hstep x hxin) with hh | hd
        · exact hh
        · have hc : (defVars P c.node).contains x = true := Std.HashSet.contains_iff_mem.mpr hd
          rw [hc] at hxnd; simp at hxnd
    · intro n x hx; exact hl.check n x hx
    · intro c hhalt x hx; exact hl.seed c hhalt x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hl.within n x hx)
  · rintro ⟨hupd, hcheck, hseed, hbound⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      by_cases hxd : x ∈ defVars P c.node
      · exact Vars.mem_union.mpr (Or.inr hxd)
      · refine Vars.mem_union.mpr (Or.inl (hupd c c' hstep x ?_))
        refine Vars.mem_union.mpr (Or.inr ?_)
        show x ∈ (h c'.node).filter _
        rw [Analysis.SetOps.mem_filter']
        refine ⟨hx, ?_⟩
        cases hc : (defVars P c.node).contains x with
        | false => rfl
        | true => exact absurd (Std.HashSet.contains_iff_mem.mp hc) hxd
    · intro n x hx; exact hcheck n x hx
    · intro c c' hstep hmeets x hx
      apply hupd c c' hstep x
      refine Vars.mem_union.mpr (Or.inl ?_)
      obtain ⟨w, hwdef, hwlive⟩ := hmeets
      have hguard : (h c'.node).toList.any (fun y => (defVars P c.node).contains y) = true :=
        List.any_eq_true.mpr ⟨w, Std.HashSet.mem_toList.mpr hwlive, Std.HashSet.contains_iff_mem.mpr hwdef⟩
      simp only [MTC.evs]; rw [if_pos hguard]; exact hx
    · intro c hf x hx; exact hseed c hf x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem liveSol_valid (P : Program) (wf : WellFormed P) : Live P (liveSol P) :=
  (live_iff_flow P _).mpr (live_correct P wf).1
theorem live_least (P : Program) (wf : WellFormed P) :
    ∀ g, Live P g → ∀ n, (liveSol P n).Subset (g n) :=
  fun g hg n x hx => (live_correct P wf).2 g ((live_iff_flow P g).mp hg) n x hx

#assert_clean_axioms liveSol_valid
#assert_clean_axioms live_least

end BaseLanguage.Analyses.Live
