-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PDCEFault.gsl by `lake exe gen` — do not edit.
import analyses.pdcefault.PdceFaultDefs
import analyses.pdcefault.PdceFaultDefsSub
import Generated.Solver.pdcefault.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PDCEFault
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Live (P : Program) (π : Node → Variables) : Prop where
  predict : ∀ c c', Step P c c' → (π c'.node).Subset ((π c.node).union (defVars P c.node))
  check   : ∀ n, (liveFloorF P n).Subset (π n)
  gate    : ∀ c c', Step P c c' → (∃ x ∈ defVars P c.node, x ∈ π c'.node) → (rhsVars P c.node).Subset (π c.node)
  seed    : ∀ c, Final P c → Variables.Subset (liveSeed P) (π c.node)
  within : ∀ n, (π n).Subset (allVars P)

structure Sink (P : Program) (η : Node → Assignments) : Prop where
  update : ∀ c c', Step P c c' → (η c'.node).Subset ((born P c.node).union ((η c.node).inter (pass P c.node)))
  seed   : (η P.entry).Subset (sinkSeed P)
  within : ∀ n, (η n).Subset (allAsgns P)

theorem π_iff_flow (P : Program) (h : Node → Variables) :
    Live P h ↔ MTCSpecB P (listVar P) (πT P) (liveFloorF P) (liveSeed P) h := by
  constructor
  · intro hl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      rcases Variables.mem_union.mp hx with hg | hdf
      · simp only [MTC.evs] at hg
        by_cases hguard : (h c'.node).toList.any (fun y => (defVars P c.node).contains y) = true
        · rw [if_pos hguard] at hg
          obtain ⟨y, hyl, hyc⟩ := List.any_eq_true.mp hguard
          exact hl.gate c c' hstep ⟨y, Std.HashSet.contains_iff_mem.mp hyc, Std.HashSet.mem_toList.mp hyl⟩ x hg
        · rw [if_neg hguard] at hg; simp [Variables.empty] at hg
      · simp only [MTC.evs] at hdf
        rw [Analysis.SetOps.mem_filter'] at hdf
        obtain ⟨hxin, hxnd⟩ := hdf
        rcases Variables.mem_union.mp (hl.predict c c' hstep x hxin) with hh | hd
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
      · exact Variables.mem_union.mpr (Or.inr hxd)
      · refine Variables.mem_union.mpr (Or.inl (hupd c c' hstep x ?_))
        refine Variables.mem_union.mpr (Or.inr ?_)
        show x ∈ (h c'.node).filter _
        rw [Analysis.SetOps.mem_filter']
        refine ⟨hx, ?_⟩
        cases hc : (defVars P c.node).contains x with
        | false => rfl
        | true => exact absurd (Std.HashSet.contains_iff_mem.mp hc) hxd
    · intro n x hx; exact hcheck n x hx
    · intro c c' hstep hmeets x hx
      apply hupd c c' hstep x
      refine Variables.mem_union.mpr (Or.inl ?_)
      obtain ⟨w, hwdef, hwlive⟩ := hmeets
      have hguard : (h c'.node).toList.any (fun y => (defVars P c.node).contains y) = true :=
        List.any_eq_true.mpr ⟨w, Std.HashSet.mem_toList.mpr hwlive, Std.HashSet.contains_iff_mem.mpr hwdef⟩
      simp only [MTC.evs]; rw [if_pos hguard]; exact hx
    · intro c hf x hx; exact hseed c hf x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem πSol_valid (P : Program) (wf : WellFormed P) : Live P (πSol P) :=
  (π_iff_flow P _).mpr (π_correct P wf).1
theorem π_least (P : Program) (wf : WellFormed P) :
    ∀ g, Live P g → ∀ n, (πSol P n).Subset (g n) :=
  fun g hg n x hx => (π_correct P wf).2 g ((π_iff_flow P g).mp hg) n x hx

#assert_clean_axioms πSol_valid
#assert_clean_axioms π_least

theorem η_iff_flow (P : Program) (h : Node → Assignments) :
    Sink P h ↔ MTCSpec P (listAsgn P) (ηT P) (sinkSeed P) h := by
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

theorem ηSol_valid (P : Program) (wf : WellFormed P) : Sink P (ηSol P) :=
  (η_iff_flow P _).mpr (η_correct P wf).1
theorem η_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Sink P g → ∀ n, (g n).Subset (ηSol P n) :=
  fun g hg n x hx => (η_correct P wf).2 g ((η_iff_flow P g).mp hg) n x hx

#assert_clean_axioms ηSol_valid
#assert_clean_axioms η_greatest

/-! ## The uniform analysis interface: `PDCEFaultResult` + `Valid`/`Extremal` + `PDCEFaultSolve`. -/

structure PDCEFaultResult (P : Program) where
  π : Node → Variables
  η : Node → Assignments

def PDCEFaultResult.Valid (P : Program) (S : PDCEFaultResult P) : Prop :=
  (Live P S.π) ∧ (Sink P S.η)

def PDCEFaultResult.Extremal (P : Program) (S : PDCEFaultResult P) : Prop :=
  (∀ g, Live P g → ∀ n, (S.π n).Subset (g n)) ∧ (∀ g, Sink P g → ∀ n, (g n).Subset (S.η n))

def PDCEFaultSolve (P : Program) (wf : WellFormed P) : PDCEFaultResult P where
  π := πSol P
  η := ηSol P

theorem PDCEFaultSolve_valid (P : Program) (wf : WellFormed P) : (PDCEFaultSolve P wf).Valid P :=
  ⟨πSol_valid P wf, ηSol_valid P wf⟩

theorem PDCEFaultSolve_extremal (P : Program) (wf : WellFormed P) : (PDCEFaultSolve P wf).Extremal P :=
  ⟨π_least P wf, η_greatest P wf⟩

#assert_clean_axioms PDCEFaultSolve_valid
#assert_clean_axioms PDCEFaultSolve_extremal

end BaseLanguage.Analyses.PDCEFault
