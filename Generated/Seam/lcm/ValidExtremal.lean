-- Copyright (c) 2026 Martin Rinard
-- GENERATED from LCM.gsl by `lake exe gen` — do not edit.
import analyses.lcm.LcmDefs
import analyses.lcm.LcmDefsSub
import Generated.Solver.lcm.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.LCM
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure Anticipated (P : Program) (πₐ : Node → Assignments) : Prop where
  predict : ∀ c c', Step P c c' → ((πₐ c.node).sdiff (ue P c.node)).Subset (πₐ c'.node)
  check : ∀ n, (πₐ n).Subset ((ue P n).union (pass P n))
  seed    : ∀ c, Final P c → (πₐ c.node).Subset (haltSeed P)
  within : ∀ n, (πₐ n).Subset (allExprs P)

structure Available (P : Program) (ηₐ : Node → Assignments) : Prop where
  update : ∀ c c', Step P c c' → (ηₐ c'.node).Subset ((de P c.node).union ((ηₐ c.node).inter (pass P c.node)))
  seed   : (ηₐ P.entry).Subset (entrySeed P)
  within : ∀ n, (ηₐ n).Subset (allExprs P)

structure Postponable (P : Program) (πₐ ηₐ : Node → Assignments) (ηₚ : Node → Assignments) : Prop where
  update : ∀ c c', Step P c c' → (ηₚ c'.node).Subset ((earliest P πₐ ηₐ c.node c'.node).union ((ηₚ c.node).sdiff (ue P c.node)))
  seed   : (ηₚ P.entry).Subset (entrySeed P)
  within : ∀ n, (ηₚ n).Subset (allExprs P)

structure Used (P : Program) (latN : Node → Assignments) (latE : Node → Node → Assignments) (πᵤ : Node → Assignments) : Prop where
  predict : ∀ c c', Step P c c' → (πᵤ c'.node).Subset ((πᵤ c.node).union ((latN c'.node).union (latE c.node c'.node)))
  check   : ∀ n, ((ue P n).sdiff (latN n)).Subset (πᵤ n)
  within : ∀ n, (πᵤ n).Subset (allExprs P)

theorem πₐ_iff_flow (P : Program) (h : Node → Assignments) :
    Anticipated P h ↔ MTCSpecBM P (listExpr P) (πₐT P) (πₐHi P) (haltSeed P) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      by_cases hue : x ∈ ue P c.node
      · exact Assignments.mem_union.mpr (Or.inl hue)
      · refine Assignments.mem_union.mpr (Or.inr ?_)
        refine Assignments.mem_inter.mpr ⟨hs.predict c c' hstep x (Assignments.mem_sdiff.mpr ⟨hx, hue⟩), ?_⟩
        rcases Assignments.mem_union.mp (hs.check c.node x hx) with h1 | h2
        · exact absurd h1 hue
        · exact h2
    · intro n x hx; exact hs.check n x hx
    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · rintro ⟨hupd, hcheck, hseed, hbound⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep x hx
      obtain ⟨hxin, hxnue⟩ := Assignments.mem_sdiff.mp hx
      rcases Assignments.mem_union.mp (hupd c c' hstep x hxin) with hue | hi
      · exact absurd hue hxnue
      · exact (Assignments.mem_inter.mp hi).1
    · intro n x hx; exact hcheck n x hx
    · intro c hhalt x hx; exact hseed c hhalt x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)

theorem πₐSol_valid (P : Program) (wf : WellFormed P) : Anticipated P (πₐSol P) :=
  (πₐ_iff_flow P _).mpr (πₐ_correct P wf).1
theorem πₐ_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Anticipated P g → ∀ n, (g n).Subset (πₐSol P n) :=
  fun g hg n x hx => (πₐ_correct P wf).2 g ((πₐ_iff_flow P g).mp hg) n x hx

#assert_clean_axioms πₐSol_valid
#assert_clean_axioms πₐ_greatest

theorem ηₐ_iff_flow (P : Program) (h : Node → Assignments) :
    Available P h ↔ MTCSpec P (listExpr P) (ηₐT P) (entrySeed P) h := by
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

theorem ηₐSol_valid (P : Program) (wf : WellFormed P) : Available P (ηₐSol P) :=
  (ηₐ_iff_flow P _).mpr (ηₐ_correct P wf).1
theorem ηₐ_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Available P g → ∀ n, (g n).Subset (ηₐSol P n) :=
  fun g hg n x hx => (ηₐ_correct P wf).2 g ((ηₐ_iff_flow P g).mp hg) n x hx

#assert_clean_axioms ηₐSol_valid
#assert_clean_axioms ηₐ_greatest

theorem ηₚ_toSpec (P : Program) (πₐ ηₐ h : Node → Assignments) (hs : Postponable P πₐ ηₐ h) :
    MTCSpec P (listExpr P) (ηₚT P πₐ ηₐ) (entrySeed P) h :=
  ⟨fun c c' hstep x hx => hs.update c c' hstep x hx, fun x hx => hs.seed x hx,
   fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
theorem ηₚ_ofSpec (P : Program) (πₐ ηₐ h : Node → Assignments) (hf : MTCSpec P (listExpr P) (ηₚT P πₐ ηₐ) (entrySeed P) h) : Postponable P πₐ ηₐ h :=
  ⟨fun c c' hstep x hx => hf.1 c c' hstep x hx, fun x hx => hf.2.1 x hx,
   fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2 n x hx)⟩
theorem ηₚSol_valid (P : Program) (wf : WellFormed P) : Postponable P (πₐSol P) (ηₐSol P) (ηₚSol P) :=
  ηₚ_ofSpec P _ _ _ (ηₚ_correct P wf).1
theorem ηₚ_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Postponable P (πₐSol P) (ηₐSol P) g → ∀ n, (g n).Subset (ηₚSol P n) :=
  fun g hg n x hx => (ηₚ_correct P wf).2 g (ηₚ_toSpec P _ _ _ hg) n x hx

#assert_clean_axioms ηₚSol_valid
#assert_clean_axioms ηₚ_greatest

theorem τₚ_iff_spec (P : Program) (X : Node → BVExpr P) (τ : Node → Assignments) :
    Transfer Assignments.Subset P (decFExpr P X) τ ↔ MeetSpec P (listExpr P) X τ := by
  constructor
  · intro ht
    exact ⟨fun c c' hs x hx => ht.predict c c' hs x hx,
           fun n x hx => Std.HashSet.mem_toList.mpr (ht.within n x hx)⟩
  · rintro ⟨htr, hb⟩
    exact ⟨fun c c' hs x hx => htr c c' hs x hx,
           fun n x hx => Std.HashSet.mem_toList.mp (hb n x hx)⟩
theorem τₚSol_valid (P : Program) (wf : WellFormed P) : Transfer Assignments.Subset P (ηₚSol P) (τₚSol P) :=
  (τₚ_iff_spec P ((solve P).ηₚ) _).mpr (τₚ_correct P wf).1
theorem τₚ_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Transfer Assignments.Subset P (ηₚSol P) g → ∀ n, (g n).Subset (τₚSol P n) :=
  fun g hg n x hx => (τₚ_correct P wf).2 g ((τₚ_iff_spec P ((solve P).ηₚ) g).mp hg) n x hx

#assert_clean_axioms τₚSol_valid
#assert_clean_axioms τₚ_greatest

theorem πᵤ_toSpec (P : Program) (latN : Node → Assignments) (latE : Node → Node → Assignments) (h : Node → Assignments) (hs : Used P latN latE h) : MTCSpecB P (listExpr P) (πᵤT P latN latE) (πᵤLo P latN) ∅ h := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' hstep x hx
    rw [show MTC.evs (c.node, c'.node) (πᵤT P latN latE) (h c'.node)
          = (h c'.node).filter (fun y => !((latN c'.node).union (latE c.node c'.node)).contains y) from rfl] at hx
    rw [SetOps.mem_filter'] at hx
    obtain ⟨hxin, hxnk⟩ := hx
    rcases Assignments.mem_union.mp (hs.predict c c' hstep x hxin) with hu | hk
    · exact hu
    · exfalso
      have : ((latN c'.node).union (latE c.node c'.node)).contains x = true := Std.HashSet.contains_iff_mem.mpr hk
      rw [this] at hxnk; simp at hxnk
  · intro n x hx; exact hs.check n x hx
  · intro c hhalt x hx; exact absurd hx Std.HashSet.not_mem_empty
  · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
theorem πᵤ_ofSpec (P : Program) (latN : Node → Assignments) (latE : Node → Node → Assignments) (h : Node → Assignments) (hf : MTCSpecB P (listExpr P) (πᵤT P latN latE) (πᵤLo P latN) ∅ h) : Used P latN latE h := by
  obtain ⟨hupd, hcheck, hseed, hbound⟩ := hf
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hstep x hx
    by_cases hk : x ∈ (latN c'.node).union (latE c.node c'.node)
    · exact Assignments.mem_union.mpr (Or.inr hk)
    · refine Assignments.mem_union.mpr (Or.inl (hupd c c' hstep x ?_))
      rw [show MTC.evs (c.node, c'.node) (πᵤT P latN latE) (h c'.node)
            = (h c'.node).filter (fun y => !((latN c'.node).union (latE c.node c'.node)).contains y) from rfl]
      rw [SetOps.mem_filter']
      refine ⟨hx, ?_⟩
      cases hc : ((latN c'.node).union (latE c.node c'.node)).contains x with
      | false => rfl
      | true => exact absurd (Std.HashSet.contains_iff_mem.mp hc) hk
  · intro n x hx; exact hcheck n x hx
  · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)
theorem πᵤSol_valid (P : Program) (wf : WellFormed P) : Used P (πᵤLatN P) (πᵤLatE P) (πᵤSol P) :=
  πᵤ_ofSpec P _ _ _ (πᵤ_correct P wf).1
theorem πᵤ_least (P : Program) (wf : WellFormed P) :
    ∀ g, Used P (πᵤLatN P) (πᵤLatE P) g → ∀ n, (πᵤSol P n).Subset (g n) :=
  fun g hg n x hx => (πᵤ_correct P wf).2 g (πᵤ_toSpec P _ _ _ hg) n x hx

#assert_clean_axioms πᵤSol_valid
#assert_clean_axioms πᵤ_least

theorem τᵤ_iff_spec (P : Program) (X : Node → BVExpr P) (τ : Node → Assignments) :
    Transfer Assignments.Sup P (decFExpr P X) τ ↔ JoinSpec P (listExpr P) X τ := by
  constructor
  · intro ht
    exact ⟨fun c c' hs x hx => ht.predict c c' hs x hx,
           fun n x hx => Std.HashSet.mem_toList.mpr (ht.within n x hx)⟩
  · rintro ⟨htr, hb⟩
    exact ⟨fun c c' hs x hx => htr c c' hs x hx,
           fun n x hx => Std.HashSet.mem_toList.mp (hb n x hx)⟩
theorem τᵤSol_valid (P : Program) (wf : WellFormed P) : Transfer Assignments.Sup P (πᵤSol P) (τᵤSol P) :=
  (τᵤ_iff_spec P ((solve P).πᵤ) _).mpr (τᵤ_correct P wf).1
theorem τᵤ_least (P : Program) (wf : WellFormed P) :
    ∀ g, Transfer Assignments.Sup P (πᵤSol P) g → ∀ n, (τᵤSol P n).Subset (g n) :=
  fun g hg n x hx => (τᵤ_correct P wf).2 g ((τᵤ_iff_spec P ((solve P).πᵤ) g).mp hg) n x hx

#assert_clean_axioms τᵤSol_valid
#assert_clean_axioms τᵤ_least

/-! ## The uniform analysis interface: `LCMResult` + `Valid`/`Extremal` + `LCMSolve`. -/

structure LCMResult (P : Program) where
  πₐ : Node → Assignments
  ηₐ : Node → Assignments
  ηₚ : Node → Assignments
  τₚ : Node → Assignments
  πᵤ : Node → Assignments
  τᵤ : Node → Assignments

def LCMResult.Valid (P : Program) (S : LCMResult P) : Prop :=
  (Anticipated P S.πₐ) ∧ (Available P S.ηₐ) ∧ (Postponable P S.πₐ S.ηₐ S.ηₚ) ∧ (Transfer Assignments.Subset P S.ηₚ S.τₚ) ∧ (Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ) S.πᵤ) ∧ (Transfer Assignments.Sup P S.πᵤ S.τᵤ)

def LCMResult.Extremal (P : Program) (S : LCMResult P) : Prop :=
  (∀ g, Anticipated P g → ∀ n, (g n).Subset (S.πₐ n)) ∧ (∀ g, Available P g → ∀ n, (g n).Subset (S.ηₐ n)) ∧ (∀ g, Postponable P S.πₐ S.ηₐ g → ∀ n, (g n).Subset (S.ηₚ n)) ∧ (∀ g, Transfer Assignments.Subset P S.ηₚ g → ∀ n, (g n).Subset (S.τₚ n)) ∧ (∀ g, Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ) g → ∀ n, (S.πᵤ n).Subset (g n)) ∧ (∀ g, Transfer Assignments.Sup P S.πᵤ g → ∀ n, (S.τᵤ n).Subset (g n))

def LCMSolve (P : Program) (wf : WellFormed P) : LCMResult P where
  πₐ := πₐSol P
  ηₐ := ηₐSol P
  ηₚ := ηₚSol P
  τₚ := τₚSol P
  πᵤ := πᵤSol P
  τᵤ := τᵤSol P

theorem LCMSolve_valid (P : Program) (wf : WellFormed P) : (LCMSolve P wf).Valid P :=
  ⟨πₐSol_valid P wf, ηₐSol_valid P wf, ηₚSol_valid P wf, τₚSol_valid P wf, πᵤSol_valid P wf, τᵤSol_valid P wf⟩

theorem LCMSolve_extremal (P : Program) (wf : WellFormed P) : (LCMSolve P wf).Extremal P :=
  ⟨πₐ_greatest P wf, ηₐ_greatest P wf, ηₚ_greatest P wf, τₚ_greatest P wf, πᵤ_least P wf, τᵤ_least P wf⟩

#assert_clean_axioms LCMSolve_valid
#assert_clean_axioms LCMSolve_extremal

end BaseLanguage.Analyses.LCM
