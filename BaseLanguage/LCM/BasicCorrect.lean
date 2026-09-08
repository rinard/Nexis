-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.BasicCov

/-!
# `BasicCorrect` — halt + fault preservation for the *basic* LCM transform (isolated insertions permitted)

The basic transform is `transform P (mkBasic S)` where `mkBasic S` sets `πᵤ = τᵤ = allExprs`
(so it inserts at every latest node/edge and replaces every numbered computation). We prove
`transform_preserves_halt_basic` and `transform_preserves_faulting_basic` by reusing
`match_step_assign` (read-justification parametrized) with `replace_covered_basic`, threading the
*reference* extremal `S`'s `Cov` for coverage (maintained via `Cov_step_edge` + monotonicity, since the
basic materialized set dominates the optimal one).
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

variable {P : Program}

/-! ## The `allExprs`-topped bundle -/

/-- `mkBasic S` — `S` with `used`/`usedOut` widened to the whole universe (the basic transform's bundle). -/
def mkBasic (S : LcmSpec P) : LcmSpec P :=
  { S with
    πᵤ := fun _ => allExprs P
    τᵤ := fun _ => allExprs P
    isUsed := by
      refine ⟨?_, ?_, ?_⟩
      · intro c c' _ e he; exact Assignments.mem_union.mpr (Or.inl he)
      · intro n e he; exact ue_mem_allExprs (Assignments.mem_sdiff.mp he).1
      · intro n e he; exact he
    isUsedOut := by
      refine ⟨?_, ?_⟩
      · intro c c' _ e he; exact he
      · intro n e he; exact he }

@[simp] theorem mkBasic_postp (S : LcmSpec P) : (mkBasic S).ηₚ = S.ηₚ := rfl
@[simp] theorem mkBasic_tauP (S : LcmSpec P) : (mkBasic S).τₚ = S.τₚ := rfl
@[simp] theorem mkBasic_anti (S : LcmSpec P) : (mkBasic S).πₐ = S.πₐ := rfl
@[simp] theorem mkBasic_avail (S : LcmSpec P) : (mkBasic S).ηₐ = S.ηₐ := rfl
@[simp] theorem mkBasic_usedOut (S : LcmSpec P) (n : Node) : (mkBasic S).τᵤ n = allExprs P := rfl
@[simp] theorem mkBasic_keep (S : LcmSpec P) : (mkBasic S).keep = S.keep := rfl
/-- The basic variant keeps everything, so its filtered gate is just the universe. -/
theorem mkBasic_mem_τᵤK (S : LcmSpec P) (n : Node) {e : Expr} (hk : S.keep e = true)
    (h : e ∈ allExprs P) : e ∈ (mkBasic S).τᵤK n :=
  Analysis.SetOps.mem_filter'.mpr ⟨h, hk⟩

/-! ## `insBefore' = insertBefore (mkBasic S)`, and coverage read-off for the basic gate -/

theorem insertBefore_mkBasic (S : LcmSpec P) (n : Node) {e : Expr}
    (he : e ∈ insBefore' S n) : e ∈ insertBefore P (mkBasic S) n := by
  unfold insertBefore
  rw [Assignments.mem_inter]
  have hk : S.keep e = true := (Analysis.SetOps.mem_filter'.mp he).2
  have he' : e ∈ Assignments.sdiff (latestNode P S.ηₚ S.τₚ n) (latestOut P S n) :=
    (Analysis.SetOps.mem_filter'.mp he).1
  refine ⟨he', ?_⟩
  -- (mkBasic S).τᵤ n = allExprs, and insBefore' ⊆ latestNode ⊆ postp ⊆ allExprs
  exact mkBasic_mem_τᵤK S n hk
    (S.isPostp.within n e (latestNode_sub_postp S n e (Assignments.mem_sdiff.mp he').1))

/-- Read-justification for the basic gate: at a numbered assignment the temp is materialized before the
    control. Built from `replace_covered_basic` (from the reference `S`'s `Cov` via `cov_implies_cov_basic`). -/
theorem hcovered_basic (S : LcmSpec P) {nd : Node} {x : Var} {e0 : Expr} {next : Node} {M : Assignments}
    (hf : P.fetch nd = some (.assign x e0 next)) (wn : WellNormalized P) (hcov : Cov S nd M)
    (hg : (isNumbered e0 && (recoverable P (mkBasic S) nd).contains e0) = true) :
    e0 ∈ M ∨ e0 ∈ insertBefore P (mkBasic S) nd := by
  have hg' : isNumbered e0 = true ∧ (recoverable P (mkBasic S) nd).contains e0 = true := by
    simpa using hg
  have hnum : isNumbered e0 = true := hg'.1
  have hkeep : (mkBasic S).keep e0 = true :=
    recoverable_keep (Std.HashSet.contains_iff_mem.mp hg'.2)
  have hbasic := replace_covered_basic (mkBasic S) hf hnum hkeep (wn.noSelfRead hf hnum)
    (cov_implies_cov_basic S hcov)
  exact hbasic.imp id (fun h => insertBefore_mkBasic S nd h)

/-! ## Materialized-set monotonicity: optimal ⊆ basic (`Mstep_edge S ⊆ Mstep_edge (mkBasic S)`) -/

theorem insertBefore_sub_mkBasic (S : LcmSpec P) (n : Node) :
    Assignments.Subset (insertBefore P S n) (insertBefore P (mkBasic S) n) :=
  fun e he => insertBefore_mkBasic S n (insertBefore_sub_insBefore' S n e he)

theorem insertAfter_sub_mkBasic (S : LcmSpec P) (i : Node) :
    Assignments.Subset (insertAfter P S i) (insertAfter P (mkBasic S) i) := by
  intro e he
  unfold insertAfter at *
  cases hf : P.fetch i with
  | none => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty
  | some instr =>
    cases instr with
    | assign x ex next =>
        simp only [hf] at he ⊢; rw [Assignments.mem_inter] at he ⊢
        exact ⟨he.1, mkBasic_mem_τᵤK S i (mem_τᵤK.mp he.2).2 (S.isUsedOut.within i e (τᵤK_sub S i e he.2))⟩
    | noop next =>
        simp only [hf] at he ⊢; rw [Assignments.mem_inter] at he ⊢
        exact ⟨he.1, mkBasic_mem_τᵤK S i (mem_τᵤK.mp he.2).2 (S.isUsedOut.within i e (τᵤK_sub S i e he.2))⟩
    | ifz x z nz => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty
    | halt => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty

theorem insertEdge_sub_mkBasic (S : LcmSpec P) (i j : Node) :
    Assignments.Subset (insertEdge P S i j) (insertEdge P (mkBasic S) i j) := by
  intro e he
  unfold insertEdge at *
  rw [Assignments.mem_inter] at he ⊢
  exact ⟨he.1, mkBasic_mem_τᵤK S i (mem_τᵤK.mp he.2).2 (S.isUsedOut.within i e (τᵤK_sub S i e he.2))⟩

theorem Mstep_edge_sub_mkBasic (S : LcmSpec P) (c c' : Node) (M : Assignments) :
    Assignments.Subset (Mstep_edge S c c' M) (Mstep_edge (mkBasic S) c c' M) := by
  intro e he
  unfold Mstep_edge Mstep at *
  rw [Assignments.mem_union] at he ⊢
  rcases he with hms | hedge
  · left
    rw [Assignments.mem_union] at hms ⊢
    rcases hms with hbody | hafter
    · left
      rw [Assignments.mem_inter, Assignments.mem_union] at hbody ⊢
      refine ⟨?_, hbody.2⟩
      rcases hbody.1 with hM | hib
      · exact Or.inl hM
      · exact Or.inr (insertBefore_sub_mkBasic S c e hib)
    · right; exact insertAfter_sub_mkBasic S c e hafter
  · right; exact insertEdge_sub_mkBasic S c c' e hedge

/-! ## The basic step lemma, simulation, and halt preservation -/

/-- **`match_step_basic`** — the simulation step for the basic transform. Same shape as `match_step`, but the
    transform is `transform P (mkBasic S)`, the read-justification comes from `replace_covered_basic` (via
    `hcovered_basic`), and coverage `Cov S` (reference) is maintained by `Cov_step_edge` + monotonicity. -/
theorem match_step_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments} {c_f : Config}
    (hm : Match P (mkBasic S) c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c')
    (hcont : StepsH P c' c_f) (hfin : Final P c_f) :
    ∃ d', StepsPlus (transform P (mkBasic S)) d d'
        ∧ Match P (mkBasic S) c' d' (Mstep_edge (mkBasic S) c.node c'.node M)
        ∧ Cov S c'.node (Mstep_edge (mkBasic S) c.node c'.node M) := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  suffices h : ∃ d', StepsPlus (transform P (mkBasic S)) ⟨dn, dσ⟩ d'
      ∧ Match P (mkBasic S) c' d' (Mstep_edge (mkBasic S) c.node c'.node M) by
    obtain ⟨d', hsteps, hmatch⟩ := h
    exact ⟨d', hsteps, hmatch,
      cov_mono S (Cov_step_edge S hS wn hstep hcov) (Mstep_edge_sub_mkBasic S c.node c'.node M)⟩
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_assign (mkBasic S) wn hf hvv hagree hHolds hMsub hpa
      (fun hg => hcovered_basic S hf wn hcov hg)
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) (StepsH.head (Step.assign hf hvv) hcont) hfin e
          (insertBefore_sub_anti (mkBasic S) hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hanti : e ∈ (mkBasic S).πₐ next := by
          rw [Assignments.mem_toList] at he
          unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he
          exact edgeIns_sub_anti (mkBasic S) (Step.assign hf hvv) hpa he.1
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) hcont hfin e hanti; rw [hw]; exact Option.some_ne_none w)
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge (mkBasic S) (Or.inr ⟨x, e0, hf⟩)]; exact he)))⟩
  | @noop nd σ next hf =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_noop (mkBasic S) hf hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) (StepsH.head (Step.noop hf) hcont) hfin e
          (insertBefore_sub_anti (mkBasic S) hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hanti : e ∈ (mkBasic S).πₐ next := by
          rw [Assignments.mem_toList] at he
          unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he
          exact edgeIns_sub_anti (mkBasic S) (Step.noop (σ := σ) hf) hpa he.1
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) hcont hfin e hanti; rw [hw]; exact Option.some_ne_none w)
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge (mkBasic S) (Or.inl hf)]; exact he)))⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz (mkBasic S) hf (Or.inl ⟨hcond, rfl⟩) hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) (StepsH.head (Step.ifzT hf hcond) hcont) hfin e
          (insertBefore_sub_anti (mkBasic S) hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hedge : e ∈ latestEdge P (mkBasic S).πₐ (mkBasic S).ηₐ (mkBasic S).ηₚ nd z :=
          (Assignments.mem_inter.mp (Assignments.mem_toList.1 he)).1
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) hcont hfin e (edgeIns_sub_anti (mkBasic S) (Step.ifzT hf hcond) hpa hedge)
        rw [hw]; exact Option.some_ne_none w)
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz (mkBasic S) hf (Or.inr ⟨hcond, rfl⟩) hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) (StepsH.head (Step.ifzF hf hcond) hcont) hfin e
          (insertBefore_sub_anti (mkBasic S) hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hedge : e ∈ latestEdge P (mkBasic S).πₐ (mkBasic S).ηₐ (mkBasic S).ηₚ nd nz :=
          (Assignments.mem_inter.mp (Assignments.mem_toList.1 he)).1
        obtain ⟨w, hw⟩ := antiNoFault (mkBasic S) hcont hfin e (edgeIns_sub_anti (mkBasic S) (Step.ifzF hf hcond) hpa hedge)
        rw [hw]; exact Option.some_ne_none w)

/-- **`sim_basic`** — forward simulation over a halting run for the basic transform. -/
theorem sim_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f → (∀ v ∈ P.obs, varIsOrig v = true) →
    ∀ {d : Config} {M : Assignments}, Match P (mkBasic S) c d M →
      Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) → Cov S c.node M →
    ∃ d_f, Steps (transform P (mkBasic S)) d d_f ∧ Final (transform P (mkBasic S)) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  intro c c_f hrun
  induction hrun with
  | refl => intro hfin hobs d M hm hpa _; exact match_final_obs (mkBasic S) hm hpa hfin hobs
  | @head c c1 cf hstep htail ih =>
      intro hfin hobs d M hm hpa hcov
      obtain ⟨d1, hsteps1, hm1, hcov1⟩ := match_step_basic S hS wn hm hpa hcov hstep htail hfin
      obtain ⟨d_f, hsteps2, hfinf, hobsf⟩ := ih hfin hobs hm1 (postpSubAnti_step S hstep hpa) hcov1
      exact ⟨d_f, steps_trans hsteps1.toSteps hsteps2, hfinf, hobsf⟩

/-- **`transform_preserves_halt_basic`** — LCM correctness for the *basic* transform (isolated insertions
    permitted). On a halting source run, the basic transform halts with every observable agreeing. -/
theorem transform_preserves_halt_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) P.entry, σ⟩ d_f
         ∧ Final (transform P (mkBasic S)) d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  have hcov : Cov S (⟨P.entry, σ⟩ : Config).node Assignments.empty := by
    intro e he
    rw [Assignments.mem_sdiff, Assignments.mem_sdiff] at he
    exact absurd (πᵤK_sub S _ e he.1.1) (used_entry_empty S hS wn hen e)
  exact sim_basic S hS wn (steps_toH hrun) hfin hobs (match_init (mkBasic S) σ) (postpSubAnti_entry S) hcov


/-! ## Fault preservation (forward) for the basic transform: `Fault → Fault`

Mirrors the optimal fault chain (`match_faulting`/`match_step_ifz_fault`/`match_step_fault`/
`sim_fault`) at `mkBasic S`, threading the reference `Cov S`. The two `replace_covered` read-offs
become `hcovered_basic`; coverage maintenance is `Cov_step_edge S hS` + `cov_mono` + monotonicity. -/

theorem match_faulting_basic (S : LcmSpec P) (wn : WellNormalized P)
    {c d : Config} {M : Assignments}
    (hm : Match P (mkBasic S) c d M) (hcov : Cov S c.node M) (hflt : Faulting P c) :
    ∃ df, Steps (transform P (mkBasic S)) d df ∧ Faulting (transform P (mkBasic S)) df := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  obtain ⟨nd, σ⟩ := c
  obtain ⟨x, e0, next, hf, hnone⟩ := hflt
  subst hlabel
  have hi : nd < P.size := fetch_lt hf
  have hfetch : ∀ k (hk : k < (insertBefore P (mkBasic S) nd).toList.length),
      (transform P (mkBasic S)).fetch (blockOff P (mkBasic S) nd + k)
        = some (.assign (tempFor P ((insertBefore P (mkBasic S) nd).toList[k]'hk)) ((insertBefore P (mkBasic S) nd).toList[k]'hk)
            (blockOff P (mkBasic S) nd + k + 1)) := by
    intro k hk
    have hkb : k < (block P (mkBasic S) nd).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (insChain P (insertBefore P (mkBasic S) nd).toList (blockOff P (mkBasic S) nd)).length := by
      rw [insChain_length]; exact hk
    rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]
  have hdist : ∀ e ∈ (insertBefore P (mkBasic S) nd).toList, ∀ e' ∈ (insertBefore P (mkBasic S) nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertBefore_mem_allExprs he))
      (Assignments.mem_toList.2 (insertBefore_mem_allExprs he')) heq)
  have hfresh : ∀ e ∈ (insertBefore P (mkBasic S) nd).toList, ∀ e' ∈ (insertBefore P (mkBasic S) nd).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertBefore_mem_allExprs he)
  rcases steps_insSeg_fault P (insertBefore P (mkBasic S) nd).toList (blockOff P (mkBasic S) nd) dσ
      Assignments.nodup_toList hdist hfetch hfresh with hfault | hclean
  · exact hfault
  · obtain ⟨τ1, hs1, hoff1, hon1⟩ := hclean
    have hag1 : ∀ y, NonFresh P y → τ1 y = σ y :=
      fun y hy => (hoff1 y (fun e _ => hy e)).trans (hagree y hy)
    -- the rewrite gate is impossible at a faulting node
    have hgfalse : (isNumbered e0 && (recoverable P (mkBasic S) nd).contains e0) = false := by
      cases h : (isNumbered e0 && (recoverable P (mkBasic S) nd).contains e0) with
      | false => rfl
      | true =>
        exfalso
        rcases hcovered_basic S hf wn hcov h with hM | hia
        · have := Holds_iff.1 (hHolds e0 hM); rw [hnone] at this; exact absurd this (by simp)
        · have := hon1 e0 (Assignments.mem_toList.2 hia)
          rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs (Assignments.mem_toList.2 hia)) hagree,
              hnone] at this
          exact absurd this (by simp)
    have hctl : (transform P (mkBasic S)).fetch (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length)
        = some (.assign x e0 (if (insertAfter P (mkBasic S) nd).toList.isEmpty then blockOff P (mkBasic S) next
            else blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1)) := by
      rw [ctrl_slot_fetch (mkBasic S) hi]; simp only [ctrlCmd, hf]; rw [if_neg (by simpa using hgfalse)]
    refine ⟨⟨blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length, τ1⟩, hs1, x, e0, _, hctl, ?_⟩
    rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
      (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
    exact hnone

theorem match_step_ifz_fault_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {nd : Node} {x : Var} {z nz succ : Node} {σ dσ : Store} {M : Assignments}
    (hf : P.fetch nd = some (.ifz x z nz))
    (hcond : (σ x = 0 ∧ succ = z) ∨ (σ x ≠ 0 ∧ succ = nz))
    (hagree : ∀ v, NonFresh P v → dσ v = σ v)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd)) (hcov : Cov S nd M) :
    (∃ df, Steps (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) nd, dσ⟩ df ∧ Faulting (transform P (mkBasic S)) df)
    ∨ (∃ d', Steps (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) nd, dσ⟩ d'
          ∧ Match P (mkBasic S) ⟨succ, σ⟩ d' (Mstep_edge (mkBasic S) nd succ M) ∧ Cov S succ (Mstep_edge (mkBasic S) nd succ M)) := by
  have hi : nd < P.size := fetch_lt hf
  rcases entryBlock_faultOr (mkBasic S) hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
  · exact Or.inl hEF
  · have hnfσ : ∀ e ∈ (insertBefore P (mkBasic S) nd).toList, eval σ e ≠ none := fun e he => by
      rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
    have hxnf : NonFresh P x := nonFresh_of_used hf (by simp [instrUsedVars])
    have hctlf : (transform P (mkBasic S)).fetch (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length)
        = some (.ifz x (if (insertEdge P (mkBasic S) nd z).toList.isEmpty then blockOff P (mkBasic S) z
                        else blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1)
                       (if (insertEdge P (mkBasic S) nd nz).toList.isEmpty then blockOff P (mkBasic S) nz
                        else blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1
                          + (insertEdge P (mkBasic S) nd z).toList.length)) := by
      rw [ctrl_slot_fetch (mkBasic S) hi]; simp only [ctrlCmd, hf]
    by_cases hX : ∃ e ∈ (insertEdge P (mkBasic S) nd succ).toList, eval σ e = none
    · refine Or.inl ?_
      have hnotempty : ¬((insertEdge P (mkBasic S) nd succ).toList.isEmpty = true) := by
        obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
      have run_edge_fault : ∀ (st : Nat),
          (∀ k (hk : k < (insertEdge P (mkBasic S) nd succ).toList.length),
            (transform P (mkBasic S)).fetch (st + k)
              = some (.assign (tempFor P ((insertEdge P (mkBasic S) nd succ).toList[k]'hk)) ((insertEdge P (mkBasic S) nd succ).toList[k]'hk)
                  (if k + 1 == (insertEdge P (mkBasic S) nd succ).toList.length then blockOff P (mkBasic S) succ else st + k + 1))) →
          ∃ df, Steps (transform P (mkBasic S)) ⟨st, τ1⟩ df ∧ Faulting (transform P (mkBasic S)) df := by
        intro st hfetch
        have hdist : ∀ e ∈ (insertEdge P (mkBasic S) nd succ).toList, ∀ e' ∈ (insertEdge P (mkBasic S) nd succ).toList,
            e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
          hne (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs he))
            (Assignments.mem_toList.2 (insertEdge_mem_allExprs he')) heq)
        have hfresh : ∀ e ∈ (insertEdge P (mkBasic S) nd succ).toList, ∀ e' ∈ (insertEdge P (mkBasic S) nd succ).toList,
            exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertEdge_mem_allExprs he)
        rcases steps_exitSeg_fault P (blockOff P (mkBasic S) succ) (insertEdge P (mkBasic S) nd succ).toList st τ1
            Assignments.nodup_toList hdist hfetch hfresh with hF | ⟨τ2, _, _, hon2⟩
        · exact hF
        · exfalso; obtain ⟨e, he, hev⟩ := hX; have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs he) hag1, hev] at this
          exact absurd this (by simp)
      rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩ <;> subst succ
      · have hstep := Step.ifzT (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hx0)
        rw [if_neg hnotempty] at hstep
        obtain ⟨df, hsdf, hfltdf⟩ := run_edge_fault (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1) (by
          intro k hk
          have hkb : (insertBefore P (mkBasic S) nd).toList.length + 1 + k < (block P (mkBasic S) nd).length := by
            rw [block_length]
            have hbl : blockLen P (mkBasic S) nd = (insertBefore P (mkBasic S) nd).toList.length + 1
                + ((insertEdge P (mkBasic S) nd z).toList.length + (insertEdge P (mkBasic S) nd nz).toList.length) := by
              simp only [blockLen, hf]
            rw [hbl]; omega
          rw [show (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1) + k
                = blockOff P (mkBasic S) nd + ((insertBefore P (mkBasic S) nd).toList.length + 1 + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_z hf hk, exitChain_getElem? hk,
              show blockOff P (mkBasic S) nd + ((insertBefore P (mkBasic S) nd).toList.length + 1 + k) + 1
                = blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1 + k + 1 from by omega])
        exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hsdf), hfltdf⟩
      · have hstep := Step.ifzF (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hxne)
        rw [if_neg hnotempty] at hstep
        obtain ⟨df, hsdf, hfltdf⟩ :=
          run_edge_fault (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length) (by
          intro k hk
          have hkb : (insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length + k
              < (block P (mkBasic S) nd).length := by
            rw [block_length]
            have hbl : blockLen P (mkBasic S) nd = (insertBefore P (mkBasic S) nd).toList.length + 1
                + ((insertEdge P (mkBasic S) nd z).toList.length + (insertEdge P (mkBasic S) nd nz).toList.length) := by
              simp only [blockLen, hf]
            rw [hbl]; omega
          rw [show (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length) + k
                = blockOff P (mkBasic S) nd + ((insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_nz hf hk, exitChain_getElem? hk,
              show blockOff P (mkBasic S) nd + ((insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length + k) + 1
                = blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1 + (insertEdge P (mkBasic S) nd z).toList.length + k + 1 from by omega])
        exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hsdf), hfltdf⟩
    · have hnfe : ∀ e ∈ (insertEdge P (mkBasic S) nd succ).toList, eval σ e ≠ none := fun e he hev => hX ⟨e, he, hev⟩
      have hstepsrc : Step P ⟨nd, σ⟩ ⟨succ, σ⟩ := by
        rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩
        · rw [hsu]; exact Step.ifzT hf hx0
        · rw [hsu]; exact Step.ifzF hf hxne
      obtain ⟨d', hsteps, hmatch⟩ := match_step_ifz (mkBasic S) hf hcond hagree hHolds hMsub hpa hnfσ hnfe
      refine Or.inr ⟨d', hsteps.toSteps, hmatch, ?_⟩
      show Cov S (⟨succ, σ⟩ : Config).node
        (Mstep_edge (mkBasic S) (⟨nd, σ⟩ : Config).node (⟨succ, σ⟩ : Config).node M)
      exact cov_mono S (Cov_step_edge S hS wn hstepsrc hcov) (Mstep_edge_sub_mkBasic S nd succ M)

theorem match_step_fault_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments}
    (hm : Match P (mkBasic S) c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c') :
    (∃ df, Steps (transform P (mkBasic S)) d df ∧ Faulting (transform P (mkBasic S)) df)
    ∨ (∃ d', Steps (transform P (mkBasic S)) d d' ∧ Match P (mkBasic S) c' d' (Mstep_edge (mkBasic S) c.node c'.node M)
          ∧ Cov S c'.node (Mstep_edge (mkBasic S) c.node c'.node M)) := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    have hi : nd < P.size := fetch_lt hf
    rcases entryBlock_faultOr (mkBasic S) hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
    · exact Or.inl hEF
    · have hnfσ : ∀ e ∈ (insertBefore P (mkBasic S) nd).toList, eval σ e ≠ none := fun e he => by
        rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
      by_cases hX : ∃ e ∈ (insertAfter P (mkBasic S) nd).toList, eval (σ.update x vv) e = none
      · -- exit chain faults ⇒ target faults
        refine Or.inl ?_
        have hnotempty : ¬((insertAfter P (mkBasic S) nd).toList.isEmpty = true) := by
          obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
        have hctrl : ∃ rhs, (transform P (mkBasic S)).fetch (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length)
              = some (.assign x rhs (if (insertAfter P (mkBasic S) nd).toList.isEmpty then blockOff P (mkBasic S) next
                  else blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1)) ∧ eval τ1 rhs = some vv := by
          by_cases hg : (isNumbered e0 && (recoverable P (mkBasic S) nd).contains e0) = true
          · refine ⟨.atom (.var (tempFor P e0)),
              by rw [ctrl_slot_fetch (mkBasic S) hi]; simp only [ctrlCmd, hf]; rw [if_pos hg], ?_⟩
            have hHe0 : Holds τ1 σ (tempFor P e0) e0 := hH1 e0 (hcovered_basic S hf wn hcov hg)
            simp only [eval, evalAtom]; exact (Holds_iff.1 hHe0).trans hvv
          · refine ⟨e0, by rw [ctrl_slot_fetch (mkBasic S) hi]; simp only [ctrlCmd, hf]; rw [if_neg hg], ?_⟩
            rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
              (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
            exact hvv
        obtain ⟨rhs, hfetchr, hrhsv⟩ := hctrl
        have hctlstep : Step (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length, τ1⟩
            ⟨blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1, τ1.update x vv⟩ := by
          have hc := Step.assign hfetchr hrhsv; rw [if_neg hnotempty] at hc; exact hc
        have hag1' : ∀ y, NonFresh P y → (τ1.update x vv) y = (σ.update x vv) y := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; simp [Store.update]
          · simp only [Store.update, if_neg hyx]; exact hag1 y hy
        rcases exitBlock_faultOr (mkBasic S) hi (Or.inr ⟨x, e0, hf⟩) (τ := τ1.update x vv) with hXF | ⟨τ2, _, _, hon2⟩
        · obtain ⟨df, hsdf, hfltdf⟩ := hXF
          exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hctlstep) hsdf), hfltdf⟩
        · exfalso
          obtain ⟨e, he, hev⟩ := hX
          have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1', hev] at this
          exact absurd this (by simp)
      · -- exit chain clean ⇒ full clean step via `match_step_assign`
        have hnfeσ : ∀ e ∈ (insertAfter P (mkBasic S) nd).toList, eval (σ.update x vv) e ≠ none :=
          fun e he hev => hX ⟨e, he, hev⟩
        obtain ⟨d', hsteps, hmatch⟩ :=
          match_step_assign (mkBasic S) wn hf hvv hagree hHolds hMsub hpa
            (fun hg => hcovered_basic S hf wn hcov hg)
            hnfσ hnfeσ
        exact Or.inr ⟨d', hsteps.toSteps, Match_union_sub hmatch (fun e he => Assignments.mem_union.mpr
          (Or.inr (by rw [insertAfter_eq_insertEdge (mkBasic S) (Or.inr ⟨x, e0, hf⟩)]; exact he))),
          cov_mono S (Cov_step_edge S hS wn (Step.assign hf hvv) hcov) (Mstep_edge_sub_mkBasic S nd next M)⟩
  | @noop nd σ next hf =>
    subst hlabel
    have hi : nd < P.size := fetch_lt hf
    rcases entryBlock_faultOr (mkBasic S) hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
    · exact Or.inl hEF
    · have hnfσ : ∀ e ∈ (insertBefore P (mkBasic S) nd).toList, eval σ e ≠ none := fun e he => by
        rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
      by_cases hX : ∃ e ∈ (insertAfter P (mkBasic S) nd).toList, eval σ e = none
      · refine Or.inl ?_
        have hnotempty : ¬((insertAfter P (mkBasic S) nd).toList.isEmpty = true) := by
          obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
        have hctl : (transform P (mkBasic S)).fetch (blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length)
            = some (ctrlCmd P (mkBasic S) nd) := ctrl_slot_fetch (mkBasic S) hi
        have hctlstep : Step (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length, τ1⟩
            ⟨blockOff P (mkBasic S) nd + (insertBefore P (mkBasic S) nd).toList.length + 1, τ1⟩ := by
          refine Step.noop ?_; rw [hctl]; simp only [ctrlCmd, hf, if_neg hnotempty]
        rcases exitBlock_faultOr (mkBasic S) hi (Or.inl hf) (τ := τ1) with hXF | ⟨τ2, _, _, hon2⟩
        · obtain ⟨df, hsdf, hfltdf⟩ := hXF
          exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hctlstep) hsdf), hfltdf⟩
        · exfalso
          obtain ⟨e, he, hev⟩ := hX
          have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1, hev] at this
          exact absurd this (by simp)
      · have hnfeσ : ∀ e ∈ (insertAfter P (mkBasic S) nd).toList, eval σ e ≠ none :=
          fun e he hev => hX ⟨e, he, hev⟩
        obtain ⟨d', hsteps, hmatch⟩ := match_step_noop (mkBasic S) hf hagree hHolds hMsub hpa hnfσ hnfeσ
        exact Or.inr ⟨d', hsteps.toSteps, Match_union_sub hmatch (fun e he => Assignments.mem_union.mpr
          (Or.inr (by rw [insertAfter_eq_insertEdge (mkBasic S) (Or.inl hf)]; exact he))),
          cov_mono S (Cov_step_edge S hS wn (Step.noop hf) hcov) (Mstep_edge_sub_mkBasic S nd next M)⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz_fault_basic S hS wn hf (Or.inl ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hcov
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz_fault_basic S hS wn hf (Or.inr ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hcov

/-- **Forward fault simulation (basic).** -/
theorem sim_fault_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) :
    ∀ {c c_n : Config}, StepsH P c c_n → Faulting P c_n →
    ∀ {d : Config} {M : Assignments}, Match P (mkBasic S) c d M →
      Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) → Cov S c.node M →
      ∃ df, Steps (transform P (mkBasic S)) d df ∧ Faulting (transform P (mkBasic S)) df := by
  intro c c_n hrun
  induction hrun with
  | refl => intro hflt d M hm _ hcov; exact match_faulting_basic S wn hm hcov hflt
  | @head c c1 cn hstep htail ih =>
      intro hflt d M hm hpa hcov
      rcases match_step_fault_basic S hS wn hm hpa hcov hstep with hF | ⟨d1, hs1, hm1, hcov1⟩
      · exact hF
      · obtain ⟨df, hsdf, hfltdf⟩ := ih hflt hm1 (postpSubAnti_step S hstep hpa) hcov1
        exact ⟨df, steps_trans hs1 hsdf, hfltdf⟩

/-- **`transform_preserves_faulting_basic` — the basic LCM transform preserves faults
    (forward `Fault → Fault`).** On a source run reaching a `Faulting` config, `transform P (mkBasic S)`
    also reaches a `Faulting` config. The new content over halt: at a source fault the faulting `e0` is
    forced into `insBefore'` (materialized as `t_{e0} := e0` in the entry chain) since `Cov`/`Holds` rule out
    `e0 ∈ M`; that insert faults by down-safety, or — when `e0` is not numbered — the control keeps `x := e0`
    and faults. Both are `match_faulting_basic`'s `hgfalse` branch. -/
theorem transform_preserves_faulting_basic (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    {σ : Store} {c_n : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_n) (hflt : Faulting P c_n) :
    ∃ df, Steps (transform P (mkBasic S)) ⟨blockOff P (mkBasic S) P.entry, σ⟩ df
        ∧ Faulting (transform P (mkBasic S)) df := by
  have hcov : Cov S (⟨P.entry, σ⟩ : Config).node Assignments.empty := by
    intro e he
    rw [Assignments.mem_sdiff, Assignments.mem_sdiff] at he
    exact absurd (πᵤK_sub S _ e he.1.1) (used_entry_empty S hS wn hen e)
  exact sim_fault_basic S hS wn (steps_toH hrun) hflt (match_init (mkBasic S) σ) (postpSubAnti_entry S) hcov

end BaseLanguage.Analyses.LCM
