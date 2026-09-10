-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.EvalCountPlace

/-!
# Eval-count optimality headline: `evalCount(transform) e ≤ #pl` for every safe placement

The computational (eval-count) optimality of Lazy Code Motion — the run-dependent capstone (it does
not lift pointwise by `length_filter_mono`, unlike lifetime/sinking). Along every terminating run, the
transform evaluates each tracked expression `e` no more often than any **safe placement** `pl`.

The proof counts **`earliest`-crossings** (steps `c→c'` with `e ∈ earliest(c,c')` — the genuine fresh-need
frontier) as the unit. This admits **eager** placements (busy-code-motion, which ties S on eval-count) — the
case the `bndN`-segmentation (`EvalCountPlace.cE_le_pl`) excludes — and rules out only out-of-scope
this-path-clever reuse. Two one-sided lemmas compose:
* **Lemma A** (`cE_count_le_cross`): `#cE ≤ #crossings + [ηₚ start]` (S evaluates ≤ once per crossing).
* **Lemma B** (`crossCount_le_pl`): `#crossings + [owed] ≤ #pl` (a covering placement evaluates ≥ once per
  crossing).
At the entry `ηₚ(entry)=∅` and `owed=false`, so `evalCount = srcContrib = #cE ≤ #crossings ≤ #pl`.

The `earliest`-engine (`notPostp_maintain_earliest` etc.) is *simpler* than the `bndN` engine — no M-set, no
`πₐ`-gap bookkeeping — because an `earliest`-crossing is exactly where `e` re-enters `ηₚ`.
`crossCount`/`PlCovers` are projections of `earliest`/`step1`/`pl`, not new analyses.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-! ## The `earliest`-crossing engine (`cE` ↔ `ηₚ` frontier facts) -/


/-- **Non-boundary `postp`-maintenance.** No `pass`/`πₐ` needed — purely the `earliest`-frontier. -/
theorem notPostp_maintain_earliest {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hstep : Step P c c')
    (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node) (hnp : e ∉ S.ηₚ c.node) :
    e ∉ S.ηₚ c'.node := by
  intro hp
  have hup := S.isPostp.update c c' hstep e hp
  rw [Assignments.mem_union] at hup
  rcases hup with hearl | hdiff
  · exact hnb hearl
  · exact hnp (Assignments.mem_sdiff.mp hdiff).1

/-- **Non-boundary insert establish.** `e ∈ insertBefore(c)` at a non-`earliest` step ⇒ `e ∉ postp(c')`. -/
theorem insertBefore_notPostp_succ_earliest {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config} {e : Expr} (hstep : Step P c c')
    (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node) (hia : e ∈ insertBefore P S c.node) :
    e ∉ S.ηₚ c'.node := by
  intro hp
  have hup := S.isPostp.update c c' hstep e hp
  rw [Assignments.mem_union] at hup
  rcases hup with hearl | hdiff
  · exact hnb hearl
  · have hnue := (Assignments.mem_sdiff.mp hdiff).2
    have hlat : e ∈ latestNode P S.ηₚ S.τₚ c.node := insertBefore_sub_latestNode (Assignments.mem_toList.2 hia)
    unfold latestNode at hlat; rw [Assignments.mem_inter, Assignments.mem_union] at hlat
    have hntp : e ∉ S.τₚ c.node := by
      rcases hlat.2 with hue | hctp
      · exact absurd hue hnue
      · unfold compl at hctp; exact (Assignments.mem_sdiff.mp hctp).2
    -- single-succ: postp(c') ⊆ tauP(c) contradicts e∉tauP; multi-succ: insert ⇒ e∈ue, contra
    cases hstep with
    | @noop nd σ next hf =>
        exact hntp (postp_succ_sub_tauP S hS (single_succ_of_fetch (Or.inl hf)) e hp)
    | @assign nd σ x e0 next v hf hv =>
        exact hntp (postp_succ_sub_tauP S hS (single_succ_of_fetch (Or.inr ⟨x, e0, hf⟩)) e hp)
    | @ifzT nd σ x z nz hf hc =>
        have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
        exact hnue (insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia))
    | @ifzF nd σ x z nz hf hc =>
        have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
        exact hnue (insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia))

/-- **Non-boundary `cE ⇒ e∈postp(c)`** (the precondition lever). Inserts `⊆ postp`; an exit insert at a
    non-boundary step is in the `ηₚ∖ue` part of `latestEdge` (the `earliest` part excluded); a kept use is
    `∈ ue∖πᵤ ⊆ latestNode ⊆ ηₚ`. -/
theorem cE_imp_postp_earliest {P : Program} (S : LcmSpec P) (wn : WellNormalized P)
    (hgc : GateComplete S) {c c' : Config} {e : Expr}
    (hi : c.node < P.size) (hnum : isNumbered e = true) (hkeep : S.keep e = true) (hstep : Step P c c')
    (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node)
    (hce : cE P S c.node e = true) : e ∈ S.ηₚ c.node := by
  unfold cE at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))
    · -- insertAfter ⊆ latestEdge; at a non-boundary step the earliest part is excluded ⇒ postp∖ue part ⇒ e∈postp
      cases hstep with
      | @noop nd σ next hf =>
          have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd next := by
            unfold insertAfter at hie; rw [hf] at hie; exact (Assignments.mem_inter.mp hie).1
          unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
          rcases hedge.1 with hear | hdif
          · exact absurd hear hnb
          · exact (Assignments.mem_sdiff.mp hdif).1
      | @assign nd σ x e0 next v hf hv =>
          have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd next := by
            unfold insertAfter at hie; rw [hf] at hie; exact (Assignments.mem_inter.mp hie).1
          unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
          rcases hedge.1 with hear | hdif
          · exact absurd hear hnb
          · exact (Assignments.mem_sdiff.mp hdif).1
      | @ifzT nd σ x z nz hf hc => unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty
      | @ifzF nd σ x z nz hf hc => unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty
  · obtain ⟨hue, hnr⟩ := keptCtrl_imp hi hnum hk
    exact latestNode_sub_postp S c.node e (keptUse_latestNode S hgc wn hue hkeep hnr)

/-- **Non-boundary kept/insertAfter establish.** Completes the establish for all `cE` shapes at a non-boundary
    step (insertBefore is `insertBefore_notPostp_succ_earliest`; this is kept + insertAfter). -/
theorem cE_imp_notPostp_succ_earliest {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config} {e : Expr} (hnum : isNumbered e = true)
    (hstep : Step P c c') (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node)
    (hce : cE P S c.node e = true) : e ∉ S.ηₚ c'.node := by
  have hi : c.node < P.size := fetch_lt (step_fetch hstep).choose_spec
  unfold cE at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact insertBefore_notPostp_succ_earliest S hS wn hstep hnb hia
    · exact insertAfter_imp_notPostp_succ S hstep hie
  · obtain ⟨hue, _⟩ := keptCtrl_imp hi hnum hk
    exact ue_transp_notPostp_succ S hstep hue (ue_sub_transp wn hue)


/-! ## Lemma A — the transform's eval count is at most the `earliest`-crossing count (`cE_count_le_cross`) -/


/-- Number of `earliest`-crossing steps along the run from `c` (with `ks` fuel). -/
def crossCount (P : Program) (S : LcmSpec P) (e : Expr) : Config → Nat → Nat
  | _, 0 => 0
  | c, k + 1 =>
      match step1 P c with
      | .next c' =>
          (if e ∈ earliest P S.πₐ S.ηₐ c.node c'.node then 1 else 0)
            + crossCount P S e c' k
      | _ => 0

/-- At a node with `e ∉ postp`, the only possible eval is an exit insert (entry inserts and kept controls
    both need `e ∈ ηₚ`). -/
theorem cE_notPostp_imp_insertAfter {P : Program} (S : LcmSpec P) (wn : WellNormalized P) (hgc : GateComplete S)
    {c : Config} {e : Expr}
    (hi : c.node < P.size) (hnum : isNumbered e = true) (hkeep : S.keep e = true)
    (hnp : e ∉ S.ηₚ c.node) (hce : cE P S c.node e = true) : e ∈ insertAfter P S c.node := by
  unfold cE at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact absurd (latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))) hnp
    · exact hie
  · -- kept ⇒ e ∈ ue ∖ used ⊆ latestNode ⊆ postp, contra hnp
    obtain ⟨hue, hnr⟩ := keptCtrl_imp hi hnum hk
    exact absurd (latestNode_sub_postp S c.node e
      (keptUse_latestNode S hgc wn hue hkeep hnr)) hnp

/-- Edge (`cEb`) version of `cE_imp_postp_earliest`. -/
theorem cEb_imp_postp_earliest {P : Program} (S : LcmSpec P) (wn : WellNormalized P)
    (hgc : GateComplete S) {c c' : Config} {e : Expr}
    (hi : c.node < P.size) (hnum : isNumbered e = true) (hkeep : S.keep e = true) (hstep : Step P c c')
    (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node)
    (hce : cEb P S c.node c'.node e = true) : e ∈ S.ηₚ c.node := by
  unfold cEb at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))
    · have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node :=
        (Assignments.mem_inter.mp hie).1
      unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
      rcases hedge.1 with hear | hdif
      · exact absurd hear hnb
      · exact (Assignments.mem_sdiff.mp hdif).1
  · obtain ⟨hue, hnr⟩ := keptCtrl_imp hi hnum hk
    exact latestNode_sub_postp S c.node e (keptUse_latestNode S hgc wn hue hkeep hnr)

/-- Edge (`cEb`) version of `cE_imp_notPostp_succ_earliest`. -/
theorem cEb_imp_notPostp_succ_earliest {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config} {e : Expr} (hnum : isNumbered e = true)
    (hstep : Step P c c') (hnb : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node)
    (hce : cEb P S c.node c'.node e = true) : e ∉ S.ηₚ c'.node := by
  have hi : c.node < P.size := fetch_lt (step_fetch hstep).choose_spec
  unfold cEb at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact insertBefore_notPostp_succ_earliest S hS wn hstep hnb hia
    · exact insertEdge_imp_notPostp_succ S hie
  · obtain ⟨hue, _⟩ := keptCtrl_imp hi hnum hk
    exact ue_transp_notPostp_succ S hstep hue (ue_sub_transp wn hue)

/-- Edge (`cEb`) version of `cE_notPostp_imp_insertAfter`: at `e ∉ postp c`, the only eval is a taken edge insert. -/
theorem cEb_notPostp_imp_insertEdge {P : Program} (S : LcmSpec P) (wn : WellNormalized P)
    (hgc : GateComplete S) {c c' : Config} {e : Expr}
    (hi : c.node < P.size) (hnum : isNumbered e = true) (hkeep : S.keep e = true)
    (hnp : e ∉ S.ηₚ c.node) (hce : cEb P S c.node c'.node e = true) : e ∈ insertEdge P S c.node c'.node := by
  unfold cEb at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · exact absurd (latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))) hnp
    · exact hie
  · obtain ⟨hue, hnr⟩ := keptCtrl_imp hi hnum hk
    exact absurd (latestNode_sub_postp S c.node e
      (keptUse_latestNode S hgc wn hue hkeep hnr)) hnp

/-- **Lemma A (edge) — `srcContrib ≤ #crossings + [postp start]`.** Along any halting source run, the transform
    evaluates `e` at most once per `earliest`-crossing (plus the initial pending deferral). `srcContrib` (the
    edge-indexed per-step contribution `= [cEb]` via `blockContribution_eq_cEb`) replaces the per-node `#cE`. -/
theorem cE_count_le_cross {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    (hgc : GateComplete S) {e : Expr}
    (hnum : isNumbered e = true) (hkeep : S.keep e = true) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f →
    ∀ ks, run P c ks = (c_f, .next c_f) →
      srcContrib P S e c ks
        ≤ crossCount P S e c ks + (if e ∈ S.ηₚ c.node then 1 else 0) := by
  intro c c_f hrun
  induction hrun with
  | @refl c0 =>
      intro hfin ks hks
      cases ks with
      | zero => simp [srcContrib, crossCount]
      | succ k =>
          exfalso
          have hh : step1 P c0 = .halt := by
            unfold step1; rw [show P.fetch c0.node = some .halt from hfin]
          rw [show run P c0 (k + 1) = (c0, .halt) from by simp [run, hh]] at hks; simp at hks
  | @head c c1 cf hstep htail ih =>
      intro hfin ks hks
      have hstepf : step1 P c = .next c1 := step1_next_iff.mpr hstep
      cases ks with
      | zero =>
          exfalso
          rw [show run P c 0 = (c, .next c) from rfl] at hks
          have hcf : c = cf := ((Prod.mk.injEq _ _ _ _).mp hks).1
          subst hcf; simp only [Final] at hfin; cases hstep <;> simp_all
      | succ k =>
          have hk : run P c1 k = (cf, .next cf) := by
            rw [show run P c (k + 1) = run P c1 k from by simp [run, hstepf]] at hks; exact hks
          have ihk := ih hfin k hk
          have hi : c.node < P.size := fetch_lt (step_fetch hstep).choose_spec
          have hcc : crossCount P S e c (k + 1)
              = (if e ∈ earliest P S.πₐ S.ηₐ c.node c1.node then 1 else 0)
                + crossCount P S e c1 k := by
            simp only [crossCount, hstepf]
          rw [srcContrib_next hstepf, blockContribution_eq_cEb S wn hstep hi e, hcc]
          have hp1 : (if e ∈ S.ηₚ c1.node then 1 else 0) ≤ 1 := by split <;> omega
          have hcE1 : (if cEb P S c.node c1.node e then 1 else 0) ≤ 1 := by split <;> omega
          by_cases hcross : e ∈ earliest P S.πₐ S.ηₐ c.node c1.node
          · -- CROSSING step
            rw [if_pos hcross]
            by_cases hpc : e ∈ S.ηₚ c.node
            · rw [if_pos hpc]; omega
            · rw [if_neg hpc]
              by_cases hce : cEb P S c.node c1.node e = true
              · rw [if_pos hce]
                have hie : e ∈ insertEdge P S c.node c1.node := cEb_notPostp_imp_insertEdge S wn hgc hi hnum hkeep hpc hce
                rw [if_neg (insertEdge_imp_notPostp_succ S hie)] at ihk
                omega
              · rw [Bool.not_eq_true] at hce; rw [if_neg (by rw [hce]; exact Bool.false_ne_true)]
                omega
          · -- NON-CROSSING step: the engine
            rw [if_neg hcross]
            by_cases hce : cEb P S c.node c1.node e = true
            · rw [if_pos hce]
              rw [if_pos (cEb_imp_postp_earliest S wn hgc hi hnum hkeep hstep hcross hce)]
              rw [if_neg (cEb_imp_notPostp_succ_earliest S hS wn hnum hstep hcross hce)] at ihk
              omega
            · rw [Bool.not_eq_true] at hce; rw [if_neg (by rw [hce]; exact Bool.false_ne_true)]
              by_cases hpc : e ∈ S.ηₚ c.node
              · rw [if_pos hpc]; omega
              · rw [if_neg hpc]
                rw [if_neg (notPostp_maintain_earliest S hstep hcross hpc)] at ihk
                omega


/-! ## Lemma B — the `earliest`-crossing count is at most any safe placement's count (`crossCount_le_pl`) -/


/-- **Operational coverage of a placement `pl`.** Between consecutive `earliest`-crossings there is a `pl`-eval
    (`owed` tracks a pending crossing; a new crossing requires the pending one already covered). The
    all-paths (must) safe-placement condition — satisfied by S itself (`pl = cE`) and by eager busy-code-motion. -/
def PlCovers (P : Program) (S : LcmSpec P) (e : Expr) (pl : Node → Bool) :
    Config → Nat → Bool → Prop
  | _, 0, owed => owed = false
  | c, k + 1, owed =>
      match step1 P c with
      | .next c' =>
          if e ∈ earliest P S.πₐ S.ηₐ c.node c'.node then
            ((owed && !(pl c.node)) = false) ∧ PlCovers P S e pl c' k true
          else
            PlCovers P S e pl c' k (owed && !(pl c.node))
      | _ => owed = false

/-- **Lemma B — `#crossings + [owed] ≤ #pl`.** A covering placement evaluates `e` at least once per
    `earliest`-crossing. At entry (`owed = false`) this gives `crossCount ≤ #pl`. -/
theorem crossCount_le_pl {P : Program} (S : LcmSpec P) {e : Expr} (pl : Node → Bool) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f →
    ∀ ks, run P c ks = (c_f, .next c_f) → ∀ owed, PlCovers P S e pl c ks owed →
      crossCount P S e c ks + (if owed then 1 else 0)
        ≤ ((runNodes P c ks).filter pl).length := by
  intro c c_f hrun
  induction hrun with
  | @refl c0 =>
      intro hfin ks hks owed hcov
      cases ks with
      | zero =>
          have : owed = false := hcov
          subst this; simp [runNodes, crossCount]
      | succ k =>
          exfalso
          have hh : step1 P c0 = .halt := by
            unfold step1; rw [show P.fetch c0.node = some .halt from hfin]
          rw [show run P c0 (k + 1) = (c0, .halt) from by simp [run, hh]] at hks; simp at hks
  | @head c c1 cf hstep htail ih =>
      intro hfin ks hks owed hcov
      have hstepf : step1 P c = .next c1 := step1_next_iff.mpr hstep
      cases ks with
      | zero =>
          exfalso
          rw [show run P c 0 = (c, .next c) from rfl] at hks
          have hcf : c = cf := ((Prod.mk.injEq _ _ _ _).mp hks).1
          subst hcf; simp only [Final] at hfin; cases hstep <;> simp_all
      | succ k =>
          have hk : run P c1 k = (cf, .next cf) := by
            rw [show run P c (k + 1) = run P c1 k from by simp [run, hstepf]] at hks; exact hks
          have hrn : runNodes P c (k + 1) = c.node :: runNodes P c1 k := by simp [runNodes, hstepf]
          have hcc : crossCount P S e c (k + 1)
              = (if e ∈ earliest P S.πₐ S.ηₐ c.node c1.node then 1 else 0)
                + crossCount P S e c1 k := by
            simp only [crossCount, hstepf]
          have hfp : (List.filter pl (c.node :: runNodes P c1 k)).length
              = (if pl c.node then 1 else 0) + (List.filter pl (runNodes P c1 k)).length := by
            rw [List.filter_cons]
            by_cases h : pl c.node <;> simp [h, Nat.add_comm]
          rw [hcc, hrn, hfp]
          rw [PlCovers] at hcov
          simp only [hstepf] at hcov
          by_cases hcross : e ∈ earliest P S.πₐ S.ηₐ c.node c1.node
          · rw [if_pos hcross] at hcov
            obtain ⟨ho1, hrec⟩ := hcov
            have ihk : crossCount P S e c1 k + 1 ≤ (List.filter pl (runNodes P c1 k)).length := by
              have := ih hfin k hk true hrec; simpa using this
            rw [if_pos hcross]
            have hop : (if owed = true then (1:Nat) else 0) ≤ (if pl c.node = true then 1 else 0) := by
              revert ho1; cases owed <;> cases hb : pl c.node <;> simp
            omega
          · rw [if_neg hcross] at hcov
            have ihk := ih hfin k hk (owed && !(pl c.node)) hcov
            rw [if_neg hcross]
            have hop : (if owed = true then (1:Nat) else 0)
                ≤ (if pl c.node = true then 1 else 0)
                  + (if (owed && !(pl c.node)) = true then 1 else 0) := by
              cases owed <;> cases hb : pl c.node <;> simp
            omega


/-! ## The headline assembly (`transform_evalCount_le_safe`) -/


/-- `e ∉ postp(entry)` — the `postp` seed is empty. -/
theorem notPostp_entry {P : Program} (S : LcmSpec P) {e : Expr} : e ∉ S.ηₚ P.entry := by
  intro h
  have := S.isPostp.seed e h
  simp only [entrySeed, Assignments.empty] at this
  exact Std.HashSet.not_mem_empty this

/-- **THE HEADLINE — computational (eval-count) optimality of Lazy Code Motion.** Along every terminating
    run, the transform evaluates `e` no more often than any safe (all-paths must, `PlCovers`) placement `pl`
    does over the source path.

    The fuel `kt` is **pinned by the first conjunct** to a run that carries the transformed program all the
    way to its final configuration `⟨blockOff P S c_f.node, τf⟩` — the image of the source's final config
    `c_f` under the layout. Without that conjunct the bound would be vacuous: `evalCount` is fuel-bounded
    (`IR/Cost.lean`, `evalCount _ 0 = 0`), so an unconstrained `∃ kt` is discharged by `kt := 0` regardless
    of the hypotheses. The count is therefore over the *complete* transformed run, not a prefix of it. -/
theorem transform_evalCount_le_safe {P : Program} (S : LcmSpec P) (hS : Extremal S)
    (hg : GateSound P S) (hgc : GateComplete S) (wn : WellNormalized P)
    {e : Expr} (hnum : isNumbered e = true)
    (hkeep : S.keep e = true)
    (pl : Node → Bool) {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f)
    (ks : Nat) (hks : run P ⟨P.entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCovers P S e pl ⟨P.entry, σ⟩ ks false) :
    ∃ kt τf, run (transform P S) ⟨blockOff P S P.entry, σ⟩ kt
                = (⟨blockOff P S c_f.node, τf⟩, .next ⟨blockOff P S c_f.node, τf⟩)
            ∧ evalCount (transform P S) e ⟨blockOff P S P.entry, σ⟩ kt
                ≤ ((runNodes P ⟨P.entry, σ⟩ ks).filter pl).length := by
  obtain ⟨kt, τf, hrunT, heq⟩ := transform_evalCount S hg e hrun hfin
  refine ⟨kt, τf, hrunT, ?_⟩
  rw [heq ks hks]
  have hA := cE_count_le_cross S hS wn hgc hnum hkeep (steps_toH hrun) hfin ks hks
  have hB := crossCount_le_pl S pl (steps_toH hrun) hfin ks hks false hcov
  rw [if_neg (notPostp_entry S)] at hA
  simp only [if_false, Nat.add_zero] at hA hB
  omega


end BaseLanguage.Analyses.LCM
