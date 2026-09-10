-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness.MatchStep

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## Fault preservation (forward): `Fault → Fault`

The halting theorem above is silent on faulting runs. This section proves the **diagonal `Fault → Fault`**
cell (LCM.md §5): a source run that reaches a `Faulting` config drives the target to a `Faulting` config.
The engine is the **fault boundary** `match_faulting`: at a source fault the faulting expression `e0` is
neither available (`Holds` gives a value) nor safely rewritten (`replace_covered`+`Cov` would materialize
it), so the target block must recompute `e0` and faults — caught by the fault-aware chain runner. -/

/-- **Fault boundary.** At a source `Faulting` config `c` (its `assign`'s rhs `e0` faults), any matched
    target `d` with a covered `M` also faults: run the block's `insChain` fault-aware — either an insert
    already faults, or it completes at the control slot, where the control necessarily keeps the original
    `x := e0` (the rewrite gate is excluded, since `replace_covered` would give `e0` a value contradicting
    `eval σ e0 = none`), and that control faults. -/
theorem match_faulting {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    {c d : Config} {M : Assignments}
    (hm : Match P S c d M) (hcov : Cov S c.node M) (hflt : Faulting P c) :
    ∃ df, Steps (transform P S) d df ∧ Faulting (transform P S) df := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  obtain ⟨nd, σ⟩ := c
  obtain ⟨x, e0, next, hf, hnone⟩ := hflt
  subst hlabel
  have hi : nd < P.size := fetch_lt hf
  have hfetch : ∀ k (hk : k < (insertBefore P S nd).toList.length),
      (transform P S).fetch (blockOff P S nd + k)
        = some (.assign (tempFor P ((insertBefore P S nd).toList[k]'hk)) ((insertBefore P S nd).toList[k]'hk)
            (blockOff P S nd + k + 1)) := by
    intro k hk
    have hkb : k < (block P S nd).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (insChain P (insertBefore P S nd).toList (blockOff P S nd)).length := by
      rw [insChain_length]; exact hk
    rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]
  have hdist : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertBefore_mem_allExprs he))
      (Assignments.mem_toList.2 (insertBefore_mem_allExprs he')) heq)
  have hfresh : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertBefore_mem_allExprs he)
  rcases steps_insSeg_fault P (insertBefore P S nd).toList (blockOff P S nd) dσ
      Assignments.nodup_toList hdist hfetch hfresh with hfault | hclean
  · exact hfault
  · obtain ⟨τ1, hs1, hoff1, hon1⟩ := hclean
    have hag1 : ∀ y, NonFresh P y → τ1 y = σ y :=
      fun y hy => (hoff1 y (fun e _ => hy e)).trans (hagree y hy)
    -- the rewrite gate is impossible at a faulting node
    have hgfalse : (isNumbered e0 && (recoverable P S nd).contains e0) = false := by
      cases h : (isNumbered e0 && (recoverable P S nd).contains e0) with
      | false => rfl
      | true =>
        exfalso
        rw [Bool.and_eq_true] at h
        have hrecov : e0 ∈ recoverable P S nd := Std.HashSet.contains_iff_mem.mp h.2
        rcases replace_covered S hg hf h.1 hrecov hcov with hM | hia
        · have := Holds_iff.1 (hHolds e0 hM); rw [hnone] at this; exact absurd this (by simp)
        · have := hon1 e0 (Assignments.mem_toList.2 hia)
          rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs (Assignments.mem_toList.2 hia)) hagree,
              hnone] at this
          exact absurd this (by simp)
    have hctl : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.assign x e0 (if (insertAfter P S nd).toList.isEmpty then blockOff P S next
            else blockOff P S nd + (insertBefore P S nd).toList.length + 1)) := by
      rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_neg (by simpa using hgfalse)]
    refine ⟨⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩, hs1, x, e0, _, hctl, ?_⟩
    rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
      (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
    exact hnone

/-! ## Block-level fault-or-clean runners

`entryBlock_faultOr`/`exitBlock_faultOr` run a block's entry/exit chain *fault-aware*: either the target
reaches a `Faulting` config, or the chain completes with the same clean output as `entry_block`/
`exitBlock_exec` (whose no-fault hypotheses these drop). They are the per-step engine of the forward fault
simulation `sim_fault`. -/

/-- Fault-aware entry block: either faults, or lands at the control slot with `entry_block`'s facts. -/
theorem entryBlock_faultOr {P : Program} (S : LcmSpec P) {nd : Node} (hi : nd < P.size)
    {dσ cσ : Store} {M : Assignments}
    (hagree : ∀ x, NonFresh P x → dσ x = cσ x)
    (hHolds : ∀ e ∈ M, Holds dσ cσ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P) :
    (∃ df, Steps (transform P S) ⟨blockOff P S nd, dσ⟩ df ∧ Faulting (transform P S) df)
    ∨ (∃ τ1, Steps (transform P S) ⟨blockOff P S nd, dσ⟩
              ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          ∧ (∀ x, NonFresh P x → τ1 x = cσ x)
          ∧ (∀ e, (e ∈ M ∨ e ∈ insertBefore P S nd) → Holds τ1 cσ (tempFor P e) e)) := by
  have hdist : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertBefore_mem_allExprs he))
      (Assignments.mem_toList.2 (insertBefore_mem_allExprs he')) heq)
  have hfresh : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertBefore_mem_allExprs he)
  have hfetch : ∀ k (hk : k < (insertBefore P S nd).toList.length),
      (transform P S).fetch (blockOff P S nd + k)
        = some (.assign (tempFor P ((insertBefore P S nd).toList[k]'hk)) ((insertBefore P S nd).toList[k]'hk)
            (blockOff P S nd + k + 1)) := by
    intro k hk
    have hkb : k < (block P S nd).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (insChain P (insertBefore P S nd).toList (blockOff P S nd)).length := by
      rw [insChain_length]; exact hk
    rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]
  rcases steps_insSeg_fault P (insertBefore P S nd).toList (blockOff P S nd) dσ
      Assignments.nodup_toList hdist hfetch hfresh with hF | ⟨τ1, _, _, hon1⟩
  · exact Or.inl hF
  · exact Or.inr (entry_block S hi hagree hHolds hMsub
      (fun e he => by rw [← hon1 e he]; exact Option.some_ne_none _))

/-- Fault-aware exit block: either faults, or completes exactly as `exitBlock_exec`. -/
theorem exitBlock_faultOr {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size) {next : Node}
    (hfi : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next)) {τ : Store} :
    (∃ df, Steps (transform P S) ⟨blockOff P S i + (insertBefore P S i).toList.length + 1, τ⟩ df
        ∧ Faulting (transform P S) df)
    ∨ (∃ τ2, Steps (transform P S)
              ⟨blockOff P S i + (insertBefore P S i).toList.length + 1, τ⟩
              ⟨(if (insertAfter P S i).toList.isEmpty
                  then blockOff P S i + (insertBefore P S i).toList.length + 1
                  else blockOff P S next), τ2⟩
          ∧ (∀ v, (∀ e ∈ (insertAfter P S i).toList, tempFor P e ≠ v) → τ2 v = τ v)
          ∧ (∀ e ∈ (insertAfter P S i).toList, some (τ2 (tempFor P e)) = eval τ e)) := by
  have hdist : ∀ e ∈ (insertAfter P S i).toList, ∀ e' ∈ (insertAfter P S i).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he))
      (Assignments.mem_toList.2 (insertAfter_mem_allExprs he')) heq)
  have hfresh : ∀ e ∈ (insertAfter P S i).toList, ∀ e' ∈ (insertAfter P S i).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertAfter_mem_allExprs he)
  have hfetch : ∀ k (hk : k < (insertAfter P S i).toList.length),
      (transform P S).fetch ((blockOff P S i + (insertBefore P S i).toList.length + 1) + k)
        = some (.assign (tempFor P ((insertAfter P S i).toList[k]'hk)) ((insertAfter P S i).toList[k]'hk)
            (if k + 1 == (insertAfter P S i).toList.length then blockOff P S next
             else (blockOff P S i + (insertBefore P S i).toList.length + 1) + k + 1)) := by
    intro k hk
    have hkb : (insertBefore P S i).toList.length + 1 + k < (block P S i).length := by
      rw [block_length]; unfold blockLen
      rcases hfi with h | ⟨x, e, h⟩ <;> simp only [h] <;> omega
    rw [show (blockOff P S i + (insertBefore P S i).toList.length + 1) + k
          = blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) from by omega]
    rw [transform_fetch hi hkb, getElem?_block_exit hfi, exitChain_getElem? hk]
    rw [show blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) + 1
          = blockOff P S i + (insertBefore P S i).toList.length + 1 + k + 1 from by omega]
  exact steps_exitSeg_fault P (blockOff P S next) (insertAfter P S i).toList
    (blockOff P S i + (insertBefore P S i).toList.length + 1) τ
    Assignments.nodup_toList hdist hfetch hfresh

set_option maxHeartbeats 400000 in
/-- **`match_step_ifz_fault` — `match_step_fault`'s `ifz` case.** Either the entry chain or the taken edge chain faults (→ target
    `Faulting`), or the branch completes cleanly (`match_step_ifz` + `Cov_step_edge`). The edge chain is run
    fault-aware via `steps_exitSeg_fault`; a clean edge run contradicts the fault witness `hX`. -/
theorem match_step_ifz_fault {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    {nd : Node} {x : Var} {z nz succ : Node} {σ dσ : Store} {M : Assignments}
    (hf : P.fetch nd = some (.ifz x z nz))
    (hcond : (σ x = 0 ∧ succ = z) ∨ (σ x ≠ 0 ∧ succ = nz))
    (hagree : ∀ v, NonFresh P v → dσ v = σ v)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd)) (hcov : Cov S nd M) :
    (∃ df, Steps (transform P S) ⟨blockOff P S nd, dσ⟩ df ∧ Faulting (transform P S) df)
    ∨ (∃ d', Steps (transform P S) ⟨blockOff P S nd, dσ⟩ d'
          ∧ Match P S ⟨succ, σ⟩ d' (Mstep_edge S nd succ M) ∧ Cov S succ (Mstep_edge S nd succ M)) := by
  have hi : nd < P.size := fetch_lt hf
  rcases entryBlock_faultOr S hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
  · exact Or.inl hEF
  · have hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none := fun e he => by
      rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
    have hxnf : NonFresh P x := nonFresh_of_used hf (by simp [instrUsedVars])
    have hctlf : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.ifz x (if (insertEdge P S nd z).toList.isEmpty then blockOff P S z
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1)
                       (if (insertEdge P S nd nz).toList.isEmpty then blockOff P S nz
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1
                          + (insertEdge P S nd z).toList.length)) := by
      rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]
    by_cases hX : ∃ e ∈ (insertEdge P S nd succ).toList, eval σ e = none
    · refine Or.inl ?_
      have hnotempty : ¬((insertEdge P S nd succ).toList.isEmpty = true) := by
        obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
      have run_edge_fault : ∀ (st : Nat),
          (∀ k (hk : k < (insertEdge P S nd succ).toList.length),
            (transform P S).fetch (st + k)
              = some (.assign (tempFor P ((insertEdge P S nd succ).toList[k]'hk)) ((insertEdge P S nd succ).toList[k]'hk)
                  (if k + 1 == (insertEdge P S nd succ).toList.length then blockOff P S succ else st + k + 1))) →
          ∃ df, Steps (transform P S) ⟨st, τ1⟩ df ∧ Faulting (transform P S) df := by
        intro st hfetch
        have hdist : ∀ e ∈ (insertEdge P S nd succ).toList, ∀ e' ∈ (insertEdge P S nd succ).toList,
            e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
          hne (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs he))
            (Assignments.mem_toList.2 (insertEdge_mem_allExprs he')) heq)
        have hfresh : ∀ e ∈ (insertEdge P S nd succ).toList, ∀ e' ∈ (insertEdge P S nd succ).toList,
            exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertEdge_mem_allExprs he)
        rcases steps_exitSeg_fault P (blockOff P S succ) (insertEdge P S nd succ).toList st τ1
            Assignments.nodup_toList hdist hfetch hfresh with hF | ⟨τ2, _, _, hon2⟩
        · exact hF
        · exfalso; obtain ⟨e, he, hev⟩ := hX; have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs he) hag1, hev] at this
          exact absurd this (by simp)
      rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩ <;> subst succ
      · have hstep := Step.ifzT (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hx0)
        rw [if_neg hnotempty] at hstep
        obtain ⟨df, hsdf, hfltdf⟩ := run_edge_fault (blockOff P S nd + (insertBefore P S nd).toList.length + 1) (by
          intro k hk
          have hkb : (insertBefore P S nd).toList.length + 1 + k < (block P S nd).length := by
            rw [block_length]
            have hbl : blockLen P S nd = (insertBefore P S nd).toList.length + 1
                + ((insertEdge P S nd z).toList.length + (insertEdge P S nd nz).toList.length) := by
              simp only [blockLen, hf]
            rw [hbl]; omega
          rw [show (blockOff P S nd + (insertBefore P S nd).toList.length + 1) + k
                = blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_z hf hk, exitChain_getElem? hk,
              show blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + k) + 1
                = blockOff P S nd + (insertBefore P S nd).toList.length + 1 + k + 1 from by omega])
        exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hsdf), hfltdf⟩
      · have hstep := Step.ifzF (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hxne)
        rw [if_neg hnotempty] at hstep
        obtain ⟨df, hsdf, hfltdf⟩ :=
          run_edge_fault (blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length) (by
          intro k hk
          have hkb : (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k
              < (block P S nd).length := by
            rw [block_length]
            have hbl : blockLen P S nd = (insertBefore P S nd).toList.length + 1
                + ((insertEdge P S nd z).toList.length + (insertEdge P S nd nz).toList.length) := by
              simp only [blockLen, hf]
            rw [hbl]; omega
          rw [show (blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length) + k
                = blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_nz hf hk, exitChain_getElem? hk,
              show blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k) + 1
                = blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k + 1 from by omega])
        exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hsdf), hfltdf⟩
    · have hnfe : ∀ e ∈ (insertEdge P S nd succ).toList, eval σ e ≠ none := fun e he hev => hX ⟨e, he, hev⟩
      have hstepsrc : Step P ⟨nd, σ⟩ ⟨succ, σ⟩ := by
        rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩
        · rw [hsu]; exact Step.ifzT hf hx0
        · rw [hsu]; exact Step.ifzF hf hxne
      obtain ⟨d', hsteps, hmatch⟩ := match_step_ifz S hf hcond hagree hHolds hMsub hpa hnfσ hnfe
      refine Or.inr ⟨d', hsteps.toSteps, hmatch, ?_⟩
      show Cov S (⟨succ, σ⟩ : Config).node
        (Mstep_edge S (⟨nd, σ⟩ : Config).node (⟨succ, σ⟩ : Config).node M)
      exact Cov_step_edge S hg hstepsrc hcov

theorem match_step_fault {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c') :
    (∃ df, Steps (transform P S) d df ∧ Faulting (transform P S) df)
    ∨ (∃ d', Steps (transform P S) d d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M)
          ∧ Cov S c'.node (Mstep_edge S c.node c'.node M)) := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    have hi : nd < P.size := fetch_lt hf
    rcases entryBlock_faultOr S hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
    · exact Or.inl hEF
    · have hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none := fun e he => by
        rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
      by_cases hX : ∃ e ∈ (insertAfter P S nd).toList, eval (σ.update x vv) e = none
      · -- exit chain faults ⇒ target faults
        refine Or.inl ?_
        have hnotempty : ¬((insertAfter P S nd).toList.isEmpty = true) := by
          obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
        have hctrl : ∃ rhs, (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
              = some (.assign x rhs (if (insertAfter P S nd).toList.isEmpty then blockOff P S next
                  else blockOff P S nd + (insertBefore P S nd).toList.length + 1)) ∧ eval τ1 rhs = some vv := by
          by_cases hfired : (isNumbered e0 && (recoverable P S nd).contains e0) = true
          · refine ⟨.atom (.var (tempFor P e0)),
              by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_pos hfired], ?_⟩
            have hand : isNumbered e0 = true ∧ (recoverable P S nd).contains e0 = true := by
              simpa using hfired
            have hHe0 : Holds τ1 σ (tempFor P e0) e0 :=
              hH1 e0 (replace_covered S hg hf hand.1 (Std.HashSet.contains_iff_mem.mp hand.2) hcov)
            simp only [eval, evalAtom]; exact (Holds_iff.1 hHe0).trans hvv
          · refine ⟨e0, by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_neg hfired], ?_⟩
            rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
              (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
            exact hvv
        obtain ⟨rhs, hfetchr, hrhsv⟩ := hctrl
        have hctlstep : Step (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
            ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1.update x vv⟩ := by
          have hc := Step.assign hfetchr hrhsv; rw [if_neg hnotempty] at hc; exact hc
        have hag1' : ∀ y, NonFresh P y → (τ1.update x vv) y = (σ.update x vv) y := by
          intro y hy
          by_cases hyx : y = x
          · subst hyx; simp [Store.update]
          · simp only [Store.update, if_neg hyx]; exact hag1 y hy
        rcases exitBlock_faultOr S hi (Or.inr ⟨x, e0, hf⟩) (τ := τ1.update x vv) with hXF | ⟨τ2, _, _, hon2⟩
        · obtain ⟨df, hsdf, hfltdf⟩ := hXF
          exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hctlstep) hsdf), hfltdf⟩
        · exfalso
          obtain ⟨e, he, hev⟩ := hX
          have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1', hev] at this
          exact absurd this (by simp)
      · -- exit chain clean ⇒ full clean step via `match_step_assign`
        have hnfeσ : ∀ e ∈ (insertAfter P S nd).toList, eval (σ.update x vv) e ≠ none :=
          fun e he hev => hX ⟨e, he, hev⟩
        obtain ⟨d', hsteps, hmatch⟩ :=
          match_step_assign S wn hf hvv hagree hHolds hMsub hpa
            (fun hfired => by
              have hand : isNumbered e0 = true ∧ (recoverable P S nd).contains e0 = true := by
                simpa using hfired
              exact replace_covered S hg hf hand.1 (Std.HashSet.contains_iff_mem.mp hand.2) hcov)
            hnfσ hnfeσ
        exact Or.inr ⟨d', hsteps.toSteps, Match_union_sub hmatch (fun e he => Assignments.mem_union.mpr
          (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)]; exact he))),
          Cov_step_edge S hg (Step.assign hf hvv) hcov⟩
  | @noop nd σ next hf =>
    subst hlabel
    have hi : nd < P.size := fetch_lt hf
    rcases entryBlock_faultOr S hi hagree hHolds hMsub with hEF | ⟨τ1, hs1, hag1, hH1⟩
    · exact Or.inl hEF
    · have hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none := fun e he => by
        rw [← Holds_iff.1 (hH1 e (Or.inr (Assignments.mem_toList.1 he)))]; exact Option.some_ne_none _
      by_cases hX : ∃ e ∈ (insertAfter P S nd).toList, eval σ e = none
      · refine Or.inl ?_
        have hnotempty : ¬((insertAfter P S nd).toList.isEmpty = true) := by
          obtain ⟨e, he, _⟩ := hX; intro hemp; rw [List.isEmpty_iff.mp hemp] at he; simp at he
        have hctl : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
            = some (ctrlCmd P S nd) := ctrl_slot_fetch S hi
        have hctlstep : Step (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
            ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩ := by
          refine Step.noop ?_; rw [hctl]; simp only [ctrlCmd, hf, if_neg hnotempty]
        rcases exitBlock_faultOr S hi (Or.inl hf) (τ := τ1) with hXF | ⟨τ2, _, _, hon2⟩
        · obtain ⟨df, hsdf, hfltdf⟩ := hXF
          exact ⟨df, steps_trans hs1 (steps_trans (Steps.tail Steps.refl hctlstep) hsdf), hfltdf⟩
        · exfalso
          obtain ⟨e, he, hev⟩ := hX
          have := hon2 e he
          rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1, hev] at this
          exact absurd this (by simp)
      · have hnfeσ : ∀ e ∈ (insertAfter P S nd).toList, eval σ e ≠ none :=
          fun e he hev => hX ⟨e, he, hev⟩
        obtain ⟨d', hsteps, hmatch⟩ := match_step_noop S hf hagree hHolds hMsub hpa hnfσ hnfeσ
        exact Or.inr ⟨d', hsteps.toSteps, Match_union_sub hmatch (fun e he => Assignments.mem_union.mpr
          (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inl hf)]; exact he))),
          Cov_step_edge S hg (Step.noop hf) hcov⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz_fault S hg hf (Or.inl ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hcov
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz_fault S hg hf (Or.inr ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hcov

/-- **Forward fault simulation.** A source head-run `c ⟶* c_n` ending in a `Faulting` config, matched at
    `c`, drives the target to a `Faulting` config: each step either faults the target now
    (`match_step_fault` left) or advances cleanly and recurses; the terminal fault is `match_faulting`. -/
theorem sim_fault {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P) :
    ∀ {c c_n : Config}, StepsH P c c_n → Faulting P c_n →
    ∀ {d : Config} {M : Assignments}, Match P S c d M →
      Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) → Cov S c.node M →
      ∃ df, Steps (transform P S) d df ∧ Faulting (transform P S) df := by
  intro c c_n hrun
  induction hrun with
  | refl => intro hflt d M hm _ hcov; exact match_faulting S hg hm hcov hflt
  | @head c c1 cn hstep htail ih =>
      intro hflt d M hm hpa hcov
      rcases match_step_fault S hg wn hm hpa hcov hstep with hF | ⟨d1, hs1, hm1, hcov1⟩
      · exact hF
      · obtain ⟨df, hsdf, hfltdf⟩ := ih hflt hm1 (postpSubAnti_step S hstep hpa) hcov1
        exact ⟨df, steps_trans hs1 hsdf, hfltdf⟩

/-- **`transform_preserves_faulting` — LCM preserves faults (forward `Fault → Fault`).** On a source run
    that reaches a `Faulting` config, the transform also reaches a `Faulting` config. Fills the diagonal
    `Fault → Fault` cell of the LCM outcome table. Stated over `GateSound`, like
    `transform_preserves_halt`; the two corollaries below are the per-gate forms. -/
theorem transform_preserves_faulting {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    (wn : WellNormalized P)
    {σ : Store} {c_n : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_n) (hflt : Faulting P c_n) :
    ∃ df, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ df ∧ Faulting (transform P S) df :=
  sim_fault S hg wn (steps_toH hrun) hflt (match_init S σ) (postpSubAnti_entry S) (Cov_entry S hg)

/-- Fault preservation under the **materialization** gate — from validity alone. -/
theorem transform_preserves_faulting_mat {P : Program} (S : LcmSpec P) (hm : S.gate = .materialized)
    (wn : WellNormalized P)
    {σ : Store} {c_n : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_n) (hflt : Faulting P c_n) :
    ∃ df, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ df ∧ Faulting (transform P S) df :=
  transform_preserves_faulting S (gateSound_materialized S hm) wn hrun hflt

/-- Fault preservation under the classical **demand** gate — the original theorem, for an extremal
    bundle over a `WellNormalized` program with the `prependEntry` `noop` entry. -/
theorem transform_preserves_faulting_demand {P : Program} (S : LcmSpec P) (hd : S.gate = .demand)
    (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    {σ : Store} {c_n : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_n) (hflt : Faulting P c_n) :
    ∃ df, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ df ∧ Faulting (transform P S) df :=
  transform_preserves_faulting S (gateSound_demand S hd hS wn hen) wn hrun hflt


end BaseLanguage.Analyses.LCM
