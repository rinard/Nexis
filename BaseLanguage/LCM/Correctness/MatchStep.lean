-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness.Coverage

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## `match_step` helpers — reusable across the four control cases

The shared facts: an `allExprs` expression reads only **non-fresh** operands (so it evaluates identically in
two `NonFresh`-agreeing stores); an inserted expression is **anticipated** at its node (so the halting
continuation certifies it fault-free); and the entry `insChain` preserves `NonFresh` agreement (it writes
only fresh temps). -/

/-- An operand of an `allExprs` expression is **non-fresh** (`tempFor` temps are read by no instruction). -/
theorem allExprs_operand_nonFresh {P : Program} {e : Expr} {v : Var}
    (he : e ∈ allExprs P) (hv : exprReadsVar e v = true) : NonFresh P v := by
  obtain ⟨nd, x, next, hf⟩ := mem_allExprs he
  intro e' heq
  have hmem : v ∈ instrUsedVars (.assign x e next) := by
    simp only [instrUsedVars]; exact readsVar_imp_mem hv
  rw [← heq] at hmem
  exact tempFor_unread P e' hf hmem

/-- Two stores agreeing on every **non-fresh** variable evaluate an `allExprs` expression identically
    (its operands are all non-fresh). -/
theorem eval_eq_of_nonFresh_agree {P : Program} {d c : Store} {e : Expr}
    (he : e ∈ allExprs P) (hagree : ∀ x, NonFresh P x → d x = c x) :
    eval d e = eval c e :=
  eval_congr (fun v hv => hagree v (allExprs_operand_nonFresh he hv))

/-- An **entry-inserted** expression is anticipated at its node (`insertBefore ⊆ latestNode ⊆ postp ⊆ anti`). -/
theorem insertBefore_sub_anti {P : Program} (S : LcmSpec P) {n : Node} {e : Expr}
    (hpa : Assignments.Subset (S.ηₚ n) (S.πₐ n)) (he : e ∈ insertBefore P S n) : e ∈ S.πₐ n := by
  unfold insertBefore at he; rw [Assignments.mem_inter, Assignments.mem_sdiff] at he
  exact hpa e (latestNode_sub_postp S n e he.1.1)

/-- An **exit-inserted** expression is in the computed universe (`usedOut`'s `bound`). -/
theorem insertAfter_mem_allExprs {P : Program} {S : LcmSpec P} {i : Node} {e : Expr}
    (he : e ∈ (insertAfter P S i).toList) : e ∈ allExprs P := by
  rw [Assignments.mem_toList] at he
  unfold insertAfter at he
  cases hfi : P.fetch i with
  | none => rw [hfi] at he; simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign x e0 next => rw [hfi, Assignments.mem_inter] at he; exact S.isUsedOut.within i e (τᵤK_sub S i e he.2)
      | noop next => rw [hfi, Assignments.mem_inter] at he; exact S.isUsedOut.within i e (τᵤK_sub S i e he.2)
      | ifz x z nz => rw [hfi] at he; simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty
      | halt => rw [hfi] at he; simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty

/-- `Holds` as a value equation (the temp's value equals the source expression's value). -/
theorem Holds_iff {d c : Store} {h : Var} {e : Expr} :
    Holds d c h e ↔ some (d h) = eval c e := by
  unfold Holds; simp [eval, evalAtom]

/-- **The shared entry-block run.** Executing node `nd`'s `insChain` (under the no-fault discharge `hnf`)
    lands at the control slot with a store `τ1` that (i) still agrees with the source on every non-fresh
    variable, and (ii) makes **every temp in `M ∪ insertBefore nd` hold** its expression's source value. This is
    the common prefix of all four `match_step` control cases. -/
theorem entry_block {P : Program} (S : LcmSpec P) {nd : Node} (hi : nd < P.size)
    {dσ cσ : Store} {M : Assignments}
    (hagree : ∀ x, NonFresh P x → dσ x = cσ x)
    (hHolds : ∀ e ∈ M, Holds dσ cσ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none) :
    ∃ τ1, Steps (transform P S) ⟨blockOff P S nd, dσ⟩
            ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
        ∧ (∀ x, NonFresh P x → τ1 x = cσ x)
        ∧ (∀ e, (e ∈ M ∨ e ∈ insertBefore P S nd) → Holds τ1 cσ (tempFor P e) e) := by
  -- every inserted expression is in `allExprs` (for injectivity / freshness)
  have hmem_all : ∀ e ∈ (insertBefore P S nd).toList, e ∈ (allExprs P).toList :=
    fun e he => Assignments.mem_toList.2 (insertBefore_mem_allExprs he)
  have hdist : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' :=
    fun e he e' he' hne heq => hne (tempFor_inj P (hmem_all e he) (hmem_all e' he') heq)
  have hfresh : ∀ e ∈ (insertBefore P S nd).toList, ∀ e' ∈ (insertBefore P S nd).toList,
      exprReadsVar e (tempFor P e') = false :=
    fun e he _ _ => insert_fresh (insertBefore_mem_allExprs he)
  obtain ⟨τ1, hs1, hoff1, hon1⟩ := insBlock_exec S hi hdist hnf hfresh
  refine ⟨τ1, hs1, ?_, ?_⟩
  · -- non-fresh agreement survives (the chain writes only `tempFor` temps)
    intro x hx
    rw [hoff1 x (fun e _ => hx e), hagree x hx]
  · -- `M ∪ insertBefore` temps hold their values
    intro e hin
    have key : some (τ1 (tempFor P e)) = eval cσ e := by
      by_cases hia : e ∈ (insertBefore P S nd).toList
      · -- freshly inserted: `hon1` gives its value (= source value by agreement)
        have h1 : some (τ1 (tempFor P e)) = eval dσ e := hon1 e hia
        rw [h1, eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs hia) hagree]
      · -- carried from `M`: its temp is untouched by the chain
        have heM : e ∈ M := hin.resolve_right (fun h => hia (Assignments.mem_toList.2 h))
        have hne : ∀ e' ∈ (insertBefore P S nd).toList, tempFor P e' ≠ tempFor P e := by
          intro e' he' heq
          have hee : e' = e := tempFor_inj P (hmem_all e' he') (Assignments.mem_toList.2 (hMsub e heM)) heq
          exact hia (hee ▸ he')
        have huntouched : τ1 (tempFor P e) = dσ (tempFor P e) := hoff1 (tempFor P e) hne
        rw [huntouched]
        exact (Holds_iff.1 (hHolds e heM))
    exact Holds_iff.2 key

/-- **`match_step`, `noop` case.** A source `noop` step is matched by running node `nd`'s block (entry
    `insChain` → floated `noop` → exit `exitChain`), re-establishing `Match` at `Mstep nd M`. The store is
    unchanged across a `noop`, so the carried temps survive without a transparency argument. -/
theorem match_step_noop {P : Program} (S : LcmSpec P) {nd next : Node} {σ dσ : Store} {M : Assignments}
    (hf : P.fetch nd = some (.noop next))
    (hagree : ∀ x, NonFresh P x → dσ x = σ x)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (_hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none)
    (hnfeσ : ∀ e ∈ (insertAfter P S nd).toList, eval σ e ≠ none) :
    ∃ d', StepsPlus (transform P S) ⟨blockOff P S nd, dσ⟩ d' ∧ Match P S ⟨next, σ⟩ d' (Mstep S nd M) := by
  have hi : nd < P.size := fetch_lt hf
  -- entry-block no-fault: transferred from the source no-fault hypothesis via non-fresh agreement
  have hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he) hagree]; exact hnfσ e he
  obtain ⟨τ1, hs1, hag1, hH1⟩ := entry_block S hi hagree hHolds hMsub hnf
  have hctl : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
      = some (ctrlCmd P S nd) := ctrl_slot_fetch S hi
  -- exit-block no-fault (post-`noop` store is still `τ1`): transferred from `hnfeσ` via agreement
  have hnfe : ∀ e ∈ (insertAfter P S nd).toList, eval τ1 e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1]; exact hnfeσ e he
  have hde : ∀ e ∈ (insertAfter P S nd).toList, ∀ e' ∈ (insertAfter P S nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he))
      (Assignments.mem_toList.2 (insertAfter_mem_allExprs he')) heq)
  have hfre : ∀ e ∈ (insertAfter P S nd).toList, ∀ e' ∈ (insertAfter P S nd).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertAfter_mem_allExprs he)
  -- control + exit run to `⟨blockOff next, τF⟩`
  obtain ⟨τF, hsF, hoffF, honF⟩ :
      ∃ τF, StepsPlus (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ⟨blockOff P S next, τF⟩
          ∧ (∀ v, (∀ e ∈ (insertAfter P S nd).toList, tempFor P e ≠ v) → τF v = τ1 v)
          ∧ (∀ e ∈ (insertAfter P S nd).toList, some (τF (tempFor P e)) = eval τ1 e) := by
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · refine ⟨τ1, StepsPlus.single (Step.noop ?_), fun v _ => rfl, ?_⟩
      · rw [hctl]; simp only [ctrlCmd, hf, hemp, if_true]
      · intro e he; rw [List.isEmpty_iff.mp hemp] at he; simp at he
    · have hctlstep : Step (transform P S)
          ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩ := by
        refine Step.noop ?_; rw [hctl]; simp only [ctrlCmd, hf, if_neg hemp]
      obtain ⟨τ2, hs2, hoff2, hon2⟩ := exitBlock_exec S hi (Or.inl hf) hde hnfe hfre
      rw [if_neg hemp] at hs2
      exact ⟨τ2, stepsPlus_trans (StepsPlus.single hctlstep) hs2, hoff2, hon2⟩
  refine ⟨⟨blockOff P S next, τF⟩, steps_trans_plus hs1 hsF, rfl, ?_, ?_, ?_⟩
  · -- clause 2: non-fresh agreement (exit chain writes only fresh temps)
    intro x hx; show τF x = σ x
    rw [hoffF x (fun e _ => hx e), hag1 x hx]
  · -- clause 3: every `Mstep` temp holds its value
    intro e he
    rw [Mstep, Assignments.mem_union] at he
    show Holds τF σ (tempFor P e) e
    rcases he with hcarry | hexit
    · rw [Assignments.mem_inter, Assignments.mem_union] at hcarry
      have heall : e ∈ allExprs P :=
        hcarry.1.elim (fun h => hMsub e h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
      have hH1e : Holds τ1 σ (tempFor P e) e := hH1 e hcarry.1
      by_cases hei : e ∈ (insertAfter P S nd).toList
      · apply Holds_iff.2
        rw [honF e hei, eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs hei) hag1]
      · have hunt : τF (tempFor P e) = τ1 (tempFor P e) := by
          apply hoffF; intro e' he' heq
          exact hei ((tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he'))
            (Assignments.mem_toList.2 heall) heq) ▸ he')
        rw [Holds_iff] at hH1e ⊢; rw [hunt]; exact hH1e
    · apply Holds_iff.2
      rw [honF e (Assignments.mem_toList.2 hexit),
          eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs (Assignments.mem_toList.2 hexit)) hag1]
  · -- clause 4: `Mstep ⊆ allExprs`
    intro e he
    rw [Mstep, Assignments.mem_union] at he
    rcases he with hc | hex
    · rw [Assignments.mem_inter, Assignments.mem_union] at hc
      exact hc.1.elim (fun h => hMsub e h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
    · exact insertAfter_mem_allExprs (Assignments.mem_toList.2 hex)

/-- An edge-inserted expression is in the computed universe (`usedOut`'s `bound`). -/
theorem insertEdge_mem_allExprs {P : Program} {S : LcmSpec P} {i j : Node} {e : Expr}
    (he : e ∈ (insertEdge P S i j).toList) : e ∈ allExprs P := by
  rw [Assignments.mem_toList, insertEdge, Assignments.mem_inter] at he
  exact S.isUsedOut.within i e (τᵤK_sub S i e he.2)

/-- Indexing into the `z`-branch edge chain of an `ifz` block (after the `insChain` prefix and control). -/
theorem getElem?_block_ifz_z {P : Program} {S : LcmSpec P} {nd k : Nat} {x : Var} {z nz : Node}
    (hf : P.fetch nd = some (.ifz x z nz)) (hk : k < (insertEdge P S nd z).toList.length) :
    (block P S nd)[(insertBefore P S nd).toList.length + 1 + k]?
      = (exitChain P (insertEdge P S nd z).toList
          (blockOff P S nd + (insertBefore P S nd).toList.length + 1) (blockOff P S z))[k]? := by
  have happ : (insChain P (insertBefore P S nd).toList (blockOff P S nd)).length
      ≤ (insertBefore P S nd).toList.length + 1 + k := by rw [insChain_length]; omega
  simp only [block, hf]
  rw [List.getElem?_append_right happ, insChain_length,
      show (insertBefore P S nd).toList.length + 1 + k - (insertBefore P S nd).toList.length = k + 1 from by omega,
      List.getElem?_cons_succ, List.getElem?_append_left (by rw [exitChain_length]; exact hk)]

/-- Indexing into the `nz`-branch edge chain of an `ifz` block (after the `z`-branch chain). -/
theorem getElem?_block_ifz_nz {P : Program} {S : LcmSpec P} {nd k : Nat} {x : Var} {z nz : Node}
    (hf : P.fetch nd = some (.ifz x z nz)) (hk : k < (insertEdge P S nd nz).toList.length) :
    (block P S nd)[(insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k]?
      = (exitChain P (insertEdge P S nd nz).toList
          (blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length)
          (blockOff P S nz))[k]? := by
  have happ : (insChain P (insertBefore P S nd).toList (blockOff P S nd)).length
      ≤ (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k := by
    rw [insChain_length]; omega
  simp only [block, hf]
  rw [List.getElem?_append_right happ, insChain_length,
      show (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k
            - (insertBefore P S nd).toList.length
          = (insertEdge P S nd z).toList.length + k + 1 from by omega,
      List.getElem?_cons_succ,
      List.getElem?_append_right (by rw [exitChain_length]; omega), exitChain_length,
      show (insertEdge P S nd z).toList.length + k - (insertEdge P S nd z).toList.length = k from by omega]

/-- **`match_step`, `ifz` case.** The store is unchanged; after the entry `insChain` and the branch, the
    **taken** edge chain (`insertEdge nd succ`) materializes on the branch edge, landing at `blockOff succ`
    with `Match` at `Mstep_edge nd succ M`. Realizes edge placement on the branch edge — no critical-edge
    splitting needed. Parameterized by the taken successor and its firing condition. -/
theorem match_step_ifz {P : Program} (S : LcmSpec P) {nd : Node} {x : Var} {z nz succ : Node}
    {σ dσ : Store} {M : Assignments}
    (hf : P.fetch nd = some (.ifz x z nz))
    (hcond : (σ x = 0 ∧ succ = z) ∨ (σ x ≠ 0 ∧ succ = nz))
    (hagree : ∀ v, NonFresh P v → dσ v = σ v)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (_hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none)
    (hnfe : ∀ e ∈ (insertEdge P S nd succ).toList, eval σ e ≠ none) :
    ∃ d', StepsPlus (transform P S) ⟨blockOff P S nd, dσ⟩ d' ∧ Match P S ⟨succ, σ⟩ d' (Mstep_edge S nd succ M) := by
  have hi : nd < P.size := fetch_lt hf
  have hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he) hagree]; exact hnfσ e he
  obtain ⟨τ1, hs1, hag1, hH1⟩ := entry_block S hi hagree hHolds hMsub hnf
  have hxnf : NonFresh P x := nonFresh_of_used hf (by simp [instrUsedVars])
  -- shared assembly: any run to `⟨blockOff succ, τ2⟩` with the edge temps materialized closes `Match`.
  have finish : ∀ τ2 : Store,
      StepsPlus (transform P S) ⟨blockOff P S nd, dσ⟩ ⟨blockOff P S succ, τ2⟩ →
      (∀ v, (∀ e ∈ (insertEdge P S nd succ).toList, tempFor P e ≠ v) → τ2 v = τ1 v) →
      (∀ e ∈ (insertEdge P S nd succ).toList, some (τ2 (tempFor P e)) = eval τ1 e) →
      ∃ d', StepsPlus (transform P S) ⟨blockOff P S nd, dσ⟩ d'
          ∧ Match P S ⟨succ, σ⟩ d' (Mstep_edge S nd succ M) := by
    intro τ2 hrun hag2 hon2
    refine ⟨⟨blockOff P S succ, τ2⟩, hrun, rfl, ?_, ?_, ?_⟩
    · intro v hv; show τ2 v = σ v
      rw [hag2 v (fun e _ => hv e)]; exact hag1 v hv
    · intro e he
      show Holds τ2 σ (tempFor P e) e
      by_cases hie : e ∈ (insertEdge P S nd succ).toList
      · rw [Holds_iff, hon2 e hie, eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs hie) hag1]
      · have heMstep : e ∈ Mstep S nd M := by
          rw [Mstep_edge, Assignments.mem_union] at he
          exact he.resolve_right (fun h => hie (Assignments.mem_toList.2 h))
        rw [Mstep, Assignments.mem_union] at heMstep
        rcases heMstep with hin | hafter
        · have hmem : e ∈ Assignments.union M (insertBefore P S nd) := (Assignments.mem_inter.mp hin).1
          have hH1e : Holds τ1 σ (tempFor P e) e := hH1 e (Assignments.mem_union.mp hmem)
          have heall : e ∈ allExprs P :=
            (Assignments.mem_union.mp hmem).elim (fun h => hMsub e h)
              (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
          rw [Holds_iff] at hH1e ⊢
          rw [hag2 (tempFor P e) (fun e'' he'' heq =>
            hie (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs he''))
              (Assignments.mem_toList.2 heall) heq ▸ he''))]
          exact hH1e
        · unfold insertAfter at hafter; rw [hf] at hafter
          simp only [Assignments.empty] at hafter; exact absurd hafter Std.HashSet.not_mem_empty
    · intro e he
      rw [Mstep_edge, Assignments.mem_union] at he
      rcases he with hms | hie
      · rw [Mstep, Assignments.mem_union] at hms
        rcases hms with hc | hafter
        · rw [Assignments.mem_inter, Assignments.mem_union] at hc
          exact hc.1.elim (fun h => hMsub e h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
        · unfold insertAfter at hafter; rw [hf] at hafter
          simp only [Assignments.empty] at hafter; exact absurd hafter Std.HashSet.not_mem_empty
      · exact insertEdge_mem_allExprs (Assignments.mem_toList.2 hie)
  -- run the taken branch's edge chain (`succ`, its chain start `st`, target `blockOff succ`).
  have run_edge : ∀ (st : Nat),
      (∀ k (hk : k < (insertEdge P S nd succ).toList.length),
        (transform P S).fetch (st + k)
          = some (.assign (tempFor P ((insertEdge P S nd succ).toList[k]'hk)) ((insertEdge P S nd succ).toList[k]'hk)
              (if k + 1 == (insertEdge P S nd succ).toList.length then blockOff P S succ else st + k + 1))) →
      ∃ τ2, Steps (transform P S) ⟨(if (insertEdge P S nd succ).toList.isEmpty then blockOff P S succ else st), τ1⟩
              ⟨blockOff P S succ, τ2⟩
          ∧ (∀ v, (∀ e ∈ (insertEdge P S nd succ).toList, tempFor P e ≠ v) → τ2 v = τ1 v)
          ∧ (∀ e ∈ (insertEdge P S nd succ).toList, some (τ2 (tempFor P e)) = eval τ1 e) := by
    intro st hfetch
    have hdist : ∀ e ∈ (insertEdge P S nd succ).toList, ∀ e' ∈ (insertEdge P S nd succ).toList,
        e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
      hne (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs he))
        (Assignments.mem_toList.2 (insertEdge_mem_allExprs he')) heq)
    have hfresh : ∀ e ∈ (insertEdge P S nd succ).toList, ∀ e' ∈ (insertEdge P S nd succ).toList,
        exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertEdge_mem_allExprs he)
    have hrec : ∀ e ∈ (insertEdge P S nd succ).toList, eval τ1 e ≠ none := fun e he => by
      rw [eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs he) hag1]; exact hnfe e he
    by_cases hemp : (insertEdge P S nd succ).toList.isEmpty = true
    · refine ⟨τ1, ?_, fun v _ => rfl, ?_⟩
      · rw [if_pos hemp]; exact Steps.refl
      · intro e he; rw [List.isEmpty_iff] at hemp; rw [hemp] at he; simp at he
    · rw [if_neg hemp]
      obtain ⟨τ2, hsteps, hag2, hon2⟩ :=
        steps_exitSeg (blockOff P S succ) (insertEdge P S nd succ).toList st τ1
          Assignments.nodup_toList hdist hfetch hrec hfresh
      rw [if_neg hemp] at hsteps
      exact ⟨τ2, hsteps, hag2, hon2⟩
  rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩
  · subst succ  -- z-branch
    have hctlf : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.ifz x (if (insertEdge P S nd z).toList.isEmpty then blockOff P S z
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1)
                       (if (insertEdge P S nd nz).toList.isEmpty then blockOff P S nz
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1
                          + (insertEdge P S nd z).toList.length)) := by
      rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]
    have hstep := Step.ifzT (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hx0)
    obtain ⟨τ2, hchain, hag2, hon2⟩ := run_edge (blockOff P S nd + (insertBefore P S nd).toList.length + 1) (by
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
    exact finish τ2 (steps_trans_plus hs1 (stepsPlus_trans (StepsPlus.single hstep) hchain)) hag2 hon2
  · subst succ  -- nz-branch
    have hctlf : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.ifz x (if (insertEdge P S nd z).toList.isEmpty then blockOff P S z
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1)
                       (if (insertEdge P S nd nz).toList.isEmpty then blockOff P S nz
                        else blockOff P S nd + (insertBefore P S nd).toList.length + 1
                          + (insertEdge P S nd z).toList.length)) := by
      rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]
    have hstep := Step.ifzF (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hxne)
    obtain ⟨τ2, hchain, hag2, hon2⟩ :=
      run_edge (blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length) (by
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
    exact finish τ2 (steps_trans_plus hs1 (stepsPlus_trans (StepsPlus.single hstep) hchain)) hag2 hon2

/-- A numbered RHS of a fetched assign is in `allExprs`. -/
theorem fetch_mem_allExprs {P : Program} {nd : Node} {x : Var} {e : Expr} {next : Node}
    (hf : P.fetch nd = some (.assign x e next)) (hn : isNumbered e = true) : e ∈ allExprs P :=
  ue_mem_allExprs (by unfold ue; rw [hf]; simp only [hn, if_true]; exact Assignments.mem_singleton.2 rfl)

/-- **Replace-branch coverage.** When the gate replaces `x := e0` by `x := tempFor e0`, the temp is
    materialized *before* the control: `e0 ∈ M ∪ insertBefore nd`. `GateSound.read` plus `Cov`.

    The two gates pay differently for `read`. `.materialized` gets it by `mem_union` on the gate itself —
    `ηₘ` is indexed at block entry, so "materialized too late" is not expressible. `.demand` has to rule
    that case out by hand, with `NoSelfRead`: a numbered computation at `nd` is transparent there, hence
    available out, hence not `earliest`, hence not in `insertAfter`. See `gateSound_demand`. -/
theorem replace_covered {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    {nd : Node} {x : Var} {e0 : Expr} {next : Node} {M : Assignments}
    (hf : P.fetch nd = some (.assign x e0 next)) (hnum : isNumbered e0 = true)
    (hrecov : e0 ∈ recoverable P S nd) (hcov : Cov S nd M) :
    e0 ∈ M ∨ e0 ∈ insertBefore P S nd :=
  (hg.read hf hnum hrecov).imp (fun h => hcov e0 h) id

/-- **`match_step`, `assign` case.** The store changes (`σ → σ.update x v`); the gate may rewrite the control
    to read a hoisted temp (coverage via `replace_covered`); carried temps survive the def of `x` by
    `transp_holds` (transparency + `x` is non-fresh); then the exit chain materializes `insertAfter` with the
    post-assign store. -/
theorem match_step_assign {P : Program} (S : LcmSpec P) (wn : WellNormalized P)
    {nd : Node} {x : Var} {e0 : Expr} {next : Node} {v : Val} {σ dσ : Store} {M : Assignments}
    (hf : P.fetch nd = some (.assign x e0 next)) (hv : eval σ e0 = some v)
    (hagree : ∀ y, NonFresh P y → dσ y = σ y)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (_hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hcovered : (isNumbered e0 && (recoverable P S nd).contains e0) = true →
        (e0 ∈ M ∨ e0 ∈ insertBefore P S nd))
    (hnfσ : ∀ e ∈ (insertBefore P S nd).toList, eval σ e ≠ none)
    (hnfeσ : ∀ e ∈ (insertAfter P S nd).toList, eval (σ.update x v) e ≠ none) :
    ∃ d', StepsPlus (transform P S) ⟨blockOff P S nd, dσ⟩ d'
        ∧ Match P S ⟨next, σ.update x v⟩ d' (Mstep S nd M) := by
  have hi : nd < P.size := fetch_lt hf
  have hstepsrc : Step P (⟨nd, σ⟩ : Config) ⟨next, σ.update x v⟩ := Step.assign hf hv
  have hxnf : NonFresh P x := nonFresh_of_def hf (by simp [instrDefVar])
  -- entry-block no-fault
  have hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he) hagree]; exact hnfσ e he
  obtain ⟨τ1, hs1, hag1, hH1⟩ := entry_block S hi hagree hHolds hMsub hnf
  -- the floated control evaluates (some rhs) to `v`, landing at `tgt`
  have hctrl : ∃ rhs, (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.assign x rhs (if (insertAfter P S nd).toList.isEmpty
            then blockOff P S next else blockOff P S nd + (insertBefore P S nd).toList.length + 1))
        ∧ eval τ1 rhs = some v := by
    by_cases hg : (isNumbered e0 && (recoverable P S nd).contains e0) = true
    · refine ⟨.atom (.var (tempFor P e0)),
        by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_pos hg], ?_⟩
      have hHe0 : Holds τ1 σ (tempFor P e0) e0 := hH1 e0 (hcovered hg)
      simp only [eval, evalAtom]; exact (Holds_iff.1 hHe0).trans hv
    · refine ⟨e0, by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_neg hg], ?_⟩
      rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
        (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
      exact hv
  obtain ⟨rhs, hfetchr, hrhsv⟩ := hctrl
  have hctlstep : Step (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
      ⟨(if (insertAfter P S nd).toList.isEmpty then blockOff P S next
          else blockOff P S nd + (insertBefore P S nd).toList.length + 1), τ1.update x v⟩ :=
    Step.assign hfetchr hrhsv
  -- post-control agreement on non-fresh vars (both stores set `x := v`)
  have hag1' : ∀ y, NonFresh P y → (τ1.update x v) y = (σ.update x v) y := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; simp [Store.update]
    · simp only [Store.update, if_neg hyx]; exact hag1 y hy
  -- exit no-fault (post-assign store)
  have hnfe : ∀ e ∈ (insertAfter P S nd).toList, eval (τ1.update x v) e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he) hag1']; exact hnfeσ e he
  have hde : ∀ e ∈ (insertAfter P S nd).toList, ∀ e' ∈ (insertAfter P S nd).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he e' he' hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he))
      (Assignments.mem_toList.2 (insertAfter_mem_allExprs he')) heq)
  have hfre : ∀ e ∈ (insertAfter P S nd).toList, ∀ e' ∈ (insertAfter P S nd).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => insert_fresh (insertAfter_mem_allExprs he)
  -- control + exit run to `⟨blockOff next, τF⟩` (base store of the off/on facts is the post-assign `τ1.update x v`)
  obtain ⟨τF, hsF, hoffF, honF⟩ :
      ∃ τF, StepsPlus (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ⟨blockOff P S next, τF⟩
          ∧ (∀ w, (∀ e ∈ (insertAfter P S nd).toList, tempFor P e ≠ w) → τF w = (τ1.update x v) w)
          ∧ (∀ e ∈ (insertAfter P S nd).toList, some (τF (tempFor P e)) = eval (τ1.update x v) e) := by
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · refine ⟨τ1.update x v, ?_, fun w _ => rfl, ?_⟩
      · have hc := hctlstep; rw [if_pos hemp] at hc; exact StepsPlus.single hc
      · intro e he; rw [List.isEmpty_iff.mp hemp] at he; simp at he
    · obtain ⟨τ2, hs2, hoff2, hon2⟩ := exitBlock_exec S hi (Or.inr ⟨x, e0, hf⟩) hde hnfe hfre
      rw [if_neg hemp] at hs2
      have hc := hctlstep; rw [if_neg hemp] at hc
      exact ⟨τ2, stepsPlus_trans (StepsPlus.single hc) hs2, hoff2, hon2⟩
  -- transparency read-off
  have htransp_read : ∀ e, e ∈ pass P nd → exprReadsVar e x = false := by
    intro e he
    unfold pass at he; rw [Assignments.mem_filter'] at he
    have h2 := he.2; unfold transpB at h2; rw [hf] at h2; simp only [instrDefVar] at h2
    simpa using h2
  refine ⟨⟨blockOff P S next, τF⟩, steps_trans_plus hs1 hsF, rfl, ?_, ?_, ?_⟩
  · -- clause 2
    intro y hy; show τF y = (σ.update x v) y
    rw [hoffF y (fun e _ => hy e), hag1' y hy]
  · -- clause 3
    intro e he
    rw [Mstep, Assignments.mem_union] at he
    show Holds τF (σ.update x v) (tempFor P e) e
    rcases he with hcarry | hexit
    · rw [Assignments.mem_inter, Assignments.mem_union] at hcarry
      have heall : e ∈ allExprs P :=
        hcarry.1.elim (fun h => hMsub e h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
      have hH1e : Holds τ1 σ (tempFor P e) e := hH1 e hcarry.1
      have hupd : Holds (τ1.update x v) (σ.update x v) (tempFor P e) e :=
        transp_holds (htransp_read e hcarry.2) (Ne.symm (hxnf e)) hH1e
      by_cases hei : e ∈ (insertAfter P S nd).toList
      · apply Holds_iff.2
        rw [honF e hei, eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs hei) hag1']
      · have hunt : τF (tempFor P e) = (τ1.update x v) (tempFor P e) := by
          apply hoffF; intro e' he' heq
          exact hei ((tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he'))
            (Assignments.mem_toList.2 heall) heq) ▸ he')
        rw [Holds_iff] at hupd ⊢; rw [hunt]; exact hupd
    · apply Holds_iff.2
      rw [honF e (Assignments.mem_toList.2 hexit),
          eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs (Assignments.mem_toList.2 hexit)) hag1']
  · -- clause 4
    intro e he
    rw [Mstep, Assignments.mem_union] at he
    rcases he with hc | hex
    · rw [Assignments.mem_inter, Assignments.mem_union] at hc
      exact hc.1.elim (fun h => hMsub e h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
    · exact insertAfter_mem_allExprs (Assignments.mem_toList.2 hex)

/-- `Match` at `M` lifts to `M ∪ N` when `N ⊆ M` (the extra members are already held). -/
theorem Match_union_sub {P : Program} {S : LcmSpec P} {c d : Config} {M N : Assignments}
    (hm : Match P S c d M) (hsub : Assignments.Subset N M) :
    Match P S c d (Assignments.union M N) := by
  obtain ⟨hl, hag, hH, hMs⟩ := hm
  exact ⟨hl, hag,
    fun e he => hH e ((Assignments.mem_union.mp he).elim id (fun h => hsub e h)),
    fun e he => hMs e ((Assignments.mem_union.mp he).elim id (fun h => hsub e h))⟩

/-- **`insertAfter ⊆ insertEdge` along a taken step.** At a `1-successor` source the two coincide
    (`insertAfter_eq_insertEdge`); at an `ifz` the exit set is empty, so the inclusion is vacuous. This is
    what lets the step-case take a *single* exit-side no-fault obligation, stated on the edge. -/
theorem insertAfter_sub_insertEdge_of_step {P : Program} (S : LcmSpec P) {c c' : Config}
    (hstep : Step P c c') {e : Expr} (he : e ∈ insertAfter P S c.node) :
    e ∈ insertEdge P S c.node c'.node := by
  cases hstep with
  | @assign nd σ x e0 next v hf hv => rw [← insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)]; exact he
  | @noop nd σ next hf => rw [← insertAfter_eq_insertEdge S (Or.inl hf)]; exact he
  | @ifzT nd σ x z nz hf _ =>
      unfold insertAfter at he; rw [hf] at he
      simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty
  | @ifzF nd σ x z nz hf _ =>
      unfold insertAfter at he; rw [hf] at he
      simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty

/-- **`match_step_core` — the simulation step-case, with the no-fault obligations as parameters.**
    A source step `c → c'` is matched by running node `c`'s block (entry `insChain` → floated control →
    the taken exit/edge chain) to the successor label, re-establishing `Match` at
    `Mstep_edge c.node c'.node M`. The coverage clause is `Cov_step_edge`. `assign`/`noop` reuse
    `match_step_{assign,noop}` (at `Mstep`) and bridge to `Mstep_edge` via `Match_union_sub` (the edge
    insert `= insertAfter ⊆ Mstep`); `ifz` uses `match_step_ifz` directly.

    The two `hnf*` hypotheses are the **only** place fault-freedom of the inserted expressions enters.
    Factoring them out is what makes the development carry *two* modes over one proof:
    * `match_step` discharges them from the **halting continuation** (`antiNoFault`: an anticipated
      expression is evaluated by the source before it halts, so it cannot fault). That certificate is
      unavailable on a non-terminating run — which is exactly why plain LCM does not preserve divergence.
    * `match_step_div` (`LCM/Divergence.lean`) discharges them **syntactically**, from `Expr.faultFree`,
      which needs no continuation and therefore also works on a divergent run. -/
theorem match_step_core {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c')
    (hnfB : ∀ e ∈ (insertBefore P S c.node).toList, eval c.store e ≠ none)
    (hnfE : ∀ e ∈ (insertEdge P S c.node c'.node).toList, eval c'.store e ≠ none) :
    ∃ d', StepsPlus (transform P S) d d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M)
        ∧ Cov S c'.node (Mstep_edge S c.node c'.node M) := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  suffices h : ∃ d', StepsPlus (transform P S) ⟨dn, dσ⟩ d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M) by
    obtain ⟨d', hsteps, hmatch⟩ := h
    exact ⟨d', hsteps, hmatch, Cov_step_edge S hg hstep hcov⟩
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_assign S wn hf hvv hagree hHolds hMsub hpa
      (fun hfired => by
        have hand : isNumbered e0 = true ∧ (recoverable P S nd).contains e0 = true := by
          simpa using hfired
        exact replace_covered S hg hf hand.1 (Std.HashSet.contains_iff_mem.mp hand.2) hcov)
      hnfB
      (fun e he => hnfE e (Assignments.mem_toList.2
        (insertAfter_sub_insertEdge_of_step S (Step.assign hf hvv) (Assignments.mem_toList.1 he))))
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)]; exact he)))⟩
  | @noop nd σ next hf =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_noop S hf hagree hHolds hMsub hpa
      hnfB
      (fun e he => hnfE e (Assignments.mem_toList.2
        (insertAfter_sub_insertEdge_of_step S (Step.noop (σ := σ) hf) (Assignments.mem_toList.1 he))))
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inl hf)]; exact he)))⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz S hf (Or.inl ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hnfB hnfE
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz S hf (Or.inr ⟨hcond, rfl⟩) hagree hHolds hMsub hpa hnfB hnfE

/-- **`match_step` — the halting-run step-case.** `match_step_core` with the two no-fault obligations
    discharged from the **halting continuation**: an inserted expression is anticipated at its node
    (`insertBefore_sub_anti` / `edgeIns_sub_anti`), and `antiNoFault` turns anticipation plus a run that
    reaches `halt` into "the source itself evaluates it, hence it does not fault". This is the certificate
    that a divergent run cannot supply; see `LCM/Divergence.lean` for the mode that replaces it. -/
theorem match_step {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments} {c_f : Config}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c')
    (hcont : StepsH P c' c_f) (hfin : Final P c_f) :
    ∃ d', StepsPlus (transform P S) d d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M)
        ∧ Cov S c'.node (Mstep_edge S c.node c'.node M) :=
  match_step_core S hg wn hm hpa hcov hstep
    (fun e he => by
      obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head hstep hcont) hfin e
        (insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he))
      rw [hw]; exact Option.some_ne_none w)
    (fun e he => by
      rw [Assignments.mem_toList, insertEdge, Assignments.mem_inter] at he
      obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e (edgeIns_sub_anti S hstep hpa he.1)
      rw [hw]; exact Option.some_ne_none w)

/-! ## The simulation base case — `Cov(P.entry) ∅` via `πᵤ(P.entry) = ∅`

`Cov(P.entry) ∅` reduces to `πᵤ(P.entry) = ∅`. With the `prependEntry` `noop` entry, the entry computes
and avails nothing, and a leastness witness (`πᵤ` with `entry ↦ ∅`) closes via the keystone +
isolation lemmas. -/

/-- A `noop` entry computes nothing: `ue(entry) = ∅`. -/
theorem ue_entry_empty {P : Program} {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) (e : Expr) :
    e ∉ ue P P.entry := by
  simp only [ue, hen]; exact Std.HashSet.not_mem_empty

/-- A `noop` entry avails nothing: `availableOut(entry) = ∅`. -/
theorem availOut_entry_empty {P : Program} (S : LcmSpec P) {ne : Node}
    (hen : P.fetch P.entry = some (.noop ne)) (e : Expr) : e ∉ availableOut P S.ηₐ P.entry := by
  unfold availableOut; rw [Assignments.mem_union]
  rintro (hde | hai)
  · rw [de, Assignments.mem_inter] at hde
    simp only [ue, hen] at hde
    exact Std.HashSet.not_mem_empty hde.1
  · rw [Assignments.mem_inter] at hai
    have hs := S.isAvail.seed e hai.1
    simp only [entrySeed, Assignments.empty] at hs
    exact Std.HashSet.not_mem_empty hs

/-- Every demanded expr at the entry's successor `c'` is *placed* — at `latestNode(c')` or on the entry edge
    `latestEdge(entry,c')` (keystone + the (b) entry special-case + isolation lemmas). -/
theorem used_entrySucc_placed {P : Program} (S : LcmSpec P) (hS : Extremal S)
    (havoutE : ∀ e, e ∉ availableOut P S.ηₐ P.entry)
    {cE c' : Config} (hstep : Step P cE c') (hE : cE.node = P.entry)
    {e : Expr} (he : e ∈ S.πᵤ c'.node) :
    e ∈ Assignments.union (latestNode P S.ηₚ S.τₚ c'.node)
          (latestEdge P S.πₐ S.ηₐ S.ηₚ cE.node c'.node) := by
  have heall : e ∈ allExprs P := S.isUsed.within c'.node e he
  have hnav : e ∉ S.ηₐ c'.node := fun h =>
    havoutE e (hE ▸ S.isAvail.update cE c' hstep e h)
  have hanti : e ∈ S.πₐ c'.node :=
    used_diff_avail_sub_anti S hS c'.node e (Assignments.mem_sdiff.mpr ⟨he, hnav⟩)
  have hearl : e ∈ earliest P S.πₐ S.ηₐ cE.node c'.node := by
    unfold earliest
    rw [hE, if_pos rfl, Assignments.mem_inter, Assignments.mem_inter]
    exact ⟨⟨hanti, Assignments.mem_sdiff.mpr ⟨heall, havoutE e⟩⟩, heall⟩
  rw [Assignments.mem_union]
  by_cases hpostp : e ∈ S.ηₚ c'.node
  · refine Or.inl ?_
    by_cases hlat : e ∈ latestNode P S.ηₚ S.τₚ c'.node
    · exact hlat
    · obtain ⟨hnue, htau⟩ := postp_not_latestNode S hpostp heall hlat
      exact absurd he (tauP_not_used S hS htau hnue hlat)
  · exact Or.inr (Assignments.mem_sdiff.mpr ⟨Assignments.mem_union.mpr (Or.inl hearl), hpostp⟩)

/-- **Base case: `used(P.entry) = ∅`** (hence `Cov(P.entry) ∅`). Leastness witness `used` with
    `entry ↦ ∅`; its only non-trivial `predict` is `used_entrySucc_placed`; steps *into* the entry are
    ruled out by `EntryNoIncoming`. -/
theorem used_entry_empty {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) (e : Expr) : e ∉ S.πᵤ P.entry := by
  have havoutE : ∀ e, e ∉ availableOut P S.ηₐ P.entry := availOut_entry_empty S hen
  have hw : Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ)
      (fun m => if m = P.entry then Assignments.empty else S.πᵤ m) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep e' he'
      have hc'ne : c'.node ≠ P.entry := fun h => wn.entryNoIncoming c.node (h ▸ step_succ_mem hstep)
      rw [if_neg hc'ne] at he'
      rw [Assignments.mem_union, Assignments.mem_union]
      by_cases hc : c.node = P.entry
      · have hpl := used_entrySucc_placed S hS havoutE hstep hc he'
        rw [Assignments.mem_union] at hpl
        exact hpl.elim (fun hl => Or.inr (Or.inl hl)) (fun hed => Or.inr (Or.inr hed))
      · rw [if_neg hc]
        have hp := S.isUsed.predict c c' hstep e' he'
        rwa [Assignments.mem_union, Assignments.mem_union] at hp
    · intro m e' he'
      by_cases hm : m = P.entry
      · subst hm; exact absurd (Assignments.mem_sdiff.mp he').1 (ue_entry_empty hen e')
      · rw [if_neg hm]; exact S.isUsed.check m e' he'
    · intro m e' he'
      by_cases hm : m = P.entry
      · rw [if_pos hm] at he'; exact absurd he' Std.HashSet.not_mem_empty
      · rw [if_neg hm] at he'; exact S.isUsed.within m e' he'
  intro hu
  have hle := hS.πᵤ _ hw P.entry e hu
  rw [if_pos rfl] at hle
  exact Std.HashSet.not_mem_empty hle

/-! ## The two gates, measured against each other

Choosing `.materialized` over `.demand` costs no optimization power, and this is the theorem that says
so. Everything the classical `πᵤ` gate admitted at `n` — bar what `n`'s own chains materialize, which the
gate names separately — the materialization ghost already admits.

It is proved by **greatest-ness of `ηₘ`** (`ExtremalMat`): the classical demand set is *itself* a valid
`Materialized`, so the greatest one contains it. Its `update` obligation is precisely `demand_step_edge`
(the classical coverage maintenance), read at `M := demandSet S c.node` where the hypothesis is
reflexivity; its `seed` obligation is `used_entry_empty`.

Note which side of the ledger this sits on. `Extremal S`, `ExtremalMat S`, `WellNormalized P` and the
`prependEntry` `noop` entry are hypotheses of **correctness** for the `.demand` gate. For
`.materialized` they are hypotheses of *completeness* only — of the claim that the cheaper gate is no
weaker — which is an optimality question. Correctness under `.materialized` sees none of them. -/

/-- **`demandSet ⊆ ηₘ`** — the classical demand gate is subsumed by the materialization gate. -/
theorem demand_materialized {P : Program} (S : LcmSpec P) (hS : Extremal S) (hM : ExtremalMat S)
    (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) (n : Node) :
    Assignments.Subset (demandSet S n) (S.ηₘ n) := by
  refine hM.ηₘ (demandSet S) ⟨?_, ?_, ?_⟩ n
  · -- update: the old coverage maintenance, at `M := demandSet S c.node`
    intro c c' hstep e he
    have hstepped :=
      demand_step_edge S hS wn hstep (M := demandSet S c.node) Assignments.subset_refl e he
    rcases Assignments.mem_union.mp hstepped with hms | hedge
    · rcases Assignments.mem_union.mp hms with hbody | hafter
      · obtain ⟨hmb, hpass⟩ := Assignments.mem_inter.mp hbody
        rcases Assignments.mem_union.mp hmb with hM | hib
        · -- the carry: `demandSet c ∩ pass c ⊆ demandSet c ∖ notPass c`
          refine Assignments.mem_union.mpr (Or.inr (Assignments.mem_sdiff.mpr ⟨hM, ?_⟩))
          intro hnp; exact (Assignments.mem_sdiff.mp hnp).2 hpass
        · -- the entry chain, surviving `c`'s instruction: `insertBefore c ∩ pass c ⊆ nodeGen ∩ pass c`
          obtain ⟨hdiff, hτK⟩ := Assignments.mem_inter.mp hib
          exact Assignments.mem_union.mpr (Or.inl (Assignments.mem_union.mpr (Or.inr
            (Assignments.mem_inter.mpr
              ⟨Assignments.mem_inter.mpr ⟨hdiff, τᵤK_sub S c.node e hτK⟩, hpass⟩))))
      · -- the exit chain is the taken edge's chain
        obtain ⟨hlat, hτK⟩ :=
          Assignments.mem_inter.mp (insertAfter_sub_insertEdge_of_step S hstep hafter)
        exact Assignments.mem_union.mpr (Or.inl (Assignments.mem_union.mpr (Or.inl
          (Assignments.mem_inter.mpr ⟨hlat, τᵤK_sub S c.node e hτK⟩))))
    · obtain ⟨hlat, hτK⟩ := Assignments.mem_inter.mp hedge
      exact Assignments.mem_union.mpr (Or.inl (Assignments.mem_union.mpr (Or.inl
        (Assignments.mem_inter.mpr ⟨hlat, τᵤK_sub S c.node e hτK⟩))))
  · -- seed: nothing is demanded at the entry
    intro e he
    exact absurd (πᵤK_sub S _ e (mem_demandSet.mp he).1.1) (used_entry_empty S hS wn hen e)
  · intro m e he
    exact S.isUsed.within m e (πᵤK_sub S m e (mem_demandSet.mp he).1.1)

/-- **`GateComplete` for the materialization gate.** The filtered form of `demand_materialized`: `keep`
    travels with the demand, so the covered set subsumes the classical one too. This is what lets the
    eval-count development run over *either* gate — see `keptUse_latestNode`. -/
theorem gateComplete_materialized {P : Program} (S : LcmSpec P) (hm : S.gate = .materialized)
    (hS : Extremal S) (hM : ExtremalMat S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) : GateComplete S := by
  intro n e he
  rw [covSet_mat hm]
  exact mem_ηₘK.mpr ⟨demand_materialized S hS hM wn hen n e he,
    (mem_πᵤK.mp (mem_demandSet.mp he).1.1).2⟩

/-- **A kept numbered computation is on the latest frontier.** If the replace gate declines to rewrite
    `x := e` at `n`, then `e ∈ latestNode n` — so `n` is where the placement wants `e` anyway, and the
    kept computation is not a redundant one.

    This is the shape the eval-count development reads off the gate, and it is stated over `GateComplete`
    so it runs under **either** `GateMode`. Under `.demand` that hypothesis is definitional
    (`gateComplete_demand`) and this is the classical argument: "not recoverable" gives "not demanded"
    directly, and `Used.check` finishes it. Under `.materialized` it is `gateComplete_materialized`, and
    the step goes the other way round — `Used.check` first, then `demand_materialized` to show the
    materialization gate would have fired. `NoSelfRead` rules out the remaining escape under both, that
    `e` is materialized by `n`'s own *exit* chain, which is too late to read from `n`'s control. -/
theorem keptUse_latestNode {P : Program} (S : LcmSpec P) (hgc : GateComplete S)
    (wn : WellNormalized P) {n : Node} {e : Expr}
    (hue : e ∈ ue P n) (hkeep : S.keep e = true) (hnr : e ∉ recoverable P S n) :
    e ∈ latestNode P S.ηₚ S.τₚ n := by
  by_cases hl : e ∈ latestNode P S.ηₚ S.τₚ n
  · exact hl
  exfalso
  obtain ⟨x, next, hf, hnum⟩ := mem_ue hue
  have hnsr : exprReadsVar e x = false := wn.noSelfRead hf hnum
  have hde : e ∈ de P n := Assignments.mem_inter.mpr ⟨hue, ue_sub_transp wn hue⟩
  -- `e` cannot be materialized by `n`'s exit chain: it is available out of `n`, hence not `earliest`,
  -- and it is computed at `n`, hence not the transparent carry.
  have hnie : e ∉ insertAfter P S n := by
    intro hin
    unfold insertAfter at hin; rw [hf, Assignments.mem_inter] at hin
    rcases Assignments.mem_union.mp (Assignments.mem_sdiff.mp hin.1).1 with hear | hcarry
    · unfold earliest at hear; rw [Assignments.mem_inter, Assignments.mem_inter] at hear
      have hnav : e ∉ availableOut P S.ηₐ n := by
        have := hear.1.2; unfold compl at this; exact (Assignments.mem_sdiff.mp this).2
      exact hnav (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde)
    · exact (Assignments.mem_sdiff.mp hcarry).2 hue
  exact hnr (covSet_sub_recoverable S n e (hgc n e (mem_demandSet.mpr
    ⟨⟨mem_πᵤK.mpr ⟨S.isUsed.check n e (Assignments.mem_sdiff.mpr ⟨hue, hl⟩), hkeep⟩,
      fun hib => hnr (mem_recoverable.mpr (Or.inr hib))⟩,
     insertAfter_eq_insertOut S (Or.inr ⟨x, e, hf⟩) ▸ hnie⟩)))

/-! ## `GateSound` for the classical `.demand` gate

This is the price of reading a **least** ghost, itemised. Each of the three fields needs something the
materialization gate gets for free:

* `entry` needs `πᵤ(entry) = ∅` — `used_entry_empty`, a *leastness witness* (`Extremal S`, plus the
  `prependEntry` `noop` entry to know the entry computes and avails nothing);
* `step` is `demand_step_edge`, the classical coverage maintenance, which consumes `used_decomp`,
  `killed_in_insertAfter` and `latestOut_used_succ_sub_insertEdge` — all leastness arguments;
* `read` needs `NoSelfRead` (a `WellNormalized` field) to rule out the temp being materialized by the
  node's own *exit* chain, after the control that would read it. `ηₘ` is indexed at block entry, so for
  `.materialized` that case does not arise at all. -/

theorem covSet_demand {P : Program} {S : LcmSpec P} (hd : S.gate = .demand) (n : Node) :
    covSet S n = demandSet S n := by unfold covSet; rw [hd]

/-- **`GateSound` for the demand gate, from extremality.** The classical LCM correctness argument,
    unchanged in content and repackaged as the three obligations the simulation actually uses. -/
theorem gateSound_demand {P : Program} (S : LcmSpec P) (hd : S.gate = .demand)
    (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) : GateSound P S where
  entry := by
    intro e he
    rw [covSet_demand hd] at he
    exact absurd (πᵤK_sub S _ e (mem_demandSet.mp he).1.1) (used_entry_empty S hS wn hen e)
  step := by
    intro c c' hstep e he
    rw [covSet_demand hd] at he ⊢
    have hstepped :=
      demand_step_edge S hS wn hstep (M := demandSet S c.node) Assignments.subset_refl e he
    rcases Assignments.mem_union.mp hstepped with hms | hedge
    · rcases Assignments.mem_union.mp hms with hbody | hafter
      · obtain ⟨hmb, hpass⟩ := Assignments.mem_inter.mp hbody
        exact (Assignments.mem_union.mp hmb).elim
          (fun hM => Or.inr (Or.inr (Or.inr ⟨hM, hpass⟩)))
          (fun hib => Or.inr (Or.inr (Or.inl ⟨hib, hpass⟩)))
      · exact Or.inr (Or.inl hafter)
    · exact Or.inl hedge
  read := by
    intro nd x e0 next hf hnum hrecov
    rw [covSet_demand hd]
    rcases mem_recoverable.mp hrecov with hused | hia
    · by_cases hia : e0 ∈ insertBefore P S nd
      · exact Or.inr hia
      -- `e0` is computed at `nd` and transparent there (`NoSelfRead`), so it is available out of `nd`,
      -- hence not `earliest`, hence not on `nd`'s exit chain — which would have been too late to read.
      · have hnsr : exprReadsVar e0 x = false := wn.noSelfRead hf hnum
        have hcomp : e0 ∈ ue P nd := by
          unfold ue; rw [hf]; simp only [hnum, if_true]; exact Assignments.mem_singleton.2 rfl
        have hde : e0 ∈ de P nd :=
          Assignments.mem_inter.mpr ⟨hcomp, ue_sub_transp wn hcomp⟩
        have hnie : e0 ∉ insertAfter P S nd := by
          intro hin
          unfold insertAfter at hin; rw [hf, Assignments.mem_inter] at hin
          rcases Assignments.mem_union.mp (Assignments.mem_sdiff.mp hin.1).1 with hear | hcarry
          · unfold earliest at hear; rw [Assignments.mem_inter, Assignments.mem_inter] at hear
            have hnav : e0 ∉ availableOut P S.ηₐ nd := by
              have := hear.1.2; unfold compl at this; exact (Assignments.mem_sdiff.mp this).2
            exact hnav (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde)
          · exact (Assignments.mem_sdiff.mp hcarry).2 hcomp
        refine Or.inl (mem_demandSet.mpr ⟨⟨?_, hia⟩,
          insertAfter_eq_insertOut S (Or.inr ⟨x, e0, hf⟩) ▸ hnie⟩)
        unfold gateSet at hused; rw [hd] at hused; exact hused
    · exact Or.inr hia

/-! ## The lift `sim` and the top-level `transform_preserves_halt`

`sim` is a forward induction on the head-recursive halting run `StepsH`: at each step `match_step` matches
the block and maintains `Match`/`Cov` (and `hpa` via `postpSubAnti_step`); at the `halt` boundary
`match_final_obs` reads off the observables. `transform_preserves_halt` instantiates it at the entry
(`match_init`, `M = ∅`, `Cov` via `used_entry_empty`, `hpa` via `postpSubAnti_entry`). -/

/-- **The forward simulation lift.** -/
theorem sim {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f → (∀ v ∈ P.obs, varIsOrig v = true) →
    ∀ {d : Config} {M : Assignments}, Match P S c d M → Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) →
      Cov S c.node M →
    ∃ d_f, Steps (transform P S) d d_f ∧ Final (transform P S) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  intro c c_f hrun
  induction hrun with
  | refl => intro hfin hobs d M hm hpa _; exact match_final_obs S hm hpa hfin hobs
  | @head c c1 cf hstep htail ih =>
      intro hfin hobs d M hm hpa hcov
      obtain ⟨d1, hsteps1, hm1, hcov1⟩ := match_step S hg wn hm hpa hcov hstep htail hfin
      obtain ⟨d_f, hsteps2, hfinf, hobsf⟩ := ih hfin hobs hm1 (postpSubAnti_step S hstep hpa) hcov1
      exact ⟨d_f, steps_trans hsteps1.toSteps hsteps2, hfinf, hobsf⟩

/-- **`transform_preserves_halt` — LCM correctness (terminating-run forward simulation).** On a halting
    source run, the transform halts with every observable agreeing.

    Stated once, over `GateSound P S` — the single obligation the replace gate owes the simulation. What
    that obligation *costs* is the whole point of the two `GateMode`s, and the two corollaries below make
    the contrast explicit:

    * `transform_preserves_halt_mat` — the `.materialized` gate, **any valid bundle**;
    * `transform_preserves_halt_demand` — the `.demand` gate, needing `Extremal S` and the `prependEntry`
      `noop` entry as well.

    `wn` survives under both, because the block-execution reasoning uses it independently of the gate. -/
theorem transform_preserves_halt {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    (wn : WellNormalized P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ d_f ∧ Final (transform P S) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v :=
  sim S hg wn (steps_toH hrun) hfin hobs (match_init S σ) (postpSubAnti_entry S) (Cov_entry S hg)

/-- **LCM correctness for the materialization gate — from validity alone.**

    No `Extremal S`, and no `prependEntry` `noop` entry. Both used to be required, and both entered at
    exactly one place: the replace gate. Reading `πᵤ` there, the proof had to know that `πᵤ` was not too
    large — a lower bound on a least fixpoint, which no clause can state, so it came in as extremality;
    and the coverage base case needed `πᵤ(entry) = ∅`, which is where the entry `noop` was used. Reading
    `ηₘ`, whose governing clause is an upper bound, both obligations *are* validity. -/
theorem transform_preserves_halt_mat {P : Program} (S : LcmSpec P) (hm : S.gate = .materialized)
    (wn : WellNormalized P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ d_f ∧ Final (transform P S) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v :=
  transform_preserves_halt S (gateSound_materialized S hm) wn hobs hrun hfin

/-- **LCM correctness for the classical demand gate — the original theorem, unchanged.** Requires an
    **extremal** bundle (extremality drives LCM down-safety — unlike PDCE, a merely valid bundle does not
    suffice: `examples/lcm-extremality/ExtremalityNeeded.lean`), over a `WellNormalized` program with the
    `prependEntry` `noop` entry. -/
theorem transform_preserves_halt_demand {P : Program} (S : LcmSpec P) (hd : S.gate = .demand)
    (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ d_f ∧ Final (transform P S) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v :=
  transform_preserves_halt S (gateSound_demand S hd hS wn hen) wn hobs hrun hfin


end BaseLanguage.Analyses.LCM
