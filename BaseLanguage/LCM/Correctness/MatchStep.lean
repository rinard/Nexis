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
      | assign x e0 next => rw [hfi, Assignments.mem_inter] at he; exact S.isUsedOut.within i e he.2
      | noop next => rw [hfi, Assignments.mem_inter] at he; exact S.isUsedOut.within i e he.2
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
    ∃ d', Steps (transform P S) ⟨blockOff P S nd, dσ⟩ d' ∧ Match P S ⟨next, σ⟩ d' (Mstep S nd M) := by
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
      ∃ τF, Steps (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ⟨blockOff P S next, τF⟩
          ∧ (∀ v, (∀ e ∈ (insertAfter P S nd).toList, tempFor P e ≠ v) → τF v = τ1 v)
          ∧ (∀ e ∈ (insertAfter P S nd).toList, some (τF (tempFor P e)) = eval τ1 e) := by
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · refine ⟨τ1, Steps.tail Steps.refl (Step.noop ?_), fun v _ => rfl, ?_⟩
      · rw [hctl]; simp only [ctrlCmd, hf, hemp, if_true]
      · intro e he; rw [List.isEmpty_iff.mp hemp] at he; simp at he
    · have hctlstep : Step (transform P S)
          ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩ := by
        refine Step.noop ?_; rw [hctl]; simp only [ctrlCmd, hf, if_neg hemp]
      obtain ⟨τ2, hs2, hoff2, hon2⟩ := exitBlock_exec S hi (Or.inl hf) hde hnfe hfre
      rw [if_neg hemp] at hs2
      exact ⟨τ2, steps_trans (Steps.tail Steps.refl hctlstep) hs2, hoff2, hon2⟩
  refine ⟨⟨blockOff P S next, τF⟩, steps_trans hs1 hsF, rfl, ?_, ?_, ?_⟩
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
  exact S.isUsedOut.within i e he.2

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
    ∃ d', Steps (transform P S) ⟨blockOff P S nd, dσ⟩ d' ∧ Match P S ⟨succ, σ⟩ d' (Mstep_edge S nd succ M) := by
  have hi : nd < P.size := fetch_lt hf
  have hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none := by
    intro e he
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he) hagree]; exact hnfσ e he
  obtain ⟨τ1, hs1, hag1, hH1⟩ := entry_block S hi hagree hHolds hMsub hnf
  have hxnf : NonFresh P x := nonFresh_of_used hf (by simp [instrUsedVars])
  -- shared assembly: any run to `⟨blockOff succ, τ2⟩` with the edge temps materialized closes `Match`.
  have finish : ∀ τ2 : Store,
      Steps (transform P S) ⟨blockOff P S nd, dσ⟩ ⟨blockOff P S succ, τ2⟩ →
      (∀ v, (∀ e ∈ (insertEdge P S nd succ).toList, tempFor P e ≠ v) → τ2 v = τ1 v) →
      (∀ e ∈ (insertEdge P S nd succ).toList, some (τ2 (tempFor P e)) = eval τ1 e) →
      ∃ d', Steps (transform P S) ⟨blockOff P S nd, dσ⟩ d'
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
    exact finish τ2 (steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hchain)) hag2 hon2
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
    exact finish τ2 (steps_trans hs1 (steps_trans (Steps.tail Steps.refl hstep) hchain)) hag2 hon2

/-- A numbered RHS of a fetched assign is in `allExprs`. -/
theorem fetch_mem_allExprs {P : Program} {nd : Node} {x : Var} {e : Expr} {next : Node}
    (hf : P.fetch nd = some (.assign x e next)) (hn : isNumbered e = true) : e ∈ allExprs P :=
  ue_mem_allExprs (by unfold ue; rw [hf]; simp only [hn, if_true]; exact Assignments.mem_singleton.2 rfl)

/-- **Replace-branch coverage.** When the gate replaces `x := e0` by `x := tempFor e0`, the
    temp is materialized *before* the control: `e0 ∈ M ∪ insertBefore nd`. If `e0 ∈ πᵤ nd ∖ insertBefore`, then
    `NoSelfRead` makes `e0` transparent at `nd` (`e0 ∈ de ⊆ availableOut ⇒ e0 ∉ earliest ⇒ e0 ∉ insertAfter`), so
    `Cov` (`πᵤ ∖ insertBefore ∖ insertAfter ⊆ M`) places it in `M`. `insertAfter` (after the control) is too
    late — `NoSelfRead` is exactly what rules out a self-reading compute landing there. -/
theorem replace_covered {P : Program} (S : LcmSpec P) (wn : WellNormalized P)
    {nd : Node} {x : Var} {e0 : Expr} {next : Node} {M : Assignments}
    (hf : P.fetch nd = some (.assign x e0 next)) (hnum : isNumbered e0 = true)
    (hrecov : e0 ∈ recoverable P S nd) (hcov : Cov S nd M) :
    e0 ∈ M ∨ e0 ∈ insertBefore P S nd := by
  rw [mem_recoverable] at hrecov
  rcases hrecov with hused | hia
  · by_cases hia : e0 ∈ insertBefore P S nd
    · exact Or.inr hia
    · have hnsr : exprReadsVar e0 x = false := wn.noSelfRead hf hnum
      have heall : e0 ∈ allExprs P := fetch_mem_allExprs hf hnum
      have htransp : e0 ∈ pass P nd := by
        unfold pass; rw [Assignments.mem_filter']
        exact ⟨heall, by simp [transpB, hf, instrDefVar, hnsr]⟩
      have hcomp : e0 ∈ ue P nd := by
        unfold ue; rw [hf]; simp only [hnum, if_true]; exact Assignments.mem_singleton.2 rfl
      have hde : e0 ∈ de P nd := Assignments.mem_inter.mpr ⟨hcomp, htransp⟩
      have hnie : e0 ∉ insertAfter P S nd := by
        intro hin
        unfold insertAfter at hin; rw [hf, Assignments.mem_inter] at hin
        rcases Assignments.mem_union.mp (Assignments.mem_sdiff.mp hin.1).1 with hear | hcarry
        · unfold earliest at hear; rw [Assignments.mem_inter, Assignments.mem_inter] at hear
          have hnav : e0 ∉ availableOut P S.ηₐ nd := by
            have := hear.1.2; unfold compl at this; exact (Assignments.mem_sdiff.mp this).2
          exact hnav (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde)
        · exact (Assignments.mem_sdiff.mp hcarry).2 hcomp
      exact Or.inl (hcov e0 (Assignments.mem_sdiff.mpr ⟨Assignments.mem_sdiff.mpr ⟨hused, hia⟩,
        insertAfter_eq_insertOut S (Or.inr ⟨x, e0, hf⟩) ▸ hnie⟩))
  · exact Or.inr hia

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
    ∃ d', Steps (transform P S) ⟨blockOff P S nd, dσ⟩ d'
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
      ∃ τF, Steps (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ⟨blockOff P S next, τF⟩
          ∧ (∀ w, (∀ e ∈ (insertAfter P S nd).toList, tempFor P e ≠ w) → τF w = (τ1.update x v) w)
          ∧ (∀ e ∈ (insertAfter P S nd).toList, some (τF (tempFor P e)) = eval (τ1.update x v) e) := by
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · refine ⟨τ1.update x v, ?_, fun w _ => rfl, ?_⟩
      · have hc := hctlstep; rw [if_pos hemp] at hc; exact Steps.tail Steps.refl hc
      · intro e he; rw [List.isEmpty_iff.mp hemp] at he; simp at he
    · obtain ⟨τ2, hs2, hoff2, hon2⟩ := exitBlock_exec S hi (Or.inr ⟨x, e0, hf⟩) hde hnfe hfre
      rw [if_neg hemp] at hs2
      have hc := hctlstep; rw [if_neg hemp] at hc
      exact ⟨τ2, steps_trans (Steps.tail Steps.refl hc) hs2, hoff2, hon2⟩
  -- transparency read-off
  have htransp_read : ∀ e, e ∈ pass P nd → exprReadsVar e x = false := by
    intro e he
    unfold pass at he; rw [Assignments.mem_filter'] at he
    have h2 := he.2; unfold transpB at h2; rw [hf] at h2; simp only [instrDefVar] at h2
    simpa using h2
  refine ⟨⟨blockOff P S next, τF⟩, steps_trans hs1 hsF, rfl, ?_, ?_, ?_⟩
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

/-- **`match_step` — the simulation step-case.** A source step `c → c'` is matched by running node `c`'s
    block (entry `insChain` → floated control → the taken exit/edge chain) to the successor label,
    re-establishing `Match` at `Mstep_edge c.node c'.node M`. The coverage clause is `Cov_step_edge`;
    the halting continuation `hcont` certifies every inserted expression fault-free
    (`antiNoFault`). `assign`/`noop` reuse `match_step_{assign,noop}` (at `Mstep`) and bridge to `Mstep_edge`
    via `Match_union_sub` (the edge insert `= insertAfter ⊆ Mstep`); `ifz` uses `match_step_ifz` directly. -/
theorem match_step {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' d : Config} {M : Assignments} {c_f : Config}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c')
    (hcont : StepsH P c' c_f) (hfin : Final P c_f) :
    ∃ d', Steps (transform P S) d d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M)
        ∧ Cov S c'.node (Mstep_edge S c.node c'.node M) := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  suffices h : ∃ d', Steps (transform P S) ⟨dn, dσ⟩ d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M) by
    obtain ⟨d', hsteps, hmatch⟩ := h
    exact ⟨d', hsteps, hmatch, Cov_step_edge S hS wn hstep hcov⟩
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_assign S wn hf hvv hagree hHolds hMsub hpa
      (fun hg => by
        have hand : isNumbered e0 = true ∧ (recoverable P S nd).contains e0 = true := by simpa using hg
        exact replace_covered S wn hf hand.1 (Std.HashSet.contains_iff_mem.mp hand.2) hcov)
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head (Step.assign hf hvv) hcont) hfin e
          (insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hanti : e ∈ S.πₐ next := by
          rw [Assignments.mem_toList] at he
          unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he
          exact edgeIns_sub_anti S (Step.assign hf hvv) hpa he.1
        obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e hanti; rw [hw]; exact Option.some_ne_none w)
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)]; exact he)))⟩
  | @noop nd σ next hf =>
    subst hlabel
    obtain ⟨d', hs, hm'⟩ := match_step_noop S hf hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head (Step.noop hf) hcont) hfin e
          (insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hanti : e ∈ S.πₐ next := by
          rw [Assignments.mem_toList] at he
          unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he
          exact edgeIns_sub_anti S (Step.noop (σ := σ) hf) hpa he.1
        obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e hanti; rw [hw]; exact Option.some_ne_none w)
    exact ⟨d', hs, Match_union_sub hm' (fun e he => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inl hf)]; exact he)))⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz S hf (Or.inl ⟨hcond, rfl⟩) hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head (Step.ifzT hf hcond) hcont) hfin e
          (insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd z :=
          (Assignments.mem_inter.mp (Assignments.mem_toList.1 he)).1
        obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e (edgeIns_sub_anti S (Step.ifzT hf hcond) hpa hedge)
        rw [hw]; exact Option.some_ne_none w)
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact match_step_ifz S hf (Or.inr ⟨hcond, rfl⟩) hagree hHolds hMsub hpa
      (fun e he => by
        obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head (Step.ifzF hf hcond) hcont) hfin e
          (insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he)); rw [hw]; exact Option.some_ne_none w)
      (fun e he => by
        have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd nz :=
          (Assignments.mem_inter.mp (Assignments.mem_toList.1 he)).1
        obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e (edgeIns_sub_anti S (Step.ifzF hf hcond) hpa hedge)
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

/-! ## The lift `sim` and the top-level `transform_preserves_halt`

`sim` is a forward induction on the head-recursive halting run `StepsH`: at each step `match_step` matches
the block and maintains `Match`/`Cov` (and `hpa` via `postpSubAnti_step`); at the `halt` boundary
`match_final_obs` reads off the observables. `transform_preserves_halt` instantiates it at the entry
(`match_init`, `M = ∅`, `Cov` via `used_entry_empty`, `hpa` via `postpSubAnti_entry`). -/

/-- **The forward simulation lift.** -/
theorem sim {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) :
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
      obtain ⟨d1, hsteps1, hm1, hcov1⟩ := match_step S hS wn hm hpa hcov hstep htail hfin
      obtain ⟨d_f, hsteps2, hfinf, hobsf⟩ := ih hfin hobs hm1 (postpSubAnti_step S hstep hpa) hcov1
      exact ⟨d_f, steps_trans hsteps1 hsteps2, hfinf, hobsf⟩

/-- **`transform_preserves_halt` — LCM correctness (terminating-run forward simulation).** On a halting
    source run, the transform halts with every observable agreeing. Requires an **extremal** bundle `S`
    (extremality drives LCM down-safety — unlike PDCE, a merely valid bundle does not suffice), over a
    `WellNormalized` program with the `prependEntry` `noop` entry. -/
theorem transform_preserves_halt {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ d_f ∧ Final (transform P S) d_f
         ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  have hcov : Cov S (⟨P.entry, σ⟩ : Config).node Assignments.empty := by
    intro e he
    rw [Assignments.mem_sdiff, Assignments.mem_sdiff] at he
    exact absurd he.1.1 (used_entry_empty S hS wn hen e)
  exact sim S hS wn (steps_toH hrun) hfin hobs (match_init S σ) (postpSubAnti_entry S) hcov


end BaseLanguage.Analyses.LCM
