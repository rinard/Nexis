-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.LCM.LayoutEval
import BaseLanguage.IR.Cost

/-!
# Per-block eval-count fold (`block_evalCount`)

The eval-count optimality theorem (`evalCount (transform P S) ≤ every P'`) folds the operational trace over
the source run's blocks. This file builds the **fuel-level** half of that fold: the block executors
(`insBlock_exec`/`exitBlock_exec`) are **relational** (`Steps`), but `evalCount`/`runNodes` are **fuel-based**
(`step1`/`run`), so the straight-line `insChain`/`exitChain` are re-run at the fuel level, tracking the count.

The decisive structural fact: a block's *internal* node-path (the slots it visits over `blockLen i` fuel) is
the **consecutive slot list** `[blockOff i, …, blockOff i + blockLen i - 1]`, independent of the control type
and store (the branch/jump only chooses where it lands *after* the block). So the per-block eval count is the
sum of three gate-attributable terms:
`evalCount(block i) = [e ∈ insertBefore i] + [kept-ctrl computes e] + [e ∈ insertAfter i]`.

`run`/`evalCount`/`runNodes` are projections of `step1` (`IR/Cost`); everything reads `S` (placements) + the
layout.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-! ## A nodup filter-count helper

For a `Nodup` list, the number of elements `beq`-equal to a fixed `e` is `1` if `e ∈ l`, else `0`. This is
how a chain's raw `(m.filter (·==e)).length` collapses to the `Assignments`-membership indicator the gate uses. -/

theorem count_filter_beq_nodup {l : List Expr} (hnd : l.Nodup) (e : Expr) :
    (l.filter (fun x => x == e)).length = if e ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      rw [List.filter_cons]
      have hrest_nd : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hnotin : a ∉ rest := (List.nodup_cons.mp hnd).1
      by_cases hae : a = e
      · subst hae
        rw [if_pos (beq_self_eq_true a), List.length_cons, ih hrest_nd]
        rw [if_neg hnotin, if_pos (List.mem_cons_self ..)]
      · have hbeq : (a == e) = false := by
          rw [beq_eq_false_iff_ne]; exact hae
        simp only [hbeq, Bool.false_eq_true, if_false]
        rw [ih hrest_nd]
        by_cases he : e ∈ rest
        · rw [if_pos he, if_pos (List.mem_cons_of_mem _ he)]
        · rw [if_neg he, if_neg (by rw [List.mem_cons]; rintro (h | h); exact hae h.symm; exact he h)]

/-! ## Fuel-level `insChain` executor (entry materialization)

The `run`/`evalCount` analogue of `steps_insSeg`: laid out as `tempFor e := e` at consecutive slots
`s0, s0+1, …` (each jumping to the next slot), the chain runs straight-line over `m.length` fuel from
`⟨s0,τ⟩` to `⟨s0 + m.length, τ'⟩` (status `.next`), with the same store facts, **and** evaluates `e`
exactly `(m.filter (·==e)).length` times. -/

theorem run_insChain {Q P : Program} (e : Expr) :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → tempFor P a ≠ tempFor P b) →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk) (s0 + k + 1))) →
    (∀ a ∈ m, eval τ a ≠ none) →
    (∀ a ∈ m, ∀ b ∈ m, exprReadsVar a (tempFor P b) = false) →
    ∃ τ', run Q ⟨s0, τ⟩ m.length = (⟨s0 + m.length, τ'⟩, .next ⟨s0 + m.length, τ'⟩)
        ∧ (∀ v, (∀ a ∈ m, tempFor P a ≠ v) → τ' v = τ v)
        ∧ (∀ a ∈ m, some (τ' (tempFor P a)) = eval τ a)
        ∧ evalCount Q e ⟨s0, τ⟩ m.length = (m.filter (fun x => x == e)).length := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _ _
      exact ⟨τ, by simp [run], fun v _ => rfl, fun a h => by simp at h, by simp [evalCount]⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hrec hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨va, hva⟩ : ∃ v, eval τ a = some v := Option.ne_none_iff_exists'.mp (hrec a ha_mem)
      have hfetch0 : Q.fetch s0 = some (.assign (tempFor P a) a (s0 + 1)) := by
        have := hfetch 0 (by simp); simpa using this
      have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
        simp only [step1, hfetch0, hva]
      -- assemble IH hypotheses for `rest` at base `s0+1` (identical to `steps_insSeg`)
      have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → tempFor P x ≠ tempFor P y :=
        fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      have hfetch' : ∀ k (hk : k < rest.length),
          Q.fetch ((s0 + 1) + k) = some (.assign (tempFor P (rest[k]'hk)) (rest[k]'hk) ((s0 + 1) + k + 1)) := by
        intro k hk
        have hk' : k + 1 < (a :: rest).length := by simp; omega
        have := hfetch (k + 1) hk'
        have hidx : (a :: rest)[k+1]'hk' = rest[k]'hk := by simp
        rw [hidx] at this
        rw [show s0 + 1 + k = s0 + (k + 1) from by omega]
        exact this
      have hkeep : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b = eval τ b := fun b hb =>
        eval_update_not_read (hfresh b (List.mem_cons_of_mem _ hb) a ha_mem)
      have hrec' : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b ≠ none := by
        intro b hb; rw [hkeep b hb]; exact hrec b (List.mem_cons_of_mem _ hb)
      have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, exprReadsVar x (tempFor P y) = false :=
        fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      obtain ⟨τ', hrun, hoff, hon, hcnt⟩ :=
        ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hrec' hfresh'
      refine ⟨τ', ?_, ?_, ?_, ?_⟩
      · show run Q ⟨s0, τ⟩ (rest.length + 1) = _
        rw [show run Q ⟨s0, τ⟩ (rest.length + 1) = run Q ⟨s0 + 1, τ.update (tempFor P a) va⟩ rest.length
              from by simp only [run, hstep0]]
        rw [hrun, show (s0 + 1) + rest.length = s0 + (a :: rest).length from by simp; omega]
      · intro v hv
        have hav : tempFor P a ≠ v := hv a ha_mem
        have heq : τ' v = (τ.update (tempFor P a) va) v :=
          hoff v (fun b hb => hv b (List.mem_cons_of_mem _ hb))
        rw [heq, Store.update, if_neg (fun h => hav h.symm)]
      · intro x hx
        rcases List.mem_cons.mp hx with heq | hx
        · subst heq
          have hno : ∀ b ∈ rest, tempFor P b ≠ tempFor P x :=
            fun b hb => hdist b (List.mem_cons_of_mem _ hb) x ha_mem (fun h => hnotin (h ▸ hb))
          have heq2 : τ' (tempFor P x) = (τ.update (tempFor P x) va) (tempFor P x) :=
            hoff (tempFor P x) hno
          rw [heq2, Store.update, if_pos rfl, hva]
        · rw [hon x hx, hkeep x hx]
      · show evalCount Q e ⟨s0, τ⟩ (rest.length + 1) = _
        rw [evalCount_next hstep0, hcnt]
        have hce : computesExpr Q s0 e = (a == e) := by
          simp only [computesExpr, hfetch0]
        rw [show (⟨s0, τ⟩ : Config).node = s0 from rfl, hce, List.filter_cons]
        by_cases hae : (a == e) = true
        · simp only [hae, if_true, List.length_cons]; omega
        · simp only [Bool.not_eq_true] at hae
          simp only [hae, Bool.false_eq_true, if_false, Nat.zero_add]

/-! ## Fuel-level `exitChain` executor (exit materialization)

The `run`/`evalCount` analogue of `steps_exitSeg`: identical to `run_insChain` except the **last** instruction
jumps to `target` (= `blockOff next`). A non-empty chain runs over `m.length` fuel to `⟨target, τ'⟩`; an empty
one stays at `s0`. Same store facts, and evaluates `e` exactly `(m.filter (·==e)).length` times. -/

theorem run_exitChain {Q P : Program} (e : Expr) (target : Nat) :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → tempFor P a ≠ tempFor P b) →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk)
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ a ∈ m, eval τ a ≠ none) →
    (∀ a ∈ m, ∀ b ∈ m, exprReadsVar a (tempFor P b) = false) →
    ∃ τ', run Q ⟨s0, τ⟩ m.length
            = (⟨(if m.isEmpty then s0 else target), τ'⟩, .next ⟨(if m.isEmpty then s0 else target), τ'⟩)
        ∧ (∀ v, (∀ a ∈ m, tempFor P a ≠ v) → τ' v = τ v)
        ∧ (∀ a ∈ m, some (τ' (tempFor P a)) = eval τ a)
        ∧ evalCount Q e ⟨s0, τ⟩ m.length = (m.filter (fun x => x == e)).length := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _ _
      exact ⟨τ, by simp [run], fun v _ => rfl, fun a h => by simp at h, by simp [evalCount]⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hrec hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨va, hva⟩ : ∃ v, eval τ a = some v := Option.ne_none_iff_exists'.mp (hrec a ha_mem)
      -- the per-head count step, reused in both branches once the continuation count is known
      have hcount : ∀ {t : Nat} {τ1 : Store},
          step1 Q ⟨s0, τ⟩ = .next ⟨t, τ1⟩ →
          Q.fetch s0 = some (.assign (tempFor P a) a (if rest = [] then target else s0 + 1)) →
          evalCount Q e ⟨t, τ1⟩ rest.length = (rest.filter (fun x => x == e)).length →
          evalCount Q e ⟨s0, τ⟩ (rest.length + 1) = ((a :: rest).filter (fun x => x == e)).length := by
        intro t τ1 hstep0 hf0 hcnt
        rw [evalCount_next hstep0]
        have hce : computesExpr Q s0 e = (a == e) := by simp only [computesExpr, hf0]
        rw [show (⟨s0, τ⟩ : Config).node = s0 from rfl, hce, hcnt, List.filter_cons]
        by_cases hae : (a == e) = true
        · simp only [hae, if_true, List.length_cons]; omega
        · simp only [Bool.not_eq_true] at hae
          simp only [hae, Bool.false_eq_true, if_false, Nat.zero_add]
      by_cases hre : rest = []
      · subst hre
        have hf0 : Q.fetch s0 = some (.assign (tempFor P a) a target) := by
          have := hfetch 0 (by simp); simpa using this
        have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨target, τ.update (tempFor P a) va⟩ := by
          simp only [step1, hf0, hva]
        refine ⟨τ.update (tempFor P a) va, ?_, ?_, ?_, ?_⟩
        · simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
          show run Q ⟨s0, τ⟩ 1 = _
          simp only [run, hstep0]
        · intro v hv
          rw [Store.update, if_neg (fun h => (hv a ha_mem) h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · subst heq; rw [Store.update, if_pos rfl, hva]
          · simp at hx
        · exact hcount hstep0 (by rw [if_pos rfl]; exact hf0) (by simp [evalCount])
      · have hlen2 : 1 < (a :: rest).length := by
          cases rest with | nil => exact absurd rfl hre | cons _ _ => simp
        have hf0 : Q.fetch s0 = some (.assign (tempFor P a) a (s0 + 1)) := by
          have := hfetch 0 (by simp)
          rw [if_neg (by simp; omega)] at this; simpa using this
        have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
          simp only [step1, hf0, hva]
        have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → tempFor P x ≠ tempFor P y :=
          fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        have hfetch' : ∀ k (hk : k < rest.length),
            Q.fetch ((s0 + 1) + k) = some (.assign (tempFor P (rest[k]'hk)) (rest[k]'hk)
              (if k + 1 == rest.length then target else (s0 + 1) + k + 1)) := by
          intro k hk
          have hk' : k + 1 < (a :: rest).length := by simp; omega
          have := hfetch (k + 1) hk'
          have hidx : (a :: rest)[k+1]'hk' = rest[k]'hk := by simp
          rw [hidx] at this
          rw [show s0 + 1 + k = s0 + (k + 1) from by omega]
          have hcond : (k + 1 + 1 == (a :: rest).length) = (k + 1 == rest.length) := by
            simp [List.length_cons]
          rw [hcond] at this
          rcases Nat.decEq (k + 1) rest.length with hc | hc
          · rw [if_neg (by simpa using hc)] at this ⊢; exact this
          · rw [if_pos (by simpa using hc)] at this ⊢; exact this
        have hkeep : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b = eval τ b := fun b hb =>
          eval_update_not_read (hfresh b (List.mem_cons_of_mem _ hb) a ha_mem)
        have hrec' : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b ≠ none := by
          intro b hb; rw [hkeep b hb]; exact hrec b (List.mem_cons_of_mem _ hb)
        have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, exprReadsVar x (tempFor P y) = false :=
          fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        obtain ⟨τ', hrun, hoff, hon, hcnt⟩ :=
          ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hrec' hfresh'
        rw [if_neg (by simpa using hre)] at hrun
        refine ⟨τ', ?_, ?_, ?_, ?_⟩
        · rw [show ((a :: rest).isEmpty) = false from by simp, if_neg (by simp)]
          show run Q ⟨s0, τ⟩ (rest.length + 1) = _
          rw [show run Q ⟨s0, τ⟩ (rest.length + 1)
                = run Q ⟨s0 + 1, τ.update (tempFor P a) va⟩ rest.length from by simp only [run, hstep0]]
          exact hrun
        · intro v hv
          have hav : tempFor P a ≠ v := hv a ha_mem
          have heq : τ' v = (τ.update (tempFor P a) va) v :=
            hoff v (fun b hb => hv b (List.mem_cons_of_mem _ hb))
          rw [heq, Store.update, if_neg (fun h => hav h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · subst heq
            have hno : ∀ b ∈ rest, tempFor P b ≠ tempFor P x :=
              fun b hb => hdist b (List.mem_cons_of_mem _ hb) x ha_mem (fun h => hnotin (h ▸ hb))
            have heq2 : τ' (tempFor P x) = (τ.update (tempFor P x) va) (tempFor P x) :=
              hoff (tempFor P x) hno
            rw [heq2, Store.update, if_pos rfl, hva]
          · rw [hon x hx, hkeep x hx]
        · exact hcount hstep0 (by rw [if_neg hre]; exact hf0) hcnt

/-! ## Block-level fuel executors (with count) — the layout specializations

`insBlock_run`/`exitBlock_run` are the `run`/`evalCount` analogues of `insBlock_exec`/`exitBlock_exec`: they
specialize the chain executors to the transform's offset layout and collapse the raw `filter`-count to the
`Assignments`-membership indicator (via `count_filter_beq_nodup` + nodup). These are the per-segment count facts the
block fold consumes; the no-fault hypotheses are the genuine operational content (discharged in the fold by
`antiNoFault`, exactly as `match_step` discharges them for `insBlock_exec`/`exitBlock_exec`). -/

/-- Fuel-level entry executor + count: the `insChain` runs straight to the control slot, evaluating `e`
    exactly `[e ∈ insertBefore i]` times. -/
theorem insBlock_run {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size) (e : Expr)
    {τ : Store}
    (hdist : ∀ a ∈ (insertBefore P S i).toList, ∀ b ∈ (insertBefore P S i).toList,
      a ≠ b → tempFor P a ≠ tempFor P b)
    (hrec : ∀ a ∈ (insertBefore P S i).toList, eval τ a ≠ none)
    (hfresh : ∀ a ∈ (insertBefore P S i).toList, ∀ b ∈ (insertBefore P S i).toList,
      exprReadsVar a (tempFor P b) = false) :
    ∃ τ1, run (transform P S) ⟨blockOff P S i, τ⟩ (insertBefore P S i).toList.length
            = (⟨blockOff P S i + (insertBefore P S i).toList.length, τ1⟩,
               .next ⟨blockOff P S i + (insertBefore P S i).toList.length, τ1⟩)
        ∧ (∀ v, (∀ a ∈ (insertBefore P S i).toList, tempFor P a ≠ v) → τ1 v = τ v)
        ∧ (∀ a ∈ (insertBefore P S i).toList, some (τ1 (tempFor P a)) = eval τ a)
        ∧ evalCount (transform P S) e ⟨blockOff P S i, τ⟩ (insertBefore P S i).toList.length
            = (if e ∈ insertBefore P S i then 1 else 0) := by
  have hfetch : ∀ k (hk : k < (insertBefore P S i).toList.length),
      (transform P S).fetch (blockOff P S i + k)
        = some (.assign (tempFor P ((insertBefore P S i).toList[k]'hk)) ((insertBefore P S i).toList[k]'hk)
            (blockOff P S i + k + 1)) := by
    intro k hk
    have hkb : k < (block P S i).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (insChain P (insertBefore P S i).toList (blockOff P S i)).length := by
      rw [insChain_length]; exact hk
    rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]
  obtain ⟨τ1, hrun, hoff, hon, hcnt⟩ :=
    run_insChain (Q := transform P S) e (insertBefore P S i).toList (blockOff P S i) τ
      Assignments.nodup_toList hdist hfetch hrec hfresh
  exact ⟨τ1, hrun, hoff, hon, by rw [hcnt, count_filter_beq_nodup Assignments.nodup_toList]; simp only [Assignments.mem_toList]⟩

/-- Fuel-level exit executor + count: the `exitChain` (`assign`/`noop` only) runs from the post-control slot
    to `blockOff next`, evaluating `e` exactly `[e ∈ insertAfter i]` times. -/
theorem exitBlock_run {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size) (e : Expr) {next : Node}
    (hfi : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next))
    {τ : Store}
    (hdist : ∀ a ∈ (insertAfter P S i).toList, ∀ b ∈ (insertAfter P S i).toList,
      a ≠ b → tempFor P a ≠ tempFor P b)
    (hrec : ∀ a ∈ (insertAfter P S i).toList, eval τ a ≠ none)
    (hfresh : ∀ a ∈ (insertAfter P S i).toList, ∀ b ∈ (insertAfter P S i).toList,
      exprReadsVar a (tempFor P b) = false) :
    ∃ τ2, run (transform P S)
            ⟨blockOff P S i + (insertBefore P S i).toList.length + 1, τ⟩
            (insertAfter P S i).toList.length
            = (⟨(if (insertAfter P S i).toList.isEmpty
                  then blockOff P S i + (insertBefore P S i).toList.length + 1
                  else blockOff P S next), τ2⟩,
               .next ⟨(if (insertAfter P S i).toList.isEmpty
                  then blockOff P S i + (insertBefore P S i).toList.length + 1
                  else blockOff P S next), τ2⟩)
        ∧ (∀ v, (∀ a ∈ (insertAfter P S i).toList, tempFor P a ≠ v) → τ2 v = τ v)
        ∧ (∀ a ∈ (insertAfter P S i).toList, some (τ2 (tempFor P a)) = eval τ a)
        ∧ evalCount (transform P S) e
            ⟨blockOff P S i + (insertBefore P S i).toList.length + 1, τ⟩
            (insertAfter P S i).toList.length
            = (if e ∈ insertAfter P S i then 1 else 0) := by
  have hfetch : ∀ k (hk : k < (insertAfter P S i).toList.length),
      (transform P S).fetch ((blockOff P S i + (insertBefore P S i).toList.length + 1) + k)
        = some (.assign (tempFor P ((insertAfter P S i).toList[k]'hk)) ((insertAfter P S i).toList[k]'hk)
            (if k + 1 == (insertAfter P S i).toList.length then blockOff P S next
             else (blockOff P S i + (insertBefore P S i).toList.length + 1) + k + 1)) := by
    intro k hk
    have hkb : (insertBefore P S i).toList.length + 1 + k < (block P S i).length := by
      rw [block_length]; unfold blockLen
      rcases hfi with h | ⟨x, e', h⟩ <;> simp only [h] <;> omega
    rw [show (blockOff P S i + (insertBefore P S i).toList.length + 1) + k
          = blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) from by omega]
    rw [transform_fetch hi hkb, getElem?_block_exit hfi, exitChain_getElem? hk]
    rw [show blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) + 1
          = blockOff P S i + (insertBefore P S i).toList.length + 1 + k + 1 from by omega]
  obtain ⟨τ2, hrun, hoff, hon, hcnt⟩ :=
    run_exitChain (Q := transform P S) e (blockOff P S next) (insertAfter P S i).toList
      (blockOff P S i + (insertBefore P S i).toList.length + 1) τ
      Assignments.nodup_toList hdist hfetch hrec hfresh
  exact ⟨τ2, hrun, hoff, hon, by rw [hcnt, count_filter_beq_nodup Assignments.nodup_toList]; simp only [Assignments.mem_toList]⟩

-- `run_add` (run composition; the `run`-level companion to `evalCount_add`) is a shared
-- reference-semantics lemma in `IR.TAC` (`namespace Semantics`).

/-! ## The shared entry-block prefix, with count

`entry_block_run` is the fuel+count analogue of `entry_block`: it runs node `nd`'s `insChain` to the control
slot, re-establishing the non-fresh agreement and the `M ∪ insertBefore`-temps `Holds` invariant (identical
reasoning to `entry_block`), **and** reports the entry-segment eval count `[e ∈ insertBefore nd]`. The common
prefix of `block_evalCount`'s control cases. -/

theorem entry_block_run {P : Program} (S : LcmSpec P) {nd : Node} (hi : nd < P.size) (e : Expr)
    {dσ cσ : Store} {M : Assignments}
    (hagree : ∀ x, NonFresh P x → dσ x = cσ x)
    (hHolds : ∀ e ∈ M, Holds dσ cσ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hnf : ∀ e ∈ (insertBefore P S nd).toList, eval dσ e ≠ none) :
    ∃ τ1, run (transform P S) ⟨blockOff P S nd, dσ⟩ (insertBefore P S nd).toList.length
            = (⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩,
               .next ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩)
        ∧ (∀ x, NonFresh P x → τ1 x = cσ x)
        ∧ (∀ e, (e ∈ M ∨ e ∈ insertBefore P S nd) → Holds τ1 cσ (tempFor P e) e)
        ∧ evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (insertBefore P S nd).toList.length
            = (if e ∈ insertBefore P S nd then 1 else 0) := by
  have hmem_all : ∀ e ∈ (insertBefore P S nd).toList, e ∈ (allExprs P).toList :=
    fun e he => Assignments.mem_toList.2 (insertBefore_mem_allExprs he)
  have hdist : ∀ a ∈ (insertBefore P S nd).toList, ∀ b ∈ (insertBefore P S nd).toList,
      a ≠ b → tempFor P a ≠ tempFor P b :=
    fun a ha b hb hne heq => hne (tempFor_inj P (hmem_all a ha) (hmem_all b hb) heq)
  have hfresh : ∀ a ∈ (insertBefore P S nd).toList, ∀ b ∈ (insertBefore P S nd).toList,
      exprReadsVar a (tempFor P b) = false :=
    fun a ha _ _ => insert_fresh (insertBefore_mem_allExprs ha)
  obtain ⟨τ1, hrun1, hoff1, hon1, hcnt1⟩ := insBlock_run S hi e hdist hnf hfresh
  refine ⟨τ1, hrun1, ?_, ?_, hcnt1⟩
  · intro x hx
    rw [hoff1 x (fun a _ => hx a), hagree x hx]
  · intro e' hin
    have key : some (τ1 (tempFor P e')) = eval cσ e' := by
      by_cases hia : e' ∈ (insertBefore P S nd).toList
      · have h1 : some (τ1 (tempFor P e')) = eval dσ e' := hon1 e' hia
        rw [h1, eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs hia) hagree]
      · have heM : e' ∈ M := hin.resolve_right (fun h => hia (Assignments.mem_toList.2 h))
        have hne : ∀ a ∈ (insertBefore P S nd).toList, tempFor P a ≠ tempFor P e' := by
          intro a ha heq
          have hee : a = e' := tempFor_inj P (hmem_all a ha) (Assignments.mem_toList.2 (hMsub e' heM)) heq
          exact hia (hee ▸ ha)
        have huntouched : τ1 (tempFor P e') = dσ (tempFor P e') := hoff1 (tempFor P e') hne
        rw [huntouched]; exact (Holds_iff.1 (hHolds e' heM))
    exact Holds_iff.2 key

/-! ## `block_evalCount` — the per-block run + Match + count

For a source step at node `nd`, running `nd`'s block (entry `insChain` → floated control → exit `exitChain`)
re-establishes `Match` at `Mstep nd M` (exactly as `match_step`) **and** evaluates `e` exactly
`[e ∈ insertBefore nd] + [ctrl computes e] + [e ∈ insertAfter nd]` times — the per-block contribution the eval-count
fold sums over the source run. The three control cases mirror `match_step_{noop,ifz,assign}`; the Match-clause
reasoning is identical, with the relational executors replaced by the fuel ones (`entry_block_run`,
`exitBlock_run`) and the count accumulated via `evalCount_add`/`evalCount_next`. -/

/-- Per-block contribution on the edge `nd → next`: entry inserts + the control evaluation + the taken
    edge/exit inserts `insertEdge nd next` (`= insertAfter nd` for a `1-successor` source; the taken branch's
    edge chain for an `ifz`). -/
def blockContribution (P : Program) (S : LcmSpec P) (nd next : Node) (e : Expr) : Nat :=
  (if e ∈ insertBefore P S nd then 1 else 0)
    + (if computesExpr (transform P S) (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0)
    + (if e ∈ insertEdge P S nd next then 1 else 0)

/-- The whole-block fuel on the edge `nd → next`: entry chain + control + the taken edge/exit chain
    `insertEdge nd next`. -/
def blockFuel (P : Program) (S : LcmSpec P) (nd next : Node) : Nat :=
  (insertBefore P S nd).toList.length + ((insertEdge P S nd next).toList.length + 1)

/-- **`block_evalCount`, `noop` case.** -/
theorem block_evalCount_noop {P : Program} (S : LcmSpec P) (e : Expr)
    {nd next : Node} {σ dσ : Store} {M : Assignments} {c_f : Config}
    (hf : P.fetch nd = some (.noop next))
    (hagree : ∀ x, NonFresh P x → dσ x = σ x)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hcont : StepsH P ⟨next, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ τF, run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next)
            = (⟨blockOff P S next, τF⟩, .next ⟨blockOff P S next, τF⟩)
        ∧ Match P S ⟨next, σ⟩ ⟨blockOff P S next, τF⟩ (Mstep S nd M)
        ∧ evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next)
            = blockContribution P S nd next e := by
  have hi : nd < P.size := fetch_lt hf
  have hAE : insertAfter P S nd = insertEdge P S nd next := insertAfter_eq_insertEdge S (Or.inl hf)
  have hnf : ∀ e' ∈ (insertBefore P S nd).toList, eval dσ e' ≠ none := by
    intro e' he'
    have hanti : e' ∈ S.πₐ nd := insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he')
    obtain ⟨v, hv⟩ := antiNoFault S (StepsH.head (Step.noop hf) hcont) hfin e' hanti
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he') hagree, hv]; exact Option.some_ne_none v
  obtain ⟨τ1, hrun1, hag1, hH1, hcnt1⟩ := entry_block_run S hi e hagree hHolds hMsub hnf
  have hctl : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
      = some (ctrlCmd P S nd) := ctrl_slot_fetch S hi
  have hnfe : ∀ e' ∈ (insertAfter P S nd).toList, eval τ1 e' ≠ none := by
    intro e' he'
    have hanti : e' ∈ S.πₐ next := by
      have h2 := he'; rw [Assignments.mem_toList] at h2
      unfold insertAfter at h2; rw [hf, Assignments.mem_inter] at h2
      exact edgeIns_sub_anti S (Step.noop (σ := σ) hf) hpa h2.1
    obtain ⟨v, hv⟩ := antiNoFault S hcont hfin e' hanti
    rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he') hag1, hv]; exact Option.some_ne_none v
  have hde : ∀ a ∈ (insertAfter P S nd).toList, ∀ b ∈ (insertAfter P S nd).toList,
      a ≠ b → tempFor P a ≠ tempFor P b := fun a ha b hb hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs ha))
      (Assignments.mem_toList.2 (insertAfter_mem_allExprs hb)) heq)
  have hfre : ∀ a ∈ (insertAfter P S nd).toList, ∀ b ∈ (insertAfter P S nd).toList,
      exprReadsVar a (tempFor P b) = false := fun a ha _ _ => insert_fresh (insertAfter_mem_allExprs ha)
  -- control + exit run (fuel L3+1) to ⟨blockOff next, τF⟩, count = [ctrl computes e] + [e ∈ insertAfter]
  obtain ⟨τF, hrunCE, hoffF, honF, hcntCE⟩ :
      ∃ τF, run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertAfter P S nd).toList.length + 1)
              = (⟨blockOff P S next, τF⟩, .next ⟨blockOff P S next, τF⟩)
          ∧ (∀ v, (∀ a ∈ (insertAfter P S nd).toList, tempFor P a ≠ v) → τF v = τ1 v)
          ∧ (∀ a ∈ (insertAfter P S nd).toList, some (τF (tempFor P a)) = eval τ1 a)
          ∧ evalCount (transform P S) e ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertAfter P S nd).toList.length + 1)
              = (if computesExpr (transform P S)
                    (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0)
                + (if e ∈ insertAfter P S nd then 1 else 0) := by
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · have hL0 : (insertAfter P S nd).toList.length = 0 := by rw [List.isEmpty_iff.mp hemp]; rfl
      have hnie : e ∉ insertAfter P S nd := by
        intro h; rw [← Assignments.mem_toList, List.isEmpty_iff.mp hemp] at h; simp at h
      have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          = .next ⟨blockOff P S next, τ1⟩ := by
        have hfetch : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
            = some (.noop (blockOff P S next)) := by rw [hctl]; simp only [ctrlCmd, hf, hemp, if_true]
        simp only [step1, hfetch]
      refine ⟨τ1, ?_, fun v _ => rfl, ?_, ?_⟩
      · rw [hL0]; show run (transform P S) _ 1 = _; simp only [run, hctlstep]
      · intro a ha; rw [List.isEmpty_iff.mp hemp] at ha; simp at ha
      · rw [hL0]; show evalCount (transform P S) e _ 1 = _
        rw [evalCount_next hctlstep, if_neg hnie, Nat.add_zero,
            show evalCount (transform P S) e ⟨blockOff P S next, τ1⟩ 0 = 0 from rfl, Nat.add_zero]
    · have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          = .next ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩ := by
        have hfetch : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
            = some (.noop (blockOff P S nd + (insertBefore P S nd).toList.length + 1)) := by
          rw [hctl]; simp only [ctrlCmd, hf, if_neg hemp]
        simp only [step1, hfetch]
      obtain ⟨τ2, hrun2, hoff2, hon2, hcnt2⟩ := exitBlock_run S hi e (Or.inl hf) hde hnfe hfre
      rw [if_neg hemp] at hrun2
      have hsplit : (insertAfter P S nd).toList.length + 1 = 1 + (insertAfter P S nd).toList.length := by omega
      have h1run : run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1
          = (⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩,
             .next ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩) := by
        simp only [run, hctlstep]
      refine ⟨τ2, ?_, hoff2, hon2, ?_⟩
      · rw [hsplit, run_add h1run]; exact hrun2
      · rw [hsplit, evalCount_add h1run, hcnt2,
            show evalCount (transform P S) e ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1
              = (if computesExpr (transform P S)
                  (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0) from by
              rw [evalCount_next hctlstep,
                  show evalCount (transform P S) e
                    ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1⟩ 0 = 0 from rfl, Nat.add_zero]]
  refine ⟨τF, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next) = _
    unfold blockFuel; rw [← hAE, run_add hrun1]; exact hrunCE
  · -- Match clause 2
    intro x hx; show τF x = σ x
    rw [hoffF x (fun a _ => hx a), hag1 x hx]
  · -- Match clause 3
    intro e' he'
    rw [Mstep, Assignments.mem_union] at he'
    show Holds τF σ (tempFor P e') e'
    rcases he' with hcarry | hexit
    · rw [Assignments.mem_inter, Assignments.mem_union] at hcarry
      have heall : e' ∈ allExprs P :=
        hcarry.1.elim (fun h => hMsub e' h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
      have hH1e : Holds τ1 σ (tempFor P e') e' := hH1 e' hcarry.1
      by_cases hei : e' ∈ (insertAfter P S nd).toList
      · apply Holds_iff.2
        rw [honF e' hei, eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs hei) hag1]
      · have hunt : τF (tempFor P e') = τ1 (tempFor P e') := by
          apply hoffF; intro e'' he'' heq
          exact hei ((tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he''))
            (Assignments.mem_toList.2 heall) heq) ▸ he'')
        rw [Holds_iff] at hH1e ⊢; rw [hunt]; exact hH1e
    · apply Holds_iff.2
      rw [honF e' (Assignments.mem_toList.2 hexit),
          eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs (Assignments.mem_toList.2 hexit)) hag1]
  · -- Match clause 4
    intro e' he'
    rw [Mstep, Assignments.mem_union] at he'
    rcases he' with hc | hex
    · rw [Assignments.mem_inter, Assignments.mem_union] at hc
      exact hc.1.elim (fun h => hMsub e' h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
    · exact insertAfter_mem_allExprs (Assignments.mem_toList.2 hex)
  · show evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next) = _
    unfold blockFuel blockContribution
    rw [← hAE, evalCount_add hrun1, hcnt1, hcntCE, Nat.add_assoc]

/-- **`block_evalCount`, `ifz` case.** The floated `ifz` branches to the taken successor's edge chain, which
    materializes `insertEdge nd succ` (store unchanged), landing at `blockOff succ`. The `ifz` control computes
    no expression, so `blockContribution nd succ e = [e∈insertBefore] + [e∈insertEdge succ]`. -/
theorem block_evalCount_ifz {P : Program} (S : LcmSpec P) (e : Expr)
    {nd : Node} {x : Var} {z nz succ : Node} {σ dσ : Store} {M : Assignments} {c_f : Config}
    (hf : P.fetch nd = some (.ifz x z nz))
    (hcond : (σ x = 0 ∧ succ = z) ∨ (σ x ≠ 0 ∧ succ = nz))
    (hagree : ∀ v, NonFresh P v → dσ v = σ v)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hstepsrc : Step P ⟨nd, σ⟩ ⟨succ, σ⟩)
    (hcont : StepsH P ⟨succ, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ τF, run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd succ)
            = (⟨blockOff P S succ, τF⟩, .next ⟨blockOff P S succ, τF⟩)
        ∧ Match P S ⟨succ, σ⟩ ⟨blockOff P S succ, τF⟩ (Mstep_edge S nd succ M)
        ∧ evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd succ)
            = blockContribution P S nd succ e := by
  have hi : nd < P.size := fetch_lt hf
  have hnf : ∀ e' ∈ (insertBefore P S nd).toList, eval dσ e' ≠ none := by
    intro e' he'
    have hanti : e' ∈ S.πₐ nd := insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he')
    obtain ⟨v, hv⟩ := antiNoFault S (StepsH.head hstepsrc hcont) hfin e' hanti
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he') hagree, hv]; exact Option.some_ne_none v
  obtain ⟨τ1, hrun1, hag1, hH1, hcnt1⟩ := entry_block_run S hi e hagree hHolds hMsub hnf
  have hxnf : NonFresh P x := nonFresh_of_used hf (by simp [instrUsedVars])
  have hctlf : (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
      = some (.ifz x (if (insertEdge P S nd z).toList.isEmpty then blockOff P S z
                      else blockOff P S nd + (insertBefore P S nd).toList.length + 1)
                     (if (insertEdge P S nd nz).toList.isEmpty then blockOff P S nz
                      else blockOff P S nd + (insertBefore P S nd).toList.length + 1
                        + (insertEdge P S nd z).toList.length)) := by
    rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]
  have hnocomp : (if computesExpr (transform P S)
      (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0) = 0 := by
    have : computesExpr (transform P S) (blockOff P S nd + (insertBefore P S nd).toList.length) e = false := by
      simp only [computesExpr, hctlf]
    rw [this]; rfl
  -- edge-chain no-fault (each insertEdge succ expr is anticipated at succ, fault-free on a halting run)
  have hnfe : ∀ e' ∈ (insertEdge P S nd succ).toList, eval σ e' ≠ none := by
    intro e' he'
    have hedge : e' ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd succ :=
      (Assignments.mem_inter.mp (Assignments.mem_toList.1 he')).1
    obtain ⟨v, hv⟩ := antiNoFault S hcont hfin e' (edgeIns_sub_anti S hstepsrc hpa hedge)
    rw [hv]; exact Option.some_ne_none v
  have hde : ∀ a ∈ (insertEdge P S nd succ).toList, ∀ b ∈ (insertEdge P S nd succ).toList,
      a ≠ b → tempFor P a ≠ tempFor P b := fun a ha b hb hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs ha))
      (Assignments.mem_toList.2 (insertEdge_mem_allExprs hb)) heq)
  have hfre : ∀ a ∈ (insertEdge P S nd succ).toList, ∀ b ∈ (insertEdge P S nd succ).toList,
      exprReadsVar a (tempFor P b) = false := fun a ha _ _ => insert_fresh (insertEdge_mem_allExprs ha)
  have hrec : ∀ a ∈ (insertEdge P S nd succ).toList, eval τ1 a ≠ none := fun a ha => by
    rw [eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs ha) hag1]; exact hnfe a ha
  -- control + taken edge chain: run (|insertEdge succ|+1) to ⟨blockOff succ, τF⟩, count = [e∈insertEdge succ]
  obtain ⟨τF, hrunCE, hoffF, honF, hcntCE⟩ :
      ∃ τF, run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertEdge P S nd succ).toList.length + 1)
              = (⟨blockOff P S succ, τF⟩, .next ⟨blockOff P S succ, τF⟩)
          ∧ (∀ v, (∀ a ∈ (insertEdge P S nd succ).toList, tempFor P a ≠ v) → τF v = τ1 v)
          ∧ (∀ a ∈ (insertEdge P S nd succ).toList, some (τF (tempFor P a)) = eval τ1 a)
          ∧ evalCount (transform P S) e ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertEdge P S nd succ).toList.length + 1)
              = (if e ∈ insertEdge P S nd succ then 1 else 0) := by
    have hsplit : (insertEdge P S nd succ).toList.length + 1
        = 1 + (insertEdge P S nd succ).toList.length := by omega
    -- the branch step to the ctrl's taken target, and the edge-chain fetch
    obtain ⟨st, hctlstep, hfetch⟩ :
        ∃ st, step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
            = .next ⟨(if (insertEdge P S nd succ).toList.isEmpty then blockOff P S succ else st), τ1⟩
          ∧ (∀ k (hk : k < (insertEdge P S nd succ).toList.length),
              (transform P S).fetch (st + k)
                = some (.assign (tempFor P ((insertEdge P S nd succ).toList[k]'hk)) ((insertEdge P S nd succ).toList[k]'hk)
                    (if k + 1 == (insertEdge P S nd succ).toList.length then blockOff P S succ else st + k + 1))) := by
      rcases hcond with ⟨hx0, hsu⟩ | ⟨hxne, hsu⟩ <;> subst succ
      · refine ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, ?_, ?_⟩
        · exact step1_next_iff.mpr (Step.ifzT (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hx0))
        · intro k hk
          have hbl : blockLen P S nd = (insertBefore P S nd).toList.length + 1
              + ((insertEdge P S nd z).toList.length + (insertEdge P S nd nz).toList.length) := by
            simp only [blockLen, hf]
          have hkb : (insertBefore P S nd).toList.length + 1 + k < (block P S nd).length := by
            rw [block_length, hbl]; omega
          rw [show (blockOff P S nd + (insertBefore P S nd).toList.length + 1) + k
                = blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_z hf hk, exitChain_getElem? hk,
              show blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + k) + 1
                = blockOff P S nd + (insertBefore P S nd).toList.length + 1 + k + 1 from by omega]
      · refine ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length, ?_, ?_⟩
        · exact step1_next_iff.mpr (Step.ifzF (σ := τ1) hctlf (by rw [hag1 x hxnf]; exact hxne))
        · intro k hk
          have hbl : blockLen P S nd = (insertBefore P S nd).toList.length + 1
              + ((insertEdge P S nd z).toList.length + (insertEdge P S nd nz).toList.length) := by
            simp only [blockLen, hf]
          have hkb : (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k
              < (block P S nd).length := by rw [block_length, hbl]; omega
          rw [show (blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length) + k
                = blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k) from by omega,
              transform_fetch hi hkb, getElem?_block_ifz_nz hf hk, exitChain_getElem? hk,
              show blockOff P S nd + ((insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k) + 1
                = blockOff P S nd + (insertBefore P S nd).toList.length + 1 + (insertEdge P S nd z).toList.length + k + 1 from by omega]
    by_cases hemp : (insertEdge P S nd succ).toList.isEmpty = true
    · have hL0 : (insertEdge P S nd succ).toList.length = 0 := by rw [List.isEmpty_iff.mp hemp]; rfl
      have hnie : e ∉ insertEdge P S nd succ := by
        intro h; rw [← Assignments.mem_toList, List.isEmpty_iff.mp hemp] at h; simp at h
      rw [if_pos hemp] at hctlstep
      refine ⟨τ1, ?_, fun v _ => rfl, ?_, ?_⟩
      · rw [hL0]; show run (transform P S) _ 1 = _; simp only [run, hctlstep]
      · intro a ha; rw [List.isEmpty_iff.mp hemp] at ha; simp at ha
      · rw [hL0]; show evalCount (transform P S) e _ 1 = _
        rw [evalCount_next hctlstep,
            show evalCount (transform P S) e ⟨blockOff P S succ, τ1⟩ 0 = 0 from rfl, Nat.add_zero, hnocomp,
            if_neg hnie]
    · rw [if_neg hemp] at hctlstep
      obtain ⟨τ2, hrun2, hoff2, hon2, hcnt2⟩ :=
        run_exitChain (Q := transform P S) e (blockOff P S succ) (insertEdge P S nd succ).toList st τ1
          Assignments.nodup_toList hde hfetch hrec hfre
      rw [if_neg hemp] at hrun2
      have h1run : run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1
          = (⟨st, τ1⟩, .next ⟨st, τ1⟩) := by simp only [run, hctlstep]
      refine ⟨τ2, ?_, hoff2, hon2, ?_⟩
      · rw [hsplit, run_add h1run]; exact hrun2
      · rw [hsplit, evalCount_add h1run,
            show evalCount (transform P S) e ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1 = 0 from by
              rw [evalCount_next hctlstep,
                  show evalCount (transform P S) e ⟨st, τ1⟩ 0 = 0 from rfl, Nat.add_zero, hnocomp],
            Nat.zero_add, hcnt2, count_filter_beq_nodup Assignments.nodup_toList]
        simp only [Assignments.mem_toList]
  refine ⟨τF, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd succ) = _
    unfold blockFuel; rw [run_add hrun1]; exact hrunCE
  · intro v hv; show τF v = σ v
    rw [hoffF v (fun a _ => hv a), hag1 v hv]
  · intro e' he'
    show Holds τF σ (tempFor P e') e'
    by_cases hie : e' ∈ (insertEdge P S nd succ).toList
    · apply Holds_iff.2
      rw [honF e' hie, eval_eq_of_nonFresh_agree (insertEdge_mem_allExprs hie) hag1]
    · have heMstep : e' ∈ Mstep S nd M := by
        rw [Mstep_edge, Assignments.mem_union] at he'
        exact he'.resolve_right (fun h => hie (Assignments.mem_toList.2 h))
      rw [Mstep, Assignments.mem_union] at heMstep
      rcases heMstep with hin | hafter
      · have hmem := (Assignments.mem_inter.mp hin).1
        have hH1e : Holds τ1 σ (tempFor P e') e' := hH1 e' (Assignments.mem_union.mp hmem)
        have heall : e' ∈ allExprs P := (Assignments.mem_union.mp hmem).elim (fun h => hMsub e' h)
          (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
        rw [Holds_iff] at hH1e ⊢
        rw [hoffF (tempFor P e') (fun e'' he'' heq =>
          hie (tempFor_inj P (Assignments.mem_toList.2 (insertEdge_mem_allExprs he''))
            (Assignments.mem_toList.2 heall) heq ▸ he''))]
        exact hH1e
      · unfold insertAfter at hafter; rw [hf] at hafter
        simp only [Assignments.empty] at hafter; exact absurd hafter Std.HashSet.not_mem_empty
  · intro e' he'
    rw [Mstep_edge, Assignments.mem_union] at he'
    rcases he' with hms | hie
    · rw [Mstep, Assignments.mem_union] at hms
      rcases hms with hc | hafter
      · rw [Assignments.mem_inter, Assignments.mem_union] at hc
        exact hc.1.elim (fun h => hMsub e' h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
      · unfold insertAfter at hafter; rw [hf] at hafter
        simp only [Assignments.empty] at hafter; exact absurd hafter Std.HashSet.not_mem_empty
    · exact insertEdge_mem_allExprs (Assignments.mem_toList.2 hie)
  · show evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd succ) = _
    unfold blockFuel blockContribution
    rw [evalCount_add hrun1, hcnt1, hcntCE, hnocomp, Nat.add_zero]

/-- **`block_evalCount`, `assign` case.** The store changes (`σ → σ.update x v`); the gate may rewrite the
    control to read a hoisted temp; carried temps survive `x`'s def by `transp_holds`; the exit chain
    materializes `insertAfter` with the post-assign store. -/
theorem block_evalCount_assign {P : Program} (S : LcmSpec P) (hg : GateSound P S) (e : Expr)
    {nd : Node} {x : Var} {e0 : Expr} {next : Node} {v : Val} {σ dσ : Store} {M : Assignments} {c_f : Config}
    (hf : P.fetch nd = some (.assign x e0 next)) (hv : eval σ e0 = some v)
    (hagree : ∀ y, NonFresh P y → dσ y = σ y)
    (hHolds : ∀ e ∈ M, Holds dσ σ (tempFor P e) e)
    (hMsub : ∀ e ∈ M, e ∈ allExprs P)
    (hpa : Assignments.Subset (S.ηₚ nd) (S.πₐ nd))
    (hcov : Cov S nd M)
    (hcont : StepsH P ⟨next, σ.update x v⟩ c_f) (hfin : Final P c_f) :
    ∃ τF, run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next)
            = (⟨blockOff P S next, τF⟩, .next ⟨blockOff P S next, τF⟩)
        ∧ Match P S ⟨next, σ.update x v⟩ ⟨blockOff P S next, τF⟩ (Mstep S nd M)
        ∧ evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next)
            = blockContribution P S nd next e := by
  have hi : nd < P.size := fetch_lt hf
  have hAE : insertAfter P S nd = insertEdge P S nd next := insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)
  have hstepsrc : Step P (⟨nd, σ⟩ : Config) ⟨next, σ.update x v⟩ := Step.assign hf hv
  have hxnf : NonFresh P x := nonFresh_of_def hf (by simp [instrDefVar])
  have hnf : ∀ e' ∈ (insertBefore P S nd).toList, eval dσ e' ≠ none := by
    intro e' he'
    have hanti : e' ∈ S.πₐ nd := insertBefore_sub_anti S hpa (Assignments.mem_toList.1 he')
    obtain ⟨w, hw⟩ := antiNoFault S (StepsH.head hstepsrc hcont) hfin e' hanti
    rw [eval_eq_of_nonFresh_agree (insertBefore_mem_allExprs he') hagree, hw]; exact Option.some_ne_none w
  obtain ⟨τ1, hrun1, hag1, hH1, hcnt1⟩ := entry_block_run S hi e hagree hHolds hMsub hnf
  have hctrl : ∃ rhs, (transform P S).fetch (blockOff P S nd + (insertBefore P S nd).toList.length)
        = some (.assign x rhs (if (insertAfter P S nd).toList.isEmpty
            then blockOff P S next else blockOff P S nd + (insertBefore P S nd).toList.length + 1))
        ∧ eval τ1 rhs = some v := by
    by_cases hfired : (isNumbered e0 && (recoverable P S nd).contains e0) = true
    · refine ⟨.atom (.var (tempFor P e0)),
        by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_pos hfired], ?_⟩
      have hand : isNumbered e0 = true ∧ (recoverable P S nd).contains e0 = true := by
        simpa using hfired
      have hrecov : e0 ∈ recoverable P S nd := Std.HashSet.contains_iff_mem.mp hand.2
      have hHe0 : Holds τ1 σ (tempFor P e0) e0 := hH1 e0 (replace_covered S hg hf hand.1 hrecov hcov)
      simp only [eval, evalAtom]; exact (Holds_iff.1 hHe0).trans hv
    · refine ⟨e0, by rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hf]; rw [if_neg hfired], ?_⟩
      rw [eval_congr (fun y hy => hag1 y (nonFresh_of_used hf
        (by simp only [instrUsedVars]; exact readsVar_imp_mem hy)))]
      exact hv
  obtain ⟨rhs, hfetchr, hrhsv⟩ := hctrl
  have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
      = .next ⟨(if (insertAfter P S nd).toList.isEmpty then blockOff P S next
          else blockOff P S nd + (insertBefore P S nd).toList.length + 1), τ1.update x v⟩ :=
    step1_next_iff.mpr (Step.assign hfetchr hrhsv)
  have hag1' : ∀ y, NonFresh P y → (τ1.update x v) y = (σ.update x v) y := by
    intro y hy
    by_cases hyx : y = x
    · subst hyx; simp [Store.update]
    · simp only [Store.update, if_neg hyx]; exact hag1 y hy
  have hnfe : ∀ e' ∈ (insertAfter P S nd).toList, eval (τ1.update x v) e' ≠ none := by
    intro e' he'
    have hanti : e' ∈ S.πₐ next := by
      have h2 := he'; rw [Assignments.mem_toList] at h2
      unfold insertAfter at h2; rw [hf, Assignments.mem_inter] at h2
      exact edgeIns_sub_anti S hstepsrc hpa h2.1
    obtain ⟨w, hw⟩ := antiNoFault S hcont hfin e' hanti
    rw [eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs he') hag1', hw]; exact Option.some_ne_none w
  have hde : ∀ a ∈ (insertAfter P S nd).toList, ∀ b ∈ (insertAfter P S nd).toList,
      a ≠ b → tempFor P a ≠ tempFor P b := fun a ha b hb hne heq =>
    hne (tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs ha))
      (Assignments.mem_toList.2 (insertAfter_mem_allExprs hb)) heq)
  have hfre : ∀ a ∈ (insertAfter P S nd).toList, ∀ b ∈ (insertAfter P S nd).toList,
      exprReadsVar a (tempFor P b) = false := fun a ha _ _ => insert_fresh (insertAfter_mem_allExprs ha)
  have htransp_read : ∀ e', e' ∈ pass P nd → exprReadsVar e' x = false := by
    intro e' he'
    unfold pass at he'; rw [Assignments.mem_filter'] at he'
    have h2 := he'.2; unfold transpB at h2; rw [hf] at h2; simp only [instrDefVar] at h2
    simpa using h2
  obtain ⟨τF, hrunCE, hoffF, honF, hcntCE⟩ :
      ∃ τF, run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertAfter P S nd).toList.length + 1)
              = (⟨blockOff P S next, τF⟩, .next ⟨blockOff P S next, τF⟩)
          ∧ (∀ w, (∀ a ∈ (insertAfter P S nd).toList, tempFor P a ≠ w) → τF w = (τ1.update x v) w)
          ∧ (∀ a ∈ (insertAfter P S nd).toList, some (τF (tempFor P a)) = eval (τ1.update x v) a)
          ∧ evalCount (transform P S) e ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
              ((insertAfter P S nd).toList.length + 1)
              = (if computesExpr (transform P S)
                    (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0)
                + (if e ∈ insertAfter P S nd then 1 else 0) := by
    have hseg1 : evalCount (transform P S) e
          ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1
        = (if computesExpr (transform P S)
            (blockOff P S nd + (insertBefore P S nd).toList.length) e then 1 else 0) := by
      rw [evalCount_next hctlstep,
          show evalCount (transform P S) e
            ⟨(if (insertAfter P S nd).toList.isEmpty then blockOff P S next
              else blockOff P S nd + (insertBefore P S nd).toList.length + 1), τ1.update x v⟩ 0 = 0 from rfl,
          Nat.add_zero]
    by_cases hemp : (insertAfter P S nd).toList.isEmpty = true
    · have hL0 : (insertAfter P S nd).toList.length = 0 := by rw [List.isEmpty_iff.mp hemp]; rfl
      have hnie : e ∉ insertAfter P S nd := by
        intro h; rw [← Assignments.mem_toList, List.isEmpty_iff.mp hemp] at h; simp at h
      have hcs : step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          = .next ⟨blockOff P S next, τ1.update x v⟩ := by rw [hctlstep, if_pos hemp]
      refine ⟨τ1.update x v, ?_, fun w _ => rfl, ?_, ?_⟩
      · rw [hL0]; show run (transform P S) _ 1 = _; simp only [run, hcs]
      · intro a ha; rw [List.isEmpty_iff.mp hemp] at ha; simp at ha
      · rw [hL0]; show evalCount (transform P S) e _ 1 = _
        rw [hseg1, if_neg hnie, Nat.add_zero]
    · obtain ⟨τ2, hrun2, hoff2, hon2, hcnt2⟩ := exitBlock_run S hi e (Or.inr ⟨x, e0, hf⟩) hde hnfe hfre
      rw [if_neg hemp] at hrun2
      have hcs : step1 (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩
          = .next ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1.update x v⟩ := by
        rw [hctlstep, if_neg hemp]
      have hsplit : (insertAfter P S nd).toList.length + 1 = 1 + (insertAfter P S nd).toList.length := by omega
      have h1run : run (transform P S) ⟨blockOff P S nd + (insertBefore P S nd).toList.length, τ1⟩ 1
          = (⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1.update x v⟩,
             .next ⟨blockOff P S nd + (insertBefore P S nd).toList.length + 1, τ1.update x v⟩) := by
        simp only [run, hcs]
      refine ⟨τ2, ?_, hoff2, hon2, ?_⟩
      · rw [hsplit, run_add h1run]; exact hrun2
      · rw [hsplit, evalCount_add h1run, hcnt2, hseg1]
  refine ⟨τF, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next) = _
    unfold blockFuel; rw [← hAE, run_add hrun1]; exact hrunCE
  · intro y hy; show τF y = (σ.update x v) y
    rw [hoffF y (fun a _ => hy a), hag1' y hy]
  · intro e' he'
    rw [Mstep, Assignments.mem_union] at he'
    show Holds τF (σ.update x v) (tempFor P e') e'
    rcases he' with hcarry | hexit
    · rw [Assignments.mem_inter, Assignments.mem_union] at hcarry
      have heall : e' ∈ allExprs P :=
        hcarry.1.elim (fun h => hMsub e' h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
      have hH1e : Holds τ1 σ (tempFor P e') e' := hH1 e' hcarry.1
      have hupd : Holds (τ1.update x v) (σ.update x v) (tempFor P e') e' :=
        transp_holds (htransp_read e' hcarry.2) (Ne.symm (hxnf e')) hH1e
      by_cases hei : e' ∈ (insertAfter P S nd).toList
      · apply Holds_iff.2
        rw [honF e' hei, eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs hei) hag1']
      · have hunt : τF (tempFor P e') = (τ1.update x v) (tempFor P e') := by
          apply hoffF; intro e'' he'' heq
          exact hei ((tempFor_inj P (Assignments.mem_toList.2 (insertAfter_mem_allExprs he''))
            (Assignments.mem_toList.2 heall) heq) ▸ he'')
        rw [Holds_iff] at hupd ⊢; rw [hunt]; exact hupd
    · apply Holds_iff.2
      rw [honF e' (Assignments.mem_toList.2 hexit),
          eval_eq_of_nonFresh_agree (insertAfter_mem_allExprs (Assignments.mem_toList.2 hexit)) hag1']
  · intro e' he'
    rw [Mstep, Assignments.mem_union] at he'
    rcases he' with hc | hex
    · rw [Assignments.mem_inter, Assignments.mem_union] at hc
      exact hc.1.elim (fun h => hMsub e' h) (fun h => insertBefore_mem_allExprs (Assignments.mem_toList.2 h))
    · exact insertAfter_mem_allExprs (Assignments.mem_toList.2 hex)
  · show evalCount (transform P S) e ⟨blockOff P S nd, dσ⟩ (blockFuel P S nd next) = _
    unfold blockFuel blockContribution
    rw [← hAE, evalCount_add hrun1, hcnt1, hcntCE, Nat.add_assoc]

/-- **`block_evalCount` — the per-block step.** A source step `c → c'` runs node `c`'s block (the same run
    `match_step` produces), re-establishing `Match` at `Mstep c.node M` **and** evaluating `e` exactly
    `blockContribution c.node e = [e ∈ insertBefore] + [ctrl computes e] + [e ∈ insertAfter]` times. This is the
    per-block summand the eval-count fold sums over the source run. -/
theorem block_evalCount {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    {c c' d : Config} {M : Assignments} {c_f : Config} (e : Expr)
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c')
    (hcont : StepsH P c' c_f) (hfin : Final P c_f) :
    ∃ τF, run (transform P S) d (blockFuel P S c.node c'.node)
            = (⟨blockOff P S c'.node, τF⟩, .next ⟨blockOff P S c'.node, τF⟩)
        ∧ Match P S c' ⟨blockOff P S c'.node, τF⟩ (Mstep_edge S c.node c'.node M)
        ∧ evalCount (transform P S) e d (blockFuel P S c.node c'.node)
            = blockContribution P S c.node c'.node e := by
  obtain ⟨hlabel, hagree, hHolds, hMsub⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  cases hstep with
  | @assign nd σ x e0 next vv hf hvv =>
    subst hlabel
    obtain ⟨τF, hrun, hm', hcnt⟩ :=
      block_evalCount_assign S hg e hf hvv hagree hHolds hMsub hpa hcov hcont hfin
    exact ⟨τF, hrun, Match_union_sub hm' (fun a ha => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inr ⟨x, e0, hf⟩)]; exact ha))), hcnt⟩
  | @noop nd σ next hf =>
    subst hlabel
    obtain ⟨τF, hrun, hm', hcnt⟩ := block_evalCount_noop S e hf hagree hHolds hMsub hpa hcont hfin
    exact ⟨τF, hrun, Match_union_sub hm' (fun a ha => Assignments.mem_union.mpr
      (Or.inr (by rw [insertAfter_eq_insertEdge S (Or.inl hf)]; exact ha))), hcnt⟩
  | @ifzT nd σ x z nz hf hcond =>
    subst hlabel
    exact block_evalCount_ifz S e hf (Or.inl ⟨hcond, rfl⟩)
      hagree hHolds hMsub hpa (Step.ifzT hf hcond) hcont hfin
  | @ifzF nd σ x z nz hf hcond =>
    subst hlabel
    exact block_evalCount_ifz S e hf (Or.inr ⟨hcond, rfl⟩)
      hagree hHolds hMsub hpa (Step.ifzF hf hcond) hcont hfin

/-! ## The fold — `evalCount(whole transform run) = Σ blockContribution`

`srcContrib` is the **source-side** trace summing the per-block contribution along the source run (an
instrumentation of `step1`, like `evalCount`). `evalCount_fold` inducts on the source `StepsH` (mirroring
`sim`), chaining `block_evalCount` + `run_add` + `evalCount_add`: the transform's total eval count over its
whole run equals `srcContrib` over the source run. This is the quantity the eval-count optimality theorems
compare against the abstract safe-placement `Place`. -/

/-- Source-side contribution trace: sum of the per-edge `blockContribution` along the source run from `c`.
    Edge-indexed (the taken successor `c'` supplies the edge inserts); a `halt`/stuck step contributes `0`. -/
def srcContrib (P : Program) (S : LcmSpec P) (e : Expr) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      match step1 P c with
      | .next c' => blockContribution P S c.node c'.node e + srcContrib P S e c' fuel
      | _        => 0

/-- Per-step recursion for `srcContrib`. -/
theorem srcContrib_next {P : Program} {S : LcmSpec P} {e : Expr} {c c' : Config} {fuel : Nat}
    (h : step1 P c = .next c') :
    srcContrib P S e c (fuel + 1) = blockContribution P S c.node c'.node e + srcContrib P S e c' fuel := by
  show (match step1 P c with
        | .next c'' => blockContribution P S c.node c''.node e + srcContrib P S e c'' fuel | _ => 0) = _
  rw [h]

/-- **The phase-2 fold.** Along a halting source run from `c`, the transform's whole-run eval count of `e`
    equals the source-side contribution sum. (`d` matches `c`; `kt` is the sum of the per-block fuels.) -/
theorem evalCount_fold {P : Program} (S : LcmSpec P) (hg : GateSound P S) (e : Expr) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f →
    ∀ {d : Config} {M : Assignments}, Match P S c d M →
      Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) → Cov S c.node M →
    ∃ kt τf, run (transform P S) d kt
              = (⟨blockOff P S c_f.node, τf⟩, .next ⟨blockOff P S c_f.node, τf⟩)
          ∧ ∀ ks, run P c ks = (c_f, .next c_f) →
              evalCount (transform P S) e d kt = srcContrib P S e c ks := by
  intro c c_f hrun
  induction hrun with
  | @refl c0 =>
      intro hfin d M hm hpa hcov
      obtain ⟨dn, dσ⟩ := d
      obtain ⟨hlabel, -, -, -⟩ := hm
      subst hlabel
      refine ⟨0, dσ, by simp [run], ?_⟩
      intro ks hks
      cases ks with
      | zero => rfl
      | succ k =>
          exfalso
          have hh : step1 P c0 = .halt := by
            unfold step1; rw [show P.fetch c0.node = some .halt from hfin]
          rw [show run P c0 (k + 1) = (c0, .halt) from by simp [run, hh]] at hks
          simp at hks
  | @head c c1 cf hstep htail ih =>
      intro hfin d M hm hpa hcov
      obtain ⟨τF, hblockrun, hm1, hcnt_block⟩ := block_evalCount S hg e hm hpa hcov hstep htail hfin
      obtain ⟨kt1, τf, hrun1, hcnt1⟩ :=
        ih hfin hm1 (postpSubAnti_step S hstep hpa) (Cov_step_edge S hg hstep hcov)
      refine ⟨blockFuel P S c.node c1.node + kt1, τf, ?_, ?_⟩
      · rw [run_add hblockrun]; exact hrun1
      · intro ks hks
        have hstepf : step1 P c = .next c1 := step1_next_iff.mpr hstep
        cases ks with
        | zero =>
            exfalso
            rw [show run P c 0 = (c, .next c) from rfl] at hks
            have hcf : c = cf := ((Prod.mk.injEq _ _ _ _).mp hks).1
            subst hcf
            simp only [Final] at hfin
            cases hstep <;> simp_all
        | succ k =>
            have hk : run P c1 k = (cf, .next cf) := by
              rw [show run P c (k + 1) = run P c1 k from by simp [run, hstepf]] at hks; exact hks
            rw [evalCount_add hblockrun, hcnt_block, hcnt1 k hk, srcContrib_next hstepf]

/-- **Fold at the entry (instantiation).** On a halting source run from the entry, the transform's
    whole-run eval count of `e` equals `srcContrib` over the source run — the operational count `=` the
    source-side per-block contribution sum. The handle for comparing `srcContrib_S` to a safe placement
    `Place`. -/
theorem transform_evalCount {P : Program} (S : LcmSpec P) (hg : GateSound P S) (e : Expr)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ kt τf, run (transform P S) ⟨blockOff P S P.entry, σ⟩ kt
              = (⟨blockOff P S c_f.node, τf⟩, .next ⟨blockOff P S c_f.node, τf⟩)
          ∧ ∀ ks, run P ⟨P.entry, σ⟩ ks = (c_f, .next c_f) →
              evalCount (transform P S) e ⟨blockOff P S P.entry, σ⟩ kt
                = srcContrib P S e ⟨P.entry, σ⟩ ks := by
  exact evalCount_fold S hg e (steps_toH hrun) hfin (match_init S σ) (postpSubAnti_entry S)
    (Cov_entry S hg)

end BaseLanguage.Analyses.LCM
