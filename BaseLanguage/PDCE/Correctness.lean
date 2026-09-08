-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Layout

/-!
# `PDCE.Correctness` — the behavior-preservation proof

Forward simulation of `transform P S` against `P` on **halting runs** (faults are don't-care;
divergence preservation is proved separately in `PDCE.Divergence`, reusing the plus-form
`match_step` below). The whole chain is sorry-free.

Proof sequence (see PDCE.md §4, §7.2):

  1. layout/structural          — `transform_wellFormed`/`_entry`/`_obs`/`_size`, `transform_fetch`     [Layout.lean]
  2. chain execution            — `steps_assignSeg`/`steps_edgeSeg` (order-independent materialization)
  3. block step                 — one source step ↦ one transform block reaching the same label        [in `match_step`]
  4. ghost glue                 — `isSink.{update,bound}`, `isLive.{predict,gate,floor}`        [used in 5]
  5. `match_step`               — `Match` preserved across one source step (4 instruction cases)
  6. `match_steps`              — multi-step lift                                                        [from 5]
  7. boundary                   — `match_init`, `match_final_obs`
  8. `transform_preserves_halt` — compose 6 + 7

Where the bundle is consumed:
  • `isSink` (Sink validity, incl. `bound`)   → step 5 (deferred-set evolution; ceiling for `pass`)
  • `isLive` (Live validity)                  → step 5 (branch sync `floor`, operand freshness
                                                 `gate`, liveness propagation `predict`), step 7 (obs at halt `seed`)
  • `Extremal.π`/`.η` (extremality)     → optimality only (separate file)

The `Match` relation (PDCE.md §7.2): same block-label, liveness-guarded store
agreement, recoverability, and a non-interference (`Indep`) clause; `live` is variable-granular.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

-- `steps_trans` is a shared reference-semantics lemma hoisted to `IR.TAC` (`namespace Semantics`).

/-- **Front-decomposition of a non-empty run.** A run `Steps P a b` extended by one more `Step P b c`
    is a *leading* `Step P a mid` then a `Steps P mid c` tail. This exposes the ≥ 1-step content of a
    block execution (the block head) that `diverges_of_stepsimG` consumes; the base case (`refl`, so
    `a = b`) *is* the extending step, and the tail case grafts the extending step onto the recursively
    peeled tail. -/
theorem steps_tail_head {P : Program} {a b : Config} (h : Steps P a b) :
    ∀ {c : Config}, Step P b c → ∃ mid, Step P a mid ∧ Steps P mid c := by
  induction h with
  | refl => intro c hs; exact ⟨c, hs, Steps.refl⟩
  | tail _ hstep ih =>
      intro c hs
      obtain ⟨mid, hlead, hrest⟩ := ih hstep
      exact ⟨mid, hlead, Steps.tail hrest hs⟩

/-! ## Evaluation under point updates

`eval_update_not_read`/`evalAtom_update_not_read` (a store update at `w` does not change the value of an
expression that does not read `w`) are shared reference-semantics lemmas hoisted to `IR.TAC`. -/

/-- `evalAtom` depends only on the variable the atom reads. -/
theorem evalAtom_congr {τ1 τ : Store} {a : Atom}
    (h : ∀ v, atomReadsVar a v = true → τ1 v = τ v) : evalAtom τ1 a = evalAtom τ a := by
  cases a with
  | var x => simp only [evalAtom]; exact h x (by simp [atomReadsVar])
  | imm n => rfl

/-- Two stores agreeing on every variable an expression reads evaluate it identically. -/
theorem eval_congr {τ1 τ : Store} {e : Expr}
    (h : ∀ v, exprReadsVar e v = true → τ1 v = τ v) : eval τ1 e = eval τ e := by
  cases e with
  | atom a => simp only [eval, evalAtom_congr (fun v hv => h v (by simpa [exprReadsVar] using hv))]
  | una op a => simp only [eval, evalAtom_congr (fun v hv => h v (by simpa [exprReadsVar] using hv))]
  | bin op a b =>
      simp only [eval,
        evalAtom_congr (a := a) (fun v hv => h v (by simp [exprReadsVar, hv])),
        evalAtom_congr (a := b) (fun v hv => h v (by simp [exprReadsVar, hv]))]

/-! ## Straight-line execution of a materialization chain

The reusable operational core: a list `m` of assignments, laid out at consecutive slots `s0, s0+1, …`
with slot `k` transferring to `s0+k+1`, runs straight-line from `⟨s0, τ⟩` to `⟨s0 + m.length, τ'⟩`.
Under the *recoverability* (each rhs evaluates in `τ` to its intended value) and *non-interference*
(distinct lhs, no rhs reads another's lhs) side-conditions, the run never faults and the final store
`τ'` sets each `a.lhs` to its intended value `vals a.lhs` and leaves all other variables at `τ`. -/

/-- The `k`-th instruction of a `matChain` (slot `k` jumps to `s0+k+1`). -/
theorem matChain_getElem? {m : List Asgn} {s0 k : Nat} (hk : k < m.length) :
    (matChain m s0)[k]? = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs (s0 + k + 1)) := by
  unfold matChain
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk]
  simp

theorem steps_assignSeg {Q : Program} :
    ∀ (m : List Asgn) (s0 : Nat) (τ : Store) (vals : Var → Val),
    m.Nodup →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs (s0 + k + 1))) →
    (∀ a ∈ m, eval τ a.rhs = some (vals a.lhs)) →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → exprReadsVar a.rhs b.lhs = false) →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → a.lhs ≠ b.lhs) →
    ∃ τ', Steps Q ⟨s0, τ⟩ ⟨s0 + m.length, τ'⟩
        ∧ (∀ v, (∀ a ∈ m, a.lhs ≠ v) → τ' v = τ v)
        ∧ (∀ a ∈ m, τ' a.lhs = vals a.lhs) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ vals _ _ _ _ _
      exact ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ vals hnodup hfetch hrec hfresh hdist
      -- first step materializes `a`
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hfetch0 : Q.fetch (s0 + 0) = some (.assign a.lhs a.rhs (s0 + 0 + 1)) := hfetch 0 (by simp)
      have heval0 : eval τ a.rhs = some (vals a.lhs) := hrec a ha_mem
      have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update a.lhs (vals a.lhs)⟩ := by
        have := Step.assign (by simpa using hfetch0) (by simpa using heval0)
        simpa using this
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      -- assemble IH hypotheses for `rest` at base `s0+1`
      have hfetch' : ∀ k (hk : k < rest.length),
          Q.fetch ((s0 + 1) + k) = some (.assign (rest[k]'hk).lhs (rest[k]'hk).rhs ((s0 + 1) + k + 1)) := by
        intro k hk
        have hk' : k + 1 < (a :: rest).length := by simp; omega
        have := hfetch (k + 1) hk'
        have hidx : (a :: rest)[k+1]'hk' = rest[k]'hk := by simp
        rw [hidx] at this
        rw [show s0 + 1 + k = s0 + (k + 1) from by omega]
        exact this
      have hrec' : ∀ b ∈ rest, eval (τ.update a.lhs (vals a.lhs)) b.rhs = some (vals b.lhs) := by
        intro b hb
        have hab : a ≠ b := fun h => hnotin (h ▸ hb)
        have hbr : exprReadsVar b.rhs a.lhs = false :=
          hfresh b (List.mem_cons_of_mem _ hb) a ha_mem (Ne.symm hab)
        rw [eval_update_not_read hbr]; exact hrec b (List.mem_cons_of_mem _ hb)
      have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → exprReadsVar x.rhs y.lhs = false :=
        fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → x.lhs ≠ y.lhs :=
        fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      obtain ⟨τ', hsteps, hoff, hon⟩ :=
        ih (s0 + 1) (τ.update a.lhs (vals a.lhs)) vals hrest_nodup hfetch' hrec' hfresh' hdist'
      refine ⟨τ', ?_, ?_, ?_⟩
      · have hlen : (s0 + 1) + rest.length = s0 + (a :: rest).length := by simp; omega
        rw [hlen] at hsteps
        exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
      · intro v hv
        have hav : a.lhs ≠ v := hv a ha_mem
        have heq : τ' v = (τ.update a.lhs (vals a.lhs)) v :=
          hoff v (fun b hb => hv b (List.mem_cons_of_mem _ hb))
        rw [heq, Store.update, if_neg (fun h => hav h.symm)]
      · intro x hx
        rcases List.mem_cons.mp hx with heq | hx
        · -- x = a: its lhs is untouched by `rest` (distinct lhs)
          rw [heq]
          have hno : ∀ b ∈ rest, b.lhs ≠ a.lhs := fun b hb =>
            hdist b (List.mem_cons_of_mem _ hb) a ha_mem (fun h => hnotin (h ▸ hb))
          have heq2 : τ' a.lhs = (τ.update a.lhs (vals a.lhs)) a.lhs := hoff a.lhs hno
          rw [heq2, Store.update, if_pos rfl]
        · exact hon x hx

/-- The `k`-th instruction of an `edgeChain` (slot `k` jumps to `target` if last, else `start+k+1`). -/
theorem edgeChain_getElem? {e : List Asgn} {start target k : Nat} (hk : k < e.length) :
    (edgeChain e start target)[k]? =
      some (.assign (e[k]'hk).lhs (e[k]'hk).rhs
        (if k + 1 == e.length then target else start + k + 1)) := by
  unfold edgeChain
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk]
  simp

/-- **Fault-aware edge chain.** Either the chain faults partway — the target is then `Faulting` at that
    slot — or every entry evaluates. The fault-preserving mode needs exactly this: a non-sinkable
    assignment is materialized in its birth block's edge chain, and it is the one entry whose evaluation
    may be `none`. Mirrors `LCM.ChainExec.steps_insSeg_fault`. -/
theorem steps_edgeSeg_fault {Q : Program} (target : Nat) :
    ∀ (m : List Asgn) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → exprReadsVar a.rhs b.lhs = false) →
    (∃ cf, Steps Q ⟨s0, τ⟩ cf ∧ Faulting Q cf) ∨ (∀ a ∈ m, eval τ a.rhs ≠ none) := by
  intro m
  induction m with
  | nil => intro s0 τ _ _ _; exact Or.inr (fun a h => by simp at h)
  | cons a rest ih =>
      intro s0 τ hnodup hfetch hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨tgt0, htgt0⟩ : ∃ t, Q.fetch s0 = some (.assign a.lhs a.rhs t) := by
        have h := hfetch 0 (by simp); exact ⟨_, by simpa using h⟩
      cases hva : eval τ a.rhs with
      | none => exact Or.inl ⟨⟨s0, τ⟩, Steps.refl, a.lhs, a.rhs, tgt0, htgt0, hva⟩
      | some va =>
          by_cases hre : rest = []
          · subst hre
            refine Or.inr (fun b hb => ?_)
            rcases List.mem_cons.mp hb with rfl | hb
            · rw [hva]; exact Option.some_ne_none _
            · simp at hb
          · have hrne : ¬ (0 + 1 == (a :: rest).length) = true := by
              cases rest with | nil => exact absurd rfl hre | cons _ _ => simp
            have hf0 : Q.fetch (s0 + 0) = some (.assign a.lhs a.rhs (s0 + 0 + 1)) := by
              have h := hfetch 0 (by simp); rw [if_neg hrne] at h; exact h
            have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update a.lhs va⟩ := by
              have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
            have hfetch' : ∀ k (hk : k < rest.length),
                Q.fetch ((s0 + 1) + k) = some (.assign (rest[k]'hk).lhs (rest[k]'hk).rhs
                  (if k + 1 == rest.length then target else (s0 + 1) + k + 1)) := by
              intro k hk
              have hk' : k + 1 < (a :: rest).length := by simp; omega
              have h := hfetch (k + 1) hk'
              have hidx : (a :: rest)[k+1]'hk' = rest[k]'hk := by simp
              rw [hidx] at h
              have hcond : (k + 1 + 1 == (a :: rest).length) = (k + 1 == rest.length) := by simp
              rw [hcond] at h
              rw [show (s0 + 1) + k = s0 + (k + 1) from by omega]
              exact h
            have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → exprReadsVar x.rhs y.lhs = false :=
              fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
            rcases ih (s0 + 1) (τ.update a.lhs va) hrest_nodup hfetch' hfresh' with
              ⟨cf, hsteps, hfl⟩ | hclean
            · exact Or.inl ⟨cf, steps_trans (Steps.tail Steps.refl hstep0) hsteps, hfl⟩
            · refine Or.inr (fun b hb => ?_)
              rcases List.mem_cons.mp hb with rfl | hb
              · rw [hva]; exact Option.some_ne_none _
              · have hne : b ≠ a := fun h => (List.nodup_cons.mp hnodup).1 (h ▸ hb)
                have hc := hclean b hb
                rwa [eval_update_not_read
                  (hfresh b (List.mem_cons_of_mem _ hb) a ha_mem hne)] at hc

/-- Edge-chain variant of `steps_assignSeg`: the final assignment jumps to `target` rather than to the
    next slot, so a non-empty chain run lands on `target`. -/
theorem steps_edgeSeg {Q : Program} (target : Nat) :
    ∀ (m : List Asgn) (s0 : Nat) (τ : Store) (vals : Var → Val),
    m.Nodup →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ a ∈ m, eval τ a.rhs = some (vals a.lhs)) →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → exprReadsVar a.rhs b.lhs = false) →
    (∀ a ∈ m, ∀ b ∈ m, a ≠ b → a.lhs ≠ b.lhs) →
    ∃ τ', Steps Q ⟨s0, τ⟩ ⟨(if m.isEmpty then s0 else target), τ'⟩
        ∧ (∀ v, (∀ a ∈ m, a.lhs ≠ v) → τ' v = τ v)
        ∧ (∀ a ∈ m, τ' a.lhs = vals a.lhs) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ vals _ _ _ _ _
      exact ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ vals hnodup hfetch hrec hfresh hdist
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hre : rest = []
      · -- singleton: the lone assignment jumps straight to `target`
        subst hre
        have hf0 : Q.fetch (s0 + 0) = some (.assign a.lhs a.rhs target) := by
          have := hfetch 0 (by simp); simpa using this
        have heval0 : eval τ a.rhs = some (vals a.lhs) := hrec a ha_mem
        have hstep0 : Step Q ⟨s0, τ⟩ ⟨target, τ.update a.lhs (vals a.lhs)⟩ := by
          have := Step.assign (by simpa using hf0) heval0; simpa using this
        refine ⟨τ.update a.lhs (vals a.lhs), ?_, ?_, ?_⟩
        · simpa using Steps.tail Steps.refl hstep0
        · intro v hv
          rw [Store.update, if_neg (fun h => (hv a ha_mem) h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · rw [heq, Store.update, if_pos rfl]
          · simp at hx
      · -- non-empty tail: head jumps to `s0+1`, then recurse
        have hlen2 : 1 < (a :: rest).length := by
          cases rest with | nil => exact absurd rfl hre | cons _ _ => simp
        have hf0 : Q.fetch (s0 + 0) = some (.assign a.lhs a.rhs (s0 + 0 + 1)) := by
          have := hfetch 0 (by simp)
          rw [if_neg (by simp; omega)] at this; simpa using this
        have heval0 : eval τ a.rhs = some (vals a.lhs) := hrec a ha_mem
        have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update a.lhs (vals a.lhs)⟩ := by
          have := Step.assign (by simpa using hf0) (by simpa using heval0); simpa using this
        have hfetch' : ∀ k (hk : k < rest.length),
            Q.fetch ((s0 + 1) + k) = some (.assign (rest[k]'hk).lhs (rest[k]'hk).rhs
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
          · rw [if_neg (by simpa using hc)] at this ⊢
            exact this
          · rw [if_pos (by simpa using hc)] at this ⊢; exact this
        have hrec' : ∀ b ∈ rest, eval (τ.update a.lhs (vals a.lhs)) b.rhs = some (vals b.lhs) := by
          intro b hb
          have hab : a ≠ b := fun h => hnotin (h ▸ hb)
          have hbr : exprReadsVar b.rhs a.lhs = false :=
            hfresh b (List.mem_cons_of_mem _ hb) a ha_mem (Ne.symm hab)
          rw [eval_update_not_read hbr]; exact hrec b (List.mem_cons_of_mem _ hb)
        have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → exprReadsVar x.rhs y.lhs = false :=
          fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → x.lhs ≠ y.lhs :=
          fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        obtain ⟨τ', hsteps, hoff, hon⟩ :=
          ih (s0 + 1) (τ.update a.lhs (vals a.lhs)) vals hrest_nodup hfetch' hrec' hfresh' hdist'
        rw [if_neg (by simpa using hre)] at hsteps
        refine ⟨τ', ?_, ?_, ?_⟩
        · rw [show (a :: rest).isEmpty = false from by simp, if_neg (by simp)]
          exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
        · intro v hv
          have hav : a.lhs ≠ v := hv a ha_mem
          have heq : τ' v = (τ.update a.lhs (vals a.lhs)) v :=
            hoff v (fun b hb => hv b (List.mem_cons_of_mem _ hb))
          rw [heq, Store.update, if_neg (fun h => hav h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · rw [heq]
            have hno : ∀ b ∈ rest, b.lhs ≠ a.lhs := fun b hb =>
              hdist b (List.mem_cons_of_mem _ hb) a ha_mem (fun h => hnotin (h ▸ hb))
            have heq2 : τ' a.lhs = (τ.update a.lhs (vals a.lhs)) a.lhs := hoff a.lhs hno
            rw [heq2, Store.update, if_pos rfl]
          · exact hon x hx

/-! ## Bridging `Assignments.toList` to set membership

The materialization chains are `(…).toList` of `Assignments` sets; these expose membership and no-duplication. -/

theorem Assignments.mem_toList {F : Assignments} {a : Asgn} : a ∈ F.toList ↔ a ∈ F :=
  Std.HashSet.mem_toList

theorem Assignments.nodup_toList {F : Assignments} : F.toList.Nodup :=
  Std.HashSet.distinct_toList.imp (fun {a b} h hab => by subst hab; simp at h)

theorem mem_matNode {P : Program} {S : PdceSpec P} {i : Node} {a : Asgn} :
    a ∈ matNode P S i ↔ a ∈ S.ηK i ∧ a ∈ blockedSet P i ∧ a.lhs ∈ S.π i := by
  unfold matNode
  rw [Assignments.mem_toList, mem_liveFilter, Assignments.mem_inter, and_assoc]

theorem mem_matEdge {P : Program} {S : PdceSpec P} {p s : Node} {a : Asgn} :
    a ∈ matEdge P S p s ↔
      a ∈ delayedExit P S p ∧ a ∉ S.ηK s ∧ (a.lhs ∈ S.π s ∨ S.keep a = false) := by
  unfold matEdge
  rw [Assignments.mem_toList, mem_liveFilterK, Assignments.mem_sdiff, and_assoc]

theorem mem_delayedExit {P : Program} {S : PdceSpec P} {i : Node} {a : Asgn} :
    a ∈ delayedExit P S i ↔ a ∈ born P i ∨ (a ∈ S.ηK i ∧ a ∈ pass P i) := by
  unfold delayedExit; rw [Assignments.mem_union, Assignments.mem_inter]

/-- Membership in the **unfiltered** deferral candidates — the exact RHS of `Sink.update`. Distinct from
    `mem_delayedExit`, which describes the *filtered* set the transform actually carries. -/
theorem mem_deferCand {P : Program} {S : PdceSpec P} {i : Node} {a : Asgn} :
    a ∈ Assignments.union (born P i) (Assignments.inter (S.η i) (pass P i))
      ↔ a ∈ born P i ∨ (a ∈ S.η i ∧ a ∈ pass P i) := by
  rw [Assignments.mem_union, Assignments.mem_inter]

theorem delayedExit_sub {P : Program} (S : PdceSpec P) (i : Node) :
    (delayedExit P S i).Subset (Assignments.union (born P i) (Assignments.inter (S.η i) (pass P i))) := by
  intro a ha
  rw [mem_delayedExit] at ha
  rw [Assignments.mem_union, Assignments.mem_inter]
  exact ha.imp id (fun h => ⟨ηK_sub S i a h.1, h.2⟩)

/-- For a **sinkable** assignment the `liveFilterK` disjunction collapses to plain liveness. -/
theorem keep_live_of_matEdge {P : Program} {S : PdceSpec P} {s : Node} {a : Asgn}
    (hk : S.keep a = true) (h : a.lhs ∈ S.π s ∨ S.keep a = false) : a.lhs ∈ S.π s :=
  h.resolve_right (fun hf => by rw [hk] at hf; exact Bool.noConfusion hf)

/-- A **deferred** assignment is by definition sinkable, so the `liveFilterK` escape cannot fire for it —
    its liveness disjunct is the only live one. This keeps the classical argument intact everywhere the
    candidate came from the sink set rather than from `born`. -/
theorem live_of_mem_ηK {P : Program} {S : PdceSpec P} {p s : Node} {a : Asgn}
    (hK : a ∈ S.ηK p) (h : a.lhs ∈ S.π s ∨ S.keep a = false) : a.lhs ∈ S.π s :=
  h.resolve_right (fun hf => by rw [(mem_ηK.mp hK).2] at hf; exact Bool.noConfusion hf)

theorem matNode_nodup {P : Program} {S : PdceSpec P} {i : Node} : (matNode P S i).Nodup :=
  Assignments.nodup_toList
theorem matEdge_nodup {P : Program} {S : PdceSpec P} {p s : Node} : (matEdge P S p s).Nodup :=
  Assignments.nodup_toList

/-! ## Syntactic facts about `born` / `pass` (for non-interference maintenance) -/

theorem Assignments.mem_singleton {a b : Asgn} : a ∈ Assignments.singleton b ↔ a = b := by
  unfold Assignments.singleton
  rw [Std.HashSet.mem_insert]
  constructor
  · rintro (h | h)
    · exact (eq_of_beq h).symm
    · exact absurd h Std.HashSet.not_mem_empty
  · rintro rfl; exact Or.inl (beq_self_eq_true _)

/-- A member of `born i` is exactly the assignment floated at `i`. -/
theorem mem_born {P : Program} {i : Node} {a : Asgn} (ha : a ∈ born P i) :
    ∃ next, P.fetch i = some (.assign a.lhs a.rhs next) := by
  unfold born at ha
  split at ha
  · next x e next heq => rw [Assignments.mem_singleton] at ha; subst ha; exact ⟨next, heq⟩
  · exact absurd ha Std.HashSet.not_mem_empty

/-- Membership in `pass`: in the candidate universe and not killed at `i`. -/
theorem mem_transp {P : Program} {n : Node} {a : Asgn} :
    a ∈ pass P n ↔ a ∈ allAsgns P ∧ kills P n a = false := by
  unfold pass; rw [Assignments.mem_filter', Bool.not_eq_true']

/-- A candidate transparent at `i` is not used, not redefined, and its rhs is not clobbered by `i`. -/
theorem transp_facts {P : Program} {i : Node} {b : Asgn} (hb : b ∈ pass P i) :
    b.lhs ∉ useV P i ∧ defV P i ≠ some b.lhs ∧ ∀ w, defV P i = some w → exprReadsVar b.rhs w = false := by
  unfold pass at hb
  rw [Assignments.mem_filter'] at hb
  have hk : kills P i b = false := by have := hb.2; simpa using this
  unfold kills at hk
  rw [Bool.or_eq_false_iff, Bool.or_eq_false_iff] at hk
  obtain ⟨⟨hA, hB⟩, hC⟩ := hk
  refine ⟨?_, ?_, ?_⟩
  · simpa using hA
  · simpa using hB
  · intro w hw; rw [hw] at hC; simpa using hC

/-! ## The forward-simulation relation

Target lags the source by exactly the in-flight (sunk) assignments: stores agree off the deferred set,
and each deferred `⟨x,e⟩` is recoverable (its rhs still evaluates, in the target store, to the value the
source already holds for `x`). -/
/-- **Non-interference** of a candidate set: distinct members have distinct lhs, and no member's lhs is
    read by another member's rhs. This makes the *sequential* materialization of a deferred set behave
    like a *parallel* assignment (order-independent), so each lhs ends at its recovered value. Holds for
    the greatest `sink` (a MUST analysis: at a merge it intersects, and on each single path an
    interfering pair would have one birth kill the other's delayability) and is maintained locally across
    one step from `Sink.update` + `pass`. -/
def Indep (F : Assignments) : Prop :=
  ∀ a ∈ F, ∀ b ∈ F, a ≠ b → a.lhs ≠ b.lhs ∧ exprReadsVar b.rhs a.lhs = false

/-- **The forward-simulation relation.** Source `c` and target `d` sit at the same (block-)label; the
    stores agree on every **live, not-in-flight** variable (clause 2 — dead deferred stores PDCE drops
    may legitimately disagree); each deferred `⟨x,e⟩` is **recoverable** (clause 3); and the deferred set
    is **non-interfering** (clause 4).

    With variable-granular `live`, a *never-assigned* observable is live at `halt` (the seed is all of
    `obs`) and never in flight, so clause 2 covers it — no separate non-candidate clause is needed, and
    "a live variable's pending store is never dropped" is structural (`matEdge` gates on `a.lhs ∈ live`),
    so no lhs-saturation hypothesis is required. -/
def Match (P : Program) (S : PdceSpec P) (c d : Config) : Prop :=
  d.node = blockOff P S c.node ∧
  (∀ x : Var, x ∈ S.π c.node →
      (∀ e' : Expr, (⟨x, e'⟩ : Asgn) ∉ S.ηK c.node) → d.store x = c.store x) ∧
  (∀ x : Var, ∀ e : Expr, (⟨x, e⟩ : Asgn) ∈ S.ηK c.node → x ∈ S.π c.node →
      eval d.store e = some (c.store x)) ∧
  Indep (S.η c.node)

/-- **`delayedExit i` is non-interfering** when `sink i` is. This is the syntactic core: a member is
    either the freshly-floated `born i` or a transparent in-flight candidate, and the `pass`/`born`
    constraints forbid any lhs/rhs interference between the two kinds (and `Indep (sink i)` handles two
    in-flight ones). -/
theorem Indep_deferCand {P : Program} (S : PdceSpec P) {i : Node} (hindep : Indep (S.η i))
    {a b : Asgn}
    (ha : a ∈ Assignments.union (born P i) (Assignments.inter (S.η i) (pass P i)))
    (hb : b ∈ Assignments.union (born P i) (Assignments.inter (S.η i) (pass P i)))
    (hab : a ≠ b) :
    a.lhs ≠ b.lhs ∧ exprReadsVar b.rhs a.lhs = false := by
  rw [Assignments.mem_union] at ha hb
  rcases ha with hba | hai
  · -- a freshly floated at `i`
    obtain ⟨na, hfa⟩ := mem_born hba
    have hdefa : defV P i = some a.lhs := by unfold defV; rw [hfa]; rfl
    rcases hb with hbb | hbi
    · -- both floated ⇒ equal, contradiction
      obtain ⟨nb, hfb⟩ := mem_born hbb
      rw [hfa] at hfb
      exact absurd (by cases a; cases b; simp_all) hab
    · rw [Assignments.mem_inter] at hbi
      obtain ⟨hbu, hbd, hbc⟩ := transp_facts hbi.2
      exact ⟨fun heq => hbd (heq ▸ hdefa), hbc a.lhs hdefa⟩
  · rw [Assignments.mem_inter] at hai
    obtain ⟨hau, had, hac⟩ := transp_facts hai.2
    rcases hb with hbb | hbi
    · -- b freshly floated at `i`
      obtain ⟨nb, hfb⟩ := mem_born hbb
      have hdefb : defV P i = some b.lhs := by unfold defV; rw [hfb]; rfl
      have huseb : useV P i = exprVars b.rhs := by unfold useV; rw [hfb]; rfl
      refine ⟨fun heq => had (heq ▸ hdefb), ?_⟩
      rcases Bool.eq_false_or_eq_true (exprReadsVar b.rhs a.lhs) with h | h
      · exact absurd (show a.lhs ∈ useV P i by rw [huseb]; exact readsVar_imp_mem h) hau
      · exact h
    · rw [Assignments.mem_inter] at hbi
      exact hindep a hai.1 b hbi.1 hab

/-- Non-interference for the *filtered* in-flight set — the form the materialization chains consume. -/
theorem Indep_delayedExit {P : Program} (S : PdceSpec P) {i : Node} (hindep : Indep (S.η i))
    {a b : Asgn} (ha : a ∈ delayedExit P S i) (hb : b ∈ delayedExit P S i) (hab : a ≠ b) :
    a.lhs ≠ b.lhs ∧ exprReadsVar b.rhs a.lhs = false :=
  Indep_deferCand S hindep (delayedExit_sub S i a ha) (delayedExit_sub S i b hb) hab

/-- **Non-interference is maintained across one step** (the new deferred set sits inside
    `born i ∪ (sink i ∩ pass i)` by `Sink.update`). -/
theorem Indep_step {P : Program} (S : PdceSpec P) {c c' : Config} (hstep : Step P c c')
    (hindep : Indep (S.η c.node)) : Indep (S.η c'.node) := by
  intro a ha b hb hab
  have hsub := S.isSink.update c c' hstep
  exact Indep_deferCand S hindep (hsub a ha) (hsub b hb) hab

/-! ## Step 1 — structural / layout

Proved in `BaseLanguage.PDCE.Layout`: `transform_entry`, `transform_obs`, `transform_size`,
`transform_wellFormed` (`entry_lt` and `succ_lt` both discharged, the latter via `block_inrange`). -/

theorem matChain_length {m : List Asgn} {s0 : Nat} : (matChain m s0).length = m.length := by
  unfold matChain; rw [List.length_map, List.length_zipIdx]

theorem edgeChain_length {e : List Asgn} {start target : Nat} :
    (edgeChain e start target).length = e.length := by
  unfold edgeChain; rw [List.length_map, List.length_zipIdx]

/-- The `matNode` materialization chain runs from a block head, materializing every blocked-and-live
    in-flight candidate to its **source** value (`σ = c.store`), leaving all other variables alone. -/
theorem matNode_exec {P : Program} (S : PdceSpec P) {i : Node} (hi : i < P.size) {τ σ : Store}
    (hrec : ∀ a ∈ matNode P S i, eval τ a.rhs = some (σ a.lhs))
    (hindep : Indep (S.η i)) :
    ∃ τ1, Steps (transform P S) ⟨blockOff P S i, τ⟩
            ⟨blockOff P S i + (matNode P S i).length, τ1⟩
        ∧ (∀ v, (∀ a ∈ matNode P S i, a.lhs ≠ v) → τ1 v = τ v)
        ∧ (∀ a ∈ matNode P S i, τ1 a.lhs = σ a.lhs) := by
  have hsink : ∀ a ∈ matNode P S i, a ∈ S.η i := fun a ha => ηK_sub S i a (mem_matNode.mp ha).1
  refine steps_assignSeg (matNode P S i) (blockOff P S i) τ σ matNode_nodup ?_ ?_ ?_ ?_
  · intro k hk
    have hkb : k < (block P S i).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (matChain (matNode P S i) (blockOff P S i)).length := by
      rw [matChain_length]; exact hk
    have happ : (block P S i)[k]? = (matChain (matNode P S i) (blockOff P S i))[k]? := by
      simp only [block]; rw [List.getElem?_append_left hml]
    rw [transform_fetch hi hkb, happ, matChain_getElem? hk]
  · exact hrec
  · intro a ha b hb hab
    exact (hindep b (hsink b hb) a (hsink a ha) (Ne.symm hab)).2
  · intro a ha b hb hab
    exact (hindep a (hsink a ha) b (hsink b hb) hab).1

/-- Indexing past the `matChain` prefix of a block: slot `|m| + j` is the `j`-th tail instruction. -/
theorem matChain_append_get {m : List Asgn} {s0 : Nat} {tail : List Cmd} {j : Nat} :
    (matChain m s0 ++ tail)[m.length + j]? = tail[j]? := by
  rw [List.getElem?_append_right (by rw [matChain_length]; omega)]
  congr 1; rw [matChain_length]; omega

/-- Run a per-successor `edgeChain` (given its fetch facts), materializing it order-independently to
    `vals`; non-interference comes from `Indep_delayedExit` (the edge ⊆ `delayedExit i`). -/
theorem edge_run {P : Program} (S : PdceSpec P) {i s : Node} (hindep : Indep (S.η i))
    (τ1 : Store) (vals : Var → Val) (est : Nat)
    (hfetch : ∀ k (hk : k < (matEdge P S i s).length),
      (transform P S).fetch (est + k) = some (.assign ((matEdge P S i s)[k]'hk).lhs
        ((matEdge P S i s)[k]'hk).rhs
        (if k + 1 == (matEdge P S i s).length then blockOff P S s else est + k + 1)))
    (hrec : ∀ a ∈ matEdge P S i s, eval τ1 a.rhs = some (vals a.lhs)) :
    ∃ τ2, Steps (transform P S) ⟨est, τ1⟩
            ⟨(if (matEdge P S i s).isEmpty then est else blockOff P S s), τ2⟩
        ∧ (∀ v, (∀ a ∈ matEdge P S i s, a.lhs ≠ v) → τ2 v = τ1 v)
        ∧ (∀ a ∈ matEdge P S i s, τ2 a.lhs = vals a.lhs) :=
  steps_edgeSeg (blockOff P S s) (matEdge P S i s) est τ1 vals matEdge_nodup hfetch hrec
    (fun _ ha _ hb hab => (Indep_delayedExit S hindep (mem_matEdge.mp hb).1 (mem_matEdge.mp ha).1 (Ne.symm hab)).2)
    (fun _ ha _ hb hab => (Indep_delayedExit S hindep (mem_matEdge.mp ha).1 (mem_matEdge.mp hb).1 hab).1)

/-! ## Step 5 — the simulation step-case

Combines the block-execution lemmas (a node's `matNode`/`matEdge` chains run straight-line to the
successor label) with the ghost invariant: the deferred set evolves `S.η c.node → S.η c'.node`
via `isSink.update`, the freshly-floated assignment is tracked via the same rule's `born` clause, branch
direction agrees via `isLive.check`, recoverability is preserved by `pass`, and operand
freshness across the float comes from the strong-liveness gate `isLive.gate`. -/
theorem match_step {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    {c c' d : Config} (hm : Match P S c d) (hstep : Step P c c') :
    ∃ mid d', Step (transform P S) d mid ∧ Steps (transform P S) mid d' ∧ Match P S c' d' := by
  obtain ⟨hnode, h2, hrec, hindep⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  cases hstep with
  | noop hf =>
    rename_i nd σ next
    -- i = nd, σ source store, next successor; dσ target store at blockOff nd
    subst hnode
    have hi : nd < P.size := fetch_lt hf
    have hnext : next < P.size := wf.succ_lt hf (by simp [Cmd.succs])
    have hstp : Step P (⟨nd, σ⟩ : Config) ⟨next, σ⟩ := Step.noop hf
    have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
    -- noop: no def, no born, transparent to everything
    have hkills : ∀ a : Asgn, kills P nd a = false := by
      intro a; simp [kills, useV, defV, hf, instrUsedVars, instrDefVar]
    have hsink_transp : ∀ a, a ∈ S.η nd → a ∈ pass P nd := fun a ha =>
      mem_transp.mpr ⟨hbound nd a ha, hkills a⟩
    -- liveness is monotone backward across a noop (no def kills nothing)
    have hlive_mono : ∀ x, x ∈ S.π next → x ∈ S.π nd := by
      intro x hx
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x hx) with h | h
      · exact h
      · simp only [defVars, defV, instrDefVar, hf, Variables.empty] at h
        exact absurd h Std.HashSet.not_mem_empty
    have hsink_next : ∀ a, a ∈ S.η next → a ∈ S.η nd ∧ a ∈ pass P nd := by
      intro a ha
      have := S.isSink.update _ _ hstp a ha
      rcases mem_deferCand.mp this with hb | h
      · rw [show born P nd = (∅ : Assignments) from by unfold born; rw [hf]] at hb
        exact absurd hb Std.HashSet.not_mem_empty
      · exact h
    -- run the matNode chain (vals = σ)
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1
      simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    -- recoverability of the edge candidates against τ1
    have her : ∀ a ∈ matEdge P S nd next, eval τ1 a.rhs = some (σ a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [show born P nd = (∅ : Assignments) from by unfold born; rw [hf]] at hb
        exact absurd hb Std.HashSet.not_mem_empty
      · have hli : a.lhs ∈ S.π nd := hlive_mono a.lhs (live_of_mem_ηK has hls)
        have hr : eval dσ a.rhs = some (σ a.lhs) := hrec a.lhs a.rhs has hli
        rw [eval_congr (fun v hv => ?_)]
        · exact hr
        · refine hoff1 v (fun m hm hmv => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm |>.1)) a (ηK_sub S nd a has) hmne).2
          rw [hmv] at this; rw [this] at hv; exact absurd hv (by simp)
    -- block layout
    have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = (block P S nd)[(matNode P S nd).length]? :=
      transform_fetch hi (by rw [block_length]; unfold blockLen; rw [hf]; omega)
    have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd)
        ++ (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
              else blockOff P S nd + (matNode P S nd).length + 1)
            :: edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
                (blockOff P S next)) := by simp only [block, hf]
    have hctl : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = some (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
              else blockOff P S nd + (matNode P S nd).length + 1)) := by
      rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
          matChain_append_get]; rfl
    -- control + edge to ⟨blockOff next, τ2⟩
    have hedge : ∃ cmid τ2, Step (transform P S)
          ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩ cmid
        ∧ Steps (transform P S) cmid ⟨blockOff P S next, τ2⟩
        ∧ (∀ v, (∀ a ∈ matEdge P S nd next, a.lhs ≠ v) → τ2 v = τ1 v)
        ∧ (∀ a ∈ matEdge P S nd next, τ2 a.lhs = σ a.lhs) := by
      by_cases he : (matEdge P S nd next).isEmpty
      · exact ⟨⟨blockOff P S next, τ1⟩, τ1, Step.noop (by rw [hctl, if_pos he]), Steps.refl,
              fun v _ => rfl, fun a ha => by rw [List.isEmpty_iff.mp he] at ha; simp at ha⟩
      · have hctlstep : Step (transform P S)
            ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
            ⟨blockOff P S nd + (matNode P S nd).length + 1, τ1⟩ := by
          refine Step.noop ?_; rw [hctl, if_neg he]
        have hef : ∀ k (hk : k < (matEdge P S nd next).length),
            (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = some (.assign ((matEdge P S nd next)[k]'hk).lhs ((matEdge P S nd next)[k]'hk).rhs
                (if k + 1 == (matEdge P S nd next).length then blockOff P S next
                 else blockOff P S nd + (matNode P S nd).length + 1 + k + 1)) := by
          intro k hk
          have hjb : (matNode P S nd).length + 1 + k < (block P S nd).length := by
            rw [block_length]; simp only [blockLen, hf]; omega
          have hfetcheq : (transform P S).fetch (blockOff P S nd + ((matNode P S nd).length + 1 + k))
              = (block P S nd)[(matNode P S nd).length + 1 + k]? := transform_fetch hi hjb
          have hL : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = (edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
                  (blockOff P S next))[k]? := by
            rw [show blockOff P S nd + (matNode P S nd).length + 1 + k
                  = blockOff P S nd + ((matNode P S nd).length + 1 + k) from by omega, hfetcheq, hbeq,
                show (matNode P S nd).length + 1 + k = (matNode P S nd).length + (1 + k) from by omega,
                matChain_append_get, show 1 + k = k + 1 from by omega, List.getElem?_cons_succ]
          rw [hL, edgeChain_getElem? hk]
        obtain ⟨τ2, hse, hoffe, hone⟩ := edge_run S hindep τ1 σ
          (blockOff P S nd + (matNode P S nd).length + 1) hef her
        rw [if_neg he] at hse
        exact ⟨_, τ2, hctlstep, hse, hoffe, hone⟩
    obtain ⟨cmid, τ2, hctl_lead, hse, hoffe, hone⟩ := hedge
    obtain ⟨mid, hlead, hmid⟩ := steps_tail_head hs1 hctl_lead
    refine ⟨mid, ⟨blockOff P S next, τ2⟩, hlead, steps_trans hmid hse, rfl, ?_, ?_, ?_⟩
    · -- clause 2: live & not-in-flight agree
      intro x hxlive hxnf
      show τ2 x = σ x
      by_cases hxe : ∃ a ∈ matEdge P S nd next, a.lhs = x
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · have hτ2x : τ2 x = τ1 x := hoffe x (fun a ha hax => hxe ⟨a, ha, hax⟩)
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x
        · obtain ⟨m, hm, rfl⟩ := hxn; rw [hτ2x]; exact hon1 m hm
        · rw [hτ2x, hoff1 x (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x (hlive_mono x hxlive) (fun e' hmem => ?_)
          -- x in flight at nd ⇒ it leaves & is live ⇒ materialized on the edge ⇒ contradiction
          have hat : (⟨x, e'⟩ : Asgn) ∈ pass P nd := hsink_transp _ (ηK_sub S nd _ hmem)
          have hde : (⟨x, e'⟩ : Asgn) ∈ delayedExit P S nd := mem_delayedExit.mpr (Or.inr ⟨hmem, hat⟩)
          have hin : (⟨x, e'⟩ : Asgn) ∈ matEdge P S nd next :=
            mem_matEdge.mpr ⟨hde, hxnf e', Or.inl hxlive⟩
          exact hxe ⟨⟨x, e'⟩, hin, rfl⟩
    · -- clause 3: recoverability at next
      intro x e hmem hxlive
      show eval τ2 e = some (σ x)
      have hupd := hsink_next _ (ηK_sub S next _ hmem)
      have hupdK : (⟨x, e⟩ : Asgn) ∈ S.ηK nd ∧ (⟨x, e⟩ : Asgn) ∈ pass P nd :=
        ⟨mem_ηK.mpr ⟨hupd.1, (mem_ηK.mp hmem).2⟩, hupd.2⟩
      have hli : x ∈ S.π nd := hlive_mono x hxlive
      have hr : eval dσ e = some (σ x) := hrec x e hupdK.1 hli
      rw [eval_congr (fun v hv => ?_)]
      · exact hr
      · -- operand v of e is not materialized
        have hvne_edge : ∀ a ∈ matEdge P S nd next, a.lhs ≠ v := by
          intro a ha hav
          have hane : a ≠ ⟨x, e⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
          have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
            (mem_delayedExit.mpr (Or.inr hupdK)) hane).2
          rw [hav] at this; rw [this] at hv; exact absurd hv (by simp)
        have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ v := by
          intro m hm hmv
          have hmne : m ≠ (⟨x, e⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hupd.2)
          have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) ⟨x, e⟩ hupd.1 hmne).2
          rw [hmv] at this; rw [this] at hv; exact absurd hv (by simp)
        rw [hoffe v hvne_edge, hoff1 v hvne_node]
    · exact Indep_step S (Step.noop hf) hindep
  | assign hf hv =>
    rename_i nd σ x e next v
    subst hnode
    have hi : nd < P.size := fetch_lt hf
    have hnext : next < P.size := wf.succ_lt hf (by simp [Cmd.succs])
    have hstp : Step P (⟨nd, σ⟩ : Config) ⟨next, σ.update x v⟩ := Step.assign hf hv
    have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
    have hdefV : defV P nd = some x := by simp only [defV, hf, instrDefVar]
    have huseV : useV P nd = exprVars e := by simp only [useV, hf, instrUsedVars]
    have hbornx : born P nd = Assignments.singleton ⟨x, e⟩ := by simp only [born, hf]
    -- predict: live next ⊆ live nd ∪ {x}
    have hpred : ∀ x', x' ∈ S.π next → x' ∈ S.π nd ∨ x' = x := by
      intro x' hx'
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x' hx') with h | h
      · exact Or.inl h
      · right; simp only [defVars, hdefV] at h; exact Variables.mem_singleton.mp h
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    -- an operand used at `nd` and live at `nd` is materialized to its source value
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.ηK nd
      · obtain ⟨ew, hew⟩ := hwf
        have hewη : (⟨w, ew⟩ : Asgn) ∈ S.η nd := ηK_sub S nd _ hew
        have hk : kills P nd ⟨w, ew⟩ = true := by
          simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        have hmn : (⟨w, ew⟩ : Asgn) ∈ matNode P S nd :=
          mem_matNode.mpr ⟨hew, by simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hewη, hntr⟩, hwl⟩
        exact hon1 ⟨w, ew⟩ hmn
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.ηK nd := fun e' h => hwf ⟨e', h⟩
        rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
        exact h2 w hwl hnf
    have hgate_live : x ∈ S.π next → ∀ w, w ∈ useV P nd → w ∈ S.π nd := by
      intro hxln w hw
      refine S.isLive.gate _ _ hstp ⟨x, ?_, hxln⟩ w ?_
      · simp only [defVars, hdefV]; exact Variables.mem_singleton.mpr rfl
      · simp only [rhsVars, hf, usedVars]; exact Variables.mem_ofList.mpr hw
    -- edge recoverability against τ1 (vals = σ' = σ.update x v)
    have her : ∀ a ∈ matEdge P S nd next, eval τ1 a.rhs = some ((σ.update x v) a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [hbornx, Assignments.mem_singleton] at hb; subst hb
        -- Operands of the freshly-floated assignment are live at `nd` for one of two reasons: the
        -- classical faint-liveness gate (its result is live downstream), or — when the mode declined to
        -- sink it — the bundle's `keepLive` obligation. This disjunction is exactly the `liveFilterK`
        -- escape, and it is why that escape is sound.
        have hwlive : ∀ w, w ∈ useV P nd → w ∈ S.π nd := by
          intro w hw'
          rcases hls with hl | hkf
          · exact hgate_live hl w hw'
          · refine S.keepLive nd ⟨x, e⟩ ?_ hkf w ?_
            · rw [hbornx]; exact Assignments.mem_singleton.mpr rfl
            · simp only [rhsVars, hf, usedVars]; exact Variables.mem_ofList.mpr hw'
        show eval τ1 e = some ((σ.update x v) x)
        rw [show (σ.update x v) x = v from by rw [Store.update, if_pos rfl]]
        rw [eval_congr (fun w hw => ?_)]
        · exact hv
        · exact hop_fresh w (huseV ▸ readsVar_imp_mem hw) (hwlive _ (huseV ▸ readsVar_imp_mem hw))
      · have hxne : a.lhs ≠ x := fun h => (transp_facts hat).2.1 (by rw [hdefV, h])
        rw [show (σ.update x v) a.lhs = σ a.lhs from by rw [Store.update, if_neg hxne]]
        have hli : a.lhs ∈ S.π nd := (hpred a.lhs (live_of_mem_ηK has hls)).resolve_right hxne
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec a.lhs a.rhs has hli
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) a (ηK_sub S nd a has) hmne).2
          rw [hmw] at this; rw [this] at hw; exact absurd hw (by simp)
    -- block layout (identical shape to the noop block)
    have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = (block P S nd)[(matNode P S nd).length]? :=
      transform_fetch hi (by rw [block_length]; simp only [blockLen, hf]; omega)
    have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd)
        ++ (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
              else blockOff P S nd + (matNode P S nd).length + 1)
            :: edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
                (blockOff P S next)) := by simp only [block, hf]
    have hctl : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = some (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
              else blockOff P S nd + (matNode P S nd).length + 1)) := by
      rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
          matChain_append_get]; rfl
    have hedge : ∃ cmid τ2, Step (transform P S)
          ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩ cmid
        ∧ Steps (transform P S) cmid ⟨blockOff P S next, τ2⟩
        ∧ (∀ w, (∀ a ∈ matEdge P S nd next, a.lhs ≠ w) → τ2 w = τ1 w)
        ∧ (∀ a ∈ matEdge P S nd next, τ2 a.lhs = (σ.update x v) a.lhs) := by
      by_cases he : (matEdge P S nd next).isEmpty
      · exact ⟨⟨blockOff P S next, τ1⟩, τ1, Step.noop (by rw [hctl, if_pos he]), Steps.refl,
              fun w _ => rfl, fun a ha => by rw [List.isEmpty_iff.mp he] at ha; simp at ha⟩
      · have hctlstep : Step (transform P S)
            ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
            ⟨blockOff P S nd + (matNode P S nd).length + 1, τ1⟩ :=
          Step.noop (by rw [hctl, if_neg he])
        have hef : ∀ k (hk : k < (matEdge P S nd next).length),
            (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = some (.assign ((matEdge P S nd next)[k]'hk).lhs ((matEdge P S nd next)[k]'hk).rhs
                (if k + 1 == (matEdge P S nd next).length then blockOff P S next
                 else blockOff P S nd + (matNode P S nd).length + 1 + k + 1)) := by
          intro k hk
          have hjb : (matNode P S nd).length + 1 + k < (block P S nd).length := by
            rw [block_length]; simp only [blockLen, hf]; omega
          have hfetcheq : (transform P S).fetch (blockOff P S nd + ((matNode P S nd).length + 1 + k))
              = (block P S nd)[(matNode P S nd).length + 1 + k]? := transform_fetch hi hjb
          have hL : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = (edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
                  (blockOff P S next))[k]? := by
            rw [show blockOff P S nd + (matNode P S nd).length + 1 + k
                  = blockOff P S nd + ((matNode P S nd).length + 1 + k) from by omega, hfetcheq, hbeq,
                show (matNode P S nd).length + 1 + k = (matNode P S nd).length + (1 + k) from by omega,
                matChain_append_get, show 1 + k = k + 1 from by omega, List.getElem?_cons_succ]
          rw [hL, edgeChain_getElem? hk]
        obtain ⟨τ2, hse, hoffe, hone⟩ := edge_run S hindep τ1 (σ.update x v)
          (blockOff P S nd + (matNode P S nd).length + 1) hef her
        rw [if_neg he] at hse
        exact ⟨_, τ2, hctlstep, hse, hoffe, hone⟩
    obtain ⟨cmid, τ2, hctl_lead, hse, hoffe, hone⟩ := hedge
    obtain ⟨mid, hlead, hmid⟩ := steps_tail_head hs1 hctl_lead
    refine ⟨mid, ⟨blockOff P S next, τ2⟩, hlead, steps_trans hmid hse, rfl, ?_, ?_, ?_⟩
    · -- clause 2
      intro x' hxlive hxnf
      show τ2 x' = (σ.update x v) x'
      by_cases hxe : ∃ a ∈ matEdge P S nd next, a.lhs = x'
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · have hx'x : x' ≠ x := fun h => hxe ⟨⟨x, e⟩,
          mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inl (by rw [hbornx]; exact Assignments.mem_singleton.mpr rfl)),
            h ▸ hxnf e, Or.inl (h ▸ hxlive)⟩, h.symm⟩
        rw [hoffe x' (fun a ha hax => hxe ⟨a, ha, hax⟩),
            show (σ.update x v) x' = σ x' from by rw [Store.update, if_neg hx'x]]
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x'
        · obtain ⟨m, hm, rfl⟩ := hxn; exact hon1 m hm
        · rw [hoff1 x' (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x' ((hpred x' hxlive).resolve_right hx'x) (fun e' hmem => ?_)
          by_cases htr : (⟨x', e'⟩ : Asgn) ∈ pass P nd
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr
              ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', Or.inl hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, (hpred x' hxlive).resolve_right hx'x⟩, rfl⟩
            simp only [blockedSet, hf]
            exact Assignments.mem_sdiff.mpr ⟨hbound nd _ (ηK_sub S nd _ hmem), htr⟩
    · -- clause 3
      intro x' e' hmem hxlive
      show eval τ2 e' = some ((σ.update x v) x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ (ηK_sub S next _ hmem)
      have hkeepx : S.keep (⟨x', e'⟩ : Asgn) = true := (mem_ηK.mp hmem).2
      rcases mem_deferCand.mp hupd with hb | ⟨has, hat⟩
      · rw [hbornx, Assignments.mem_singleton] at hb
        injection hb with hxx hee
        have hmemxe : (⟨x, e⟩ : Asgn) ∈ S.η next := by
          rw [← hxx, ← hee]; exact ηK_sub S next _ hmem
        rw [show (σ.update x v) x' = v from by rw [hxx, Store.update, if_pos rfl], hee]
        rw [eval_congr (fun w hw => ?_)]
        · exact hv
        · have hwu : w ∈ useV P nd := huseV ▸ readsVar_imp_mem hw
          have hwne : ∀ a ∈ matEdge P S nd next, a.lhs ≠ w := by
            intro a ha haw
            rcases mem_delayedExit.mp (mem_matEdge.mp ha).1 with hab | ⟨_, hatr⟩
            · rw [hbornx, Assignments.mem_singleton] at hab
              rw [hab] at ha; exact (mem_matEdge.mp ha).2.1 (mem_ηK.mpr ⟨hmemxe, hxx ▸ hee ▸ hkeepx⟩)
            · exact (transp_facts hatr).1 (haw ▸ hwu)
          rw [hoffe w hwne]; exact hop_fresh w hwu (hgate_live (hxx ▸ hxlive) _ hwu)
      · have hxne : x' ≠ x := fun h => (transp_facts hat).2.1 (by rw [hdefV, h])
        have hasK : (⟨x', e'⟩ : Asgn) ∈ S.ηK nd := mem_ηK.mpr ⟨has, hkeepx⟩
        rw [show (σ.update x v) x' = σ x' from by rw [Store.update, if_neg hxne]]
        have hli : x' ∈ S.π nd := (hpred x' hxlive).resolve_right hxne
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' hasK hli
        · have hvne_edge : ∀ a ∈ matEdge P S nd next, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨hasK, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep
  | ifzT hf hz =>
    rename_i nd σ x z nz
    subst hnode
    have hi : nd < P.size := fetch_lt hf
    have hnz : z < P.size := wf.succ_lt hf (by simp [Cmd.succs])
    have hstp : Step P (⟨nd, σ⟩ : Config) ⟨z, σ⟩ := Step.ifzT hf hz
    have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
    have hdefV : defV P nd = none := by simp only [defV, hf, instrDefVar]
    have huseV : useV P nd = [x] := by simp only [useV, hf, instrUsedVars]
    have hborn0 : born P nd = (∅ : Assignments) := by simp only [born, hf]
    have hlive_mono : ∀ x', x' ∈ S.π z → x' ∈ S.π nd := by
      intro x' hx'
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x' hx') with h | h
      · exact h
      · simp only [defVars, hdefV] at h; exact absurd h Std.HashSet.not_mem_empty
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.ηK nd
      · obtain ⟨ew, hew⟩ := hwf
        have hk : kills P nd ⟨w, ew⟩ = true := by simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        exact hon1 ⟨w, ew⟩ (mem_matNode.mpr ⟨hew,
          by simp only [blockedSet, hf]
             exact Assignments.mem_sdiff.mpr ⟨hbound nd _ (ηK_sub S nd _ hew), hntr⟩, hwl⟩)
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.ηK nd := fun e' h => hwf ⟨e', h⟩
        rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
        exact h2 w hwl hnf
    -- branch sync: target reads the condition variable at the same value
    have hxlive_nd : x ∈ S.π nd := S.isLive.check nd x (by
      simp only [condVars, hf, usedVars]; exact Variables.mem_ofList.mpr (by rw [huseV]; simp))
    have hxsync : τ1 x = 0 := by rw [hop_fresh x (by rw [huseV]; simp) hxlive_nd]; exact hz
    -- edge recoverability (matEdge nd z), vals = σ
    have her : ∀ a ∈ matEdge P S nd z, eval τ1 a.rhs = some (σ a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · rw [eval_congr (fun w hw => ?_)]
        · exact hrec a.lhs a.rhs has (hlive_mono a.lhs (live_of_mem_ηK has hls))
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) a (ηK_sub S nd a has) hmne).2
          rw [hmw] at this; rw [this] at hw; exact absurd hw (by simp)
    -- block layout
    have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = (block P S nd)[(matNode P S nd).length]? :=
      transform_fetch hi (by rw [block_length]; simp only [blockLen, hf]; omega)
    have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd)
        ++ (Cmd.ifz x (if (matEdge P S nd z).isEmpty then blockOff P S z
                else blockOff P S nd + (matNode P S nd).length + 1)
              (if (matEdge P S nd nz).isEmpty then blockOff P S nz
                else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
            :: (edgeChain (matEdge P S nd z) (blockOff P S nd + (matNode P S nd).length + 1) (blockOff P S z)
                ++ edgeChain (matEdge P S nd nz)
                    (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
                    (blockOff P S nz))) := by simp only [block, hf]
    have hctl : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = some (Cmd.ifz x (if (matEdge P S nd z).isEmpty then blockOff P S z
                else blockOff P S nd + (matNode P S nd).length + 1)
              (if (matEdge P S nd nz).isEmpty then blockOff P S nz
                else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)) := by
      rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
          matChain_append_get]; rfl
    have hedge : ∃ cmid τ2, Step (transform P S)
          ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩ cmid
        ∧ Steps (transform P S) cmid ⟨blockOff P S z, τ2⟩
        ∧ (∀ w, (∀ a ∈ matEdge P S nd z, a.lhs ≠ w) → τ2 w = τ1 w)
        ∧ (∀ a ∈ matEdge P S nd z, τ2 a.lhs = σ a.lhs) := by
      by_cases he : (matEdge P S nd z).isEmpty
      · exact ⟨⟨blockOff P S z, τ1⟩, τ1, Step.ifzT (by rw [hctl, if_pos he]) hxsync, Steps.refl,
              fun w _ => rfl, fun a ha => by rw [List.isEmpty_iff.mp he] at ha; simp at ha⟩
      · have hctlstep : Step (transform P S)
            ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
            ⟨blockOff P S nd + (matNode P S nd).length + 1, τ1⟩ :=
          Step.ifzT (by rw [hctl, if_neg he]) hxsync
        have hef : ∀ k (hk : k < (matEdge P S nd z).length),
            (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = some (.assign ((matEdge P S nd z)[k]'hk).lhs ((matEdge P S nd z)[k]'hk).rhs
                (if k + 1 == (matEdge P S nd z).length then blockOff P S z
                 else blockOff P S nd + (matNode P S nd).length + 1 + k + 1)) := by
          intro k hk
          have hjb : (matNode P S nd).length + 1 + k < (block P S nd).length := by
            rw [block_length]
            have hbl : blockLen P S nd = (matNode P S nd).length + 1
                + (matEdge P S nd z).length + (matEdge P S nd nz).length := by
              simp only [blockLen, hf]; rw [← Nat.add_assoc]
            rw [hbl]; omega
          have hfetcheq : (transform P S).fetch (blockOff P S nd + ((matNode P S nd).length + 1 + k))
              = (block P S nd)[(matNode P S nd).length + 1 + k]? := transform_fetch hi hjb
          have hL : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
              = (edgeChain (matEdge P S nd z) (blockOff P S nd + (matNode P S nd).length + 1)
                  (blockOff P S z))[k]? := by
            rw [show blockOff P S nd + (matNode P S nd).length + 1 + k
                  = blockOff P S nd + ((matNode P S nd).length + 1 + k) from by omega, hfetcheq, hbeq,
                show (matNode P S nd).length + 1 + k = (matNode P S nd).length + (1 + k) from by omega,
                matChain_append_get, show 1 + k = k + 1 from by omega, List.getElem?_cons_succ,
                List.getElem?_append_left (by rw [edgeChain_length]; exact hk)]
          rw [hL, edgeChain_getElem? hk]
        obtain ⟨τ2, hse, hoffe, hone⟩ := edge_run S hindep τ1 σ
          (blockOff P S nd + (matNode P S nd).length + 1) hef her
        rw [if_neg he] at hse
        exact ⟨_, τ2, hctlstep, hse, hoffe, hone⟩
    obtain ⟨cmid, τ2, hctl_lead, hse, hoffe, hone⟩ := hedge
    obtain ⟨mid, hlead, hmid⟩ := steps_tail_head hs1 hctl_lead
    refine ⟨mid, ⟨blockOff P S z, τ2⟩, hlead, steps_trans hmid hse, rfl, ?_, ?_, ?_⟩
    · intro x' hxlive hxnf
      show τ2 x' = σ x'
      by_cases hxe : ∃ a ∈ matEdge P S nd z, a.lhs = x'
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · rw [hoffe x' (fun a ha hax => hxe ⟨a, ha, hax⟩)]
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x'
        · obtain ⟨m, hm, rfl⟩ := hxn; exact hon1 m hm
        · rw [hoff1 x' (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x' (hlive_mono x' hxlive) (fun e' hmem => ?_)
          by_cases htr : (⟨x', e'⟩ : Asgn) ∈ pass P nd
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr
              ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', Or.inl hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, hlive_mono x' hxlive⟩, rfl⟩
            simp only [blockedSet, hf]
            exact Assignments.mem_sdiff.mpr ⟨hbound nd _ (ηK_sub S nd _ hmem), htr⟩
    · intro x' e' hmem hxlive
      show eval τ2 e' = some (σ x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ (ηK_sub S _ _ hmem)
      have hkeepx : S.keep (⟨x', e'⟩ : Asgn) = true := (mem_ηK.mp hmem).2
      rcases mem_deferCand.mp hupd with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · have hasK : (⟨x', e'⟩ : Asgn) ∈ S.ηK nd := mem_ηK.mpr ⟨has, hkeepx⟩
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' hasK (hlive_mono x' hxlive)
        · have hvne_edge : ∀ a ∈ matEdge P S nd z, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨hasK, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep
  | ifzF hf hz =>
    rename_i nd σ x z nz
    subst hnode
    have hi : nd < P.size := fetch_lt hf
    have hnnz : nz < P.size := wf.succ_lt hf (by simp [Cmd.succs])
    have hstp : Step P (⟨nd, σ⟩ : Config) ⟨nz, σ⟩ := Step.ifzF hf hz
    have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
    have hdefV : defV P nd = none := by simp only [defV, hf, instrDefVar]
    have huseV : useV P nd = [x] := by simp only [useV, hf, instrUsedVars]
    have hborn0 : born P nd = (∅ : Assignments) := by simp only [born, hf]
    have hlive_mono : ∀ x', x' ∈ S.π nz → x' ∈ S.π nd := by
      intro x' hx'
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x' hx') with h | h
      · exact h
      · simp only [defVars, hdefV] at h; exact absurd h Std.HashSet.not_mem_empty
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.ηK nd
      · obtain ⟨ew, hew⟩ := hwf
        have hk : kills P nd ⟨w, ew⟩ = true := by simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        exact hon1 ⟨w, ew⟩ (mem_matNode.mpr ⟨hew,
          by simp only [blockedSet, hf]
             exact Assignments.mem_sdiff.mpr ⟨hbound nd _ (ηK_sub S nd _ hew), hntr⟩, hwl⟩)
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.ηK nd := fun e' h => hwf ⟨e', h⟩
        rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
        exact h2 w hwl hnf
    have hxlive_nd : x ∈ S.π nd := S.isLive.check nd x (by
      simp only [condVars, hf, usedVars]; exact Variables.mem_ofList.mpr (by rw [huseV]; simp))
    have hxsync : τ1 x ≠ 0 := by rw [hop_fresh x (by rw [huseV]; simp) hxlive_nd]; exact hz
    have her : ∀ a ∈ matEdge P S nd nz, eval τ1 a.rhs = some (σ a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · rw [eval_congr (fun w hw => ?_)]
        · exact hrec a.lhs a.rhs has (hlive_mono a.lhs (live_of_mem_ηK has hls))
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) a (ηK_sub S nd a has) hmne).2
          rw [hmw] at this; rw [this] at hw; exact absurd hw (by simp)
    have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = (block P S nd)[(matNode P S nd).length]? :=
      transform_fetch hi (by rw [block_length]; simp only [blockLen, hf]; omega)
    have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd)
        ++ (Cmd.ifz x (if (matEdge P S nd z).isEmpty then blockOff P S z
                else blockOff P S nd + (matNode P S nd).length + 1)
              (if (matEdge P S nd nz).isEmpty then blockOff P S nz
                else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
            :: (edgeChain (matEdge P S nd z) (blockOff P S nd + (matNode P S nd).length + 1) (blockOff P S z)
                ++ edgeChain (matEdge P S nd nz)
                    (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
                    (blockOff P S nz))) := by simp only [block, hf]
    have hctl : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
        = some (Cmd.ifz x (if (matEdge P S nd z).isEmpty then blockOff P S z
                else blockOff P S nd + (matNode P S nd).length + 1)
              (if (matEdge P S nd nz).isEmpty then blockOff P S nz
                else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)) := by
      rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
          matChain_append_get]; rfl
    have hbl : blockLen P S nd = (matNode P S nd).length + 1
        + (matEdge P S nd z).length + (matEdge P S nd nz).length := by
      simp only [blockLen, hf]; rw [← Nat.add_assoc]
    have hedge : ∃ cmid τ2, Step (transform P S)
          ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩ cmid
        ∧ Steps (transform P S) cmid ⟨blockOff P S nz, τ2⟩
        ∧ (∀ w, (∀ a ∈ matEdge P S nd nz, a.lhs ≠ w) → τ2 w = τ1 w)
        ∧ (∀ a ∈ matEdge P S nd nz, τ2 a.lhs = σ a.lhs) := by
      by_cases he : (matEdge P S nd nz).isEmpty
      · exact ⟨⟨blockOff P S nz, τ1⟩, τ1, Step.ifzF (by rw [hctl, if_pos he]) hxsync, Steps.refl,
              fun w _ => rfl, fun a ha => by rw [List.isEmpty_iff.mp he] at ha; simp at ha⟩
      · have hctlstep : Step (transform P S)
            ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
            ⟨blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length, τ1⟩ :=
          Step.ifzF (by rw [hctl, if_neg he]) hxsync
        have hef : ∀ k (hk : k < (matEdge P S nd nz).length),
            (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length + k)
              = some (.assign ((matEdge P S nd nz)[k]'hk).lhs ((matEdge P S nd nz)[k]'hk).rhs
                (if k + 1 == (matEdge P S nd nz).length then blockOff P S nz
                 else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length + k + 1)) := by
          intro k hk
          have hjb : (matNode P S nd).length + 1 + (matEdge P S nd z).length + k < (block P S nd).length := by
            rw [block_length, hbl]; omega
          have hfetcheq : (transform P S).fetch
              (blockOff P S nd + ((matNode P S nd).length + 1 + (matEdge P S nd z).length + k))
              = (block P S nd)[(matNode P S nd).length + 1 + (matEdge P S nd z).length + k]? :=
            transform_fetch hi hjb
          have hL : (transform P S).fetch
              (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length + k)
              = (edgeChain (matEdge P S nd nz)
                  (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
                  (blockOff P S nz))[k]? := by
            rw [show blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length + k
                  = blockOff P S nd + ((matNode P S nd).length + 1 + (matEdge P S nd z).length + k) from by omega,
                hfetcheq, hbeq,
                show (matNode P S nd).length + 1 + (matEdge P S nd z).length + k
                  = (matNode P S nd).length + (1 + (matEdge P S nd z).length + k) from by omega,
                matChain_append_get,
                show 1 + (matEdge P S nd z).length + k = ((matEdge P S nd z).length + k) + 1 from by omega,
                List.getElem?_cons_succ,
                List.getElem?_append_right (by rw [edgeChain_length]; omega)]
            rw [edgeChain_length]; congr 1; omega
          rw [hL, edgeChain_getElem? hk]
        obtain ⟨τ2, hse, hoffe, hone⟩ := edge_run S hindep τ1 σ
          (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length) hef her
        rw [if_neg he] at hse
        exact ⟨_, τ2, hctlstep, hse, hoffe, hone⟩
    obtain ⟨cmid, τ2, hctl_lead, hse, hoffe, hone⟩ := hedge
    obtain ⟨mid, hlead, hmid⟩ := steps_tail_head hs1 hctl_lead
    refine ⟨mid, ⟨blockOff P S nz, τ2⟩, hlead, steps_trans hmid hse, rfl, ?_, ?_, ?_⟩
    · intro x' hxlive hxnf
      show τ2 x' = σ x'
      by_cases hxe : ∃ a ∈ matEdge P S nd nz, a.lhs = x'
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · rw [hoffe x' (fun a ha hax => hxe ⟨a, ha, hax⟩)]
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x'
        · obtain ⟨m, hm, rfl⟩ := hxn; exact hon1 m hm
        · rw [hoff1 x' (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x' (hlive_mono x' hxlive) (fun e' hmem => ?_)
          by_cases htr : (⟨x', e'⟩ : Asgn) ∈ pass P nd
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr
              ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', Or.inl hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, hlive_mono x' hxlive⟩, rfl⟩
            simp only [blockedSet, hf]
            exact Assignments.mem_sdiff.mpr ⟨hbound nd _ (ηK_sub S nd _ hmem), htr⟩
    · intro x' e' hmem hxlive
      show eval τ2 e' = some (σ x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ (ηK_sub S _ _ hmem)
      have hkeepx : S.keep (⟨x', e'⟩ : Asgn) = true := (mem_ηK.mp hmem).2
      rcases mem_deferCand.mp hupd with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · have hasK : (⟨x', e'⟩ : Asgn) ∈ S.ηK nd := mem_ηK.mpr ⟨has, hkeepx⟩
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' hasK (hlive_mono x' hxlive)
        · have hvne_edge : ∀ a ∈ matEdge P S nd nz, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨hasK, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (ηK_sub S nd m (mem_matNode.mp hm).1) ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep

/-! ## Step 7 — boundary -/

/-- At the entry, `S.η P.entry ⊆ ∅` (the seed), so `Match` is full store equality. -/
theorem match_init {P : Program} (S : PdceSpec P) (σ : Store) :
    Match P S ⟨P.entry, σ⟩ ⟨blockOff P S P.entry, σ⟩ := by
  have hempty : ∀ a : Asgn, a ∉ S.η P.entry := fun a hmem =>
    absurd (S.isSink.seed _ hmem) (by simp [sinkSeed, Assignments.empty])
  refine ⟨rfl, fun x _ _ => rfl, fun x e hmem _ => ?_, ?_⟩
  · exact absurd (ηK_sub S _ _ hmem) (hempty _)
  · exact fun a ha => absurd ha (hempty _)

/-- At `halt`, `blocked` is everything, so the exit frontier materializes every in-flight observable
    (`isLive.seed`: `liveSeed ⊆ live halt`); `Match` then forces agreement on `obs`. -/
theorem match_final_obs {P : Program} (S : PdceSpec P) (_wf : WellFormed P)
    {c d : Config} (hm : Match P S c d) (hfin : Final P c) :
    ∃ d', Steps (transform P S) d d' ∧ Final (transform P S) d' ∧
          ∀ v ∈ P.obs, d'.store v = c.store v := by
  obtain ⟨hnode, h2, hrec, hindep⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  obtain ⟨nd, σ⟩ := c
  -- `Final` ⇒ the node holds `halt`
  have hfin' : P.fetch nd = some .halt := hfin
  subst hnode
  have hi : nd < P.size := fetch_lt hfin'
  have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
  -- at `halt`, everything is blocked
  have hblk : blockedSet P nd = allAsgns P := by simp only [blockedSet, hfin']
  have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
    intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
  obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
  -- the `halt` instruction sits right after the matNode chain
  have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
      = (block P S nd)[(matNode P S nd).length]? :=
    transform_fetch hi (by rw [block_length]; simp only [blockLen, hfin']; omega)
  have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd) ++ [Cmd.halt] := by
    simp only [block, hfin']
  have hhalt : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length) = some Cmd.halt := by
    rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
        matChain_append_get]; rfl
  refine ⟨⟨blockOff P S nd + (matNode P S nd).length, τ1⟩, hs1, hhalt, ?_⟩
  intro v hv
  show τ1 v = σ v
  -- observables are live at the halt
  have hvlive : v ∈ S.π nd := S.isLive.seed ⟨nd, σ⟩ hfin' v (Variables.mem_ofList.mpr hv)
  by_cases hvn : ∃ m ∈ matNode P S nd, m.lhs = v
  · obtain ⟨m, hm, rfl⟩ := hvn; exact hon1 m hm
  · rw [hoff1 v (fun m hm hmx => hvn ⟨m, hm, hmx⟩)]
    refine h2 v hvlive (fun e' hmem => ?_)
    -- v in flight at halt ⇒ blocked (everything is) & live ⇒ materialized ⇒ contradiction
    exact hvn ⟨⟨v, e'⟩, mem_matNode.mpr ⟨hmem, hblk ▸ hbound nd _ (ηK_sub S nd _ hmem), hvlive⟩, rfl⟩

/-! ## Step 6 — multi-step lift -/

/-- `Match` is preserved across a whole source run. -/
theorem match_steps {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    {c c_f d : Config} (hm : Match P S c d) (hrun : Steps P c c_f) :
    ∃ d_f, Steps (transform P S) d d_f ∧ Match P S c_f d_f := by
  induction hrun with
  | refl => exact ⟨d, Steps.refl, hm⟩
  | tail _ hstep ih =>
      obtain ⟨d_mid, hsd, hmm⟩ := ih
      obtain ⟨mid, d_f, hlead, hrest, hmf⟩ := match_step S wf hmm hstep
      exact ⟨d_f, steps_trans hsd (steps_trans (Steps.tail Steps.refl hlead) hrest), hmf⟩

/-! ## Step 8 — top-level correctness -/

/-- **PDCE preserves observable behavior on halting runs.** If `P` started at its entry on store `σ`
    runs to a `halt` config `c_f`, then `transform P S` started at *its* entry on the same `σ` also
    reaches a `halt`, with every observable variable holding the same value. (Faults/divergence are
    don't-care; a halting run is automatically non-faulting.) -/
theorem transform_preserves_halt {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (transform P S) ⟨(transform P S).entry, σ⟩ d_f ∧ Final (transform P S) d_f ∧
           ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  rw [transform_entry]
  obtain ⟨d1, hsteps1, hm1⟩ := match_steps S wf (match_init S σ) hrun
  obtain ⟨d_f, hsteps2, hfin2, hobs⟩ := match_final_obs S wf hm1 hfin
  exact ⟨d_f, steps_trans hsteps1 hsteps2, hfin2, hobs⟩

end BaseLanguage.Analyses.PDCE
