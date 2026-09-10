-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Layout

/-!
# `LCM.Correctness` — behavior-preservation of the hoisting `transform`

Forward simulation of `transform P S` against `P` on **halting runs** (`transform_preserves_halt`, in
`Correctness/MatchStep.lean`); the diagonal **`Fault → Fault`** cell is also proved
(`transform_preserves_faulting`, in `Correctness/FaultPreservation.lean` — forward fault preservation:
divergence stays don't-care, and LCM *can* turn divergence into a fault, §5).
The **dual** of `PDCE.Correctness`: PDCE's target *lags* by a deferred set; LCM's target *leads* by a set
`μ` of **materialized-ahead temps**. The `μ` set is carried *operationally*
in the `Match` relation — it is pure store-bookkeeping (`Holds`), not a ghost.

The proof is split across `Correctness/{ChainExec, Match, Coverage, MatchStep, FaultPreservation}.lean`,
re-exported by the `Correctness.lean` shim. **This file (`ChainExec`)** holds the **simulation
infrastructure** — the reusable operational core: straight-line execution of an `insChain`
(`steps_insSeg`), `Assignments.toList` membership/no-dup bridges, and the temp-map facts.
`Match`/`match_init`/`match_step` build on top in the later sub-files.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std


-- `steps_trans`, `evalAtom_update_not_read`, `eval_update_not_read` are shared reference-semantics
-- lemmas in `IR.TAC` (`namespace Semantics`); available here via `open Semantics`.

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

/-! ## Straight-line execution of an insert chain

The reusable operational core: a list `m` of expressions, laid out as `tempFor e := e` at consecutive
slots `s0, s0+1, …` with slot `k` transferring to `s0+k+1`, runs straight-line from `⟨s0, τ⟩` to
`⟨s0 + m.length, τ'⟩`. Under recoverability (each `e` evaluates in `τ` to its intended value) and
freshness (no `e` reads any temp `tempFor e'`; distinct `e` get distinct temps), the run never faults,
`τ'` sets each `tempFor e` to its intended value and leaves all other variables at `τ`. -/

theorem insChain_length {P : Program} {m : List Expr} {s0 : Nat} :
    (insChain P m s0).length = m.length := by
  unfold insChain; rw [List.length_map, List.length_zipIdx]

/-- The `k`-th instruction of an `insChain` (slot `k` jumps to `s0+k+1`). -/
theorem insChain_getElem? {P : Program} {m : List Expr} {s0 k : Nat} (hk : k < m.length) :
    (insChain P m s0)[k]? = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk) (s0 + k + 1)) := by
  unfold insChain
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk]
  simp

theorem steps_insSeg {Q : Program} {P : Program} :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → tempFor P e ≠ tempFor P e') →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk) (s0 + k + 1))) →
    (∀ e ∈ m, eval τ e ≠ none) →
    (∀ e ∈ m, ∀ e' ∈ m, exprReadsVar e (tempFor P e') = false) →
    ∃ τ', Steps Q ⟨s0, τ⟩ ⟨s0 + m.length, τ'⟩
        ∧ (∀ v, (∀ e ∈ m, tempFor P e ≠ v) → τ' v = τ v)
        ∧ (∀ e ∈ m, some (τ' (tempFor P e)) = eval τ e) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _ _
      exact ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hrec hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨va, hva⟩ : ∃ v, eval τ a = some v := Option.ne_none_iff_exists'.mp (hrec a ha_mem)
      have hfetch0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a (s0 + 0 + 1)) := by
        have := hfetch 0 (by simp); simpa using this
      have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
        have := Step.assign (by simpa using hfetch0) (by simpa using hva); simpa using this
      -- assemble IH hypotheses for `rest` at base `s0+1`
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
      obtain ⟨τ', hsteps, hoff, hon⟩ :=
        ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hrec' hfresh'
      refine ⟨τ', ?_, ?_, ?_⟩
      · have hlen : (s0 + 1) + rest.length = s0 + (a :: rest).length := by simp; omega
        rw [hlen] at hsteps
        exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
      · intro v hv
        have hav : tempFor P a ≠ v := hv a ha_mem
        have heq : τ' v = (τ.update (tempFor P a) va) v :=
          hoff v (fun b hb => hv b (List.mem_cons_of_mem _ hb))
        rw [heq, Store.update, if_neg (fun h => hav h.symm)]
      · intro x hx
        rcases List.mem_cons.mp hx with heq | hx
        · -- x = a: its temp is untouched by `rest` (distinct temps)
          subst heq
          have hno : ∀ b ∈ rest, tempFor P b ≠ tempFor P x :=
            fun b hb => hdist b (List.mem_cons_of_mem _ hb) x ha_mem (fun h => hnotin (h ▸ hb))
          have heq2 : τ' (tempFor P x) = (τ.update (tempFor P x) va) (tempFor P x) :=
            hoff (tempFor P x) hno
          rw [heq2, Store.update, if_pos rfl, hva]
        · rw [hon x hx, hkeep x hx]

/-! ## The exit-chain executor (`steps_exitSeg`)

`exitChain` differs from `insChain` in exactly one place: its **last** instruction jumps to `target`
(= `blockOff next`) rather than to the next slot. So a non-empty exit chain run lands on `target`. This is
the LCM analogue of PDCE's `steps_edgeSeg`; the store reasoning is identical to `steps_insSeg`. -/

theorem exitChain_length {P : Program} {m : List Expr} {start target : Nat} :
    (exitChain P m start target).length = m.length := by
  unfold exitChain; rw [List.length_map, List.length_zipIdx]

/-- The `k`-th instruction of an `exitChain` (slot `k` jumps to `target` if last, else `start+k+1`). -/
theorem exitChain_getElem? {P : Program} {m : List Expr} {start target k : Nat} (hk : k < m.length) :
    (exitChain P m start target)[k]? = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk)
      (if k + 1 == m.length then target else start + k + 1)) := by
  unfold exitChain
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hk]
  simp

/-- Exit-chain variant of `steps_insSeg`: the final assignment jumps to `target` rather than to the next
    slot, so a non-empty chain run lands on `target` (an empty one stays at `s0`). -/
theorem steps_exitSeg {Q : Program} {P : Program} (target : Nat) :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → tempFor P e ≠ tempFor P e') →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk)
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ e ∈ m, eval τ e ≠ none) →
    (∀ e ∈ m, ∀ e' ∈ m, exprReadsVar e (tempFor P e') = false) →
    ∃ τ', Steps Q ⟨s0, τ⟩ ⟨(if m.isEmpty then s0 else target), τ'⟩
        ∧ (∀ v, (∀ e ∈ m, tempFor P e ≠ v) → τ' v = τ v)
        ∧ (∀ e ∈ m, some (τ' (tempFor P e)) = eval τ e) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _ _
      exact ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hrec hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      obtain ⟨va, hva⟩ : ∃ v, eval τ a = some v := Option.ne_none_iff_exists'.mp (hrec a ha_mem)
      by_cases hre : rest = []
      · -- singleton: the lone assignment jumps straight to `target`
        subst hre
        have hf0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a target) := by
          have := hfetch 0 (by simp); simpa using this
        have hstep0 : Step Q ⟨s0, τ⟩ ⟨target, τ.update (tempFor P a) va⟩ := by
          have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
        refine ⟨τ.update (tempFor P a) va, ?_, ?_, ?_⟩
        · simpa using Steps.tail Steps.refl hstep0
        · intro v hv
          rw [Store.update, if_neg (fun h => (hv a ha_mem) h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · subst heq; rw [Store.update, if_pos rfl, hva]
          · simp at hx
      · -- non-empty tail: head jumps to `s0+1`, then recurse
        have hlen2 : 1 < (a :: rest).length := by
          cases rest with | nil => exact absurd rfl hre | cons _ _ => simp
        have hf0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a (s0 + 0 + 1)) := by
          have := hfetch 0 (by simp)
          rw [if_neg (by simp; omega)] at this; simpa using this
        have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
          have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
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
        obtain ⟨τ', hsteps, hoff, hon⟩ :=
          ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hrec' hfresh'
        rw [if_neg (by simpa using hre)] at hsteps
        refine ⟨τ', ?_, ?_, ?_⟩
        · rw [show (a :: rest).isEmpty = false from by simp, if_neg (by simp)]
          exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
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

/-! ## Fault-aware chain runners (for fault preservation)

The no-fault runners `steps_insSeg`/`steps_exitSeg` assume every inserted rhs evaluates. On a *faulting*
run that assumption is exactly what breaks — and when it does the target faults, which is what
fault-preservation needs. These variants drop the no-fault hypothesis and branch on `eval`: the chain
either reaches a `Faulting` config (the first insert whose rhs is `none`) or completes exactly as the
clean runner does. -/

theorem steps_insSeg_fault {Q : Program} (P : Program) :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → tempFor P e ≠ tempFor P e') →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk) (s0 + k + 1))) →
    (∀ e ∈ m, ∀ e' ∈ m, exprReadsVar e (tempFor P e') = false) →
    (∃ cf, Steps Q ⟨s0, τ⟩ cf ∧ Faulting Q cf)
    ∨ (∃ τ', Steps Q ⟨s0, τ⟩ ⟨s0 + m.length, τ'⟩
        ∧ (∀ v, (∀ e ∈ m, tempFor P e ≠ v) → τ' v = τ v)
        ∧ (∀ e ∈ m, some (τ' (tempFor P e)) = eval τ e)) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _
      exact Or.inr ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hf0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a (s0 + 0 + 1)) := by
        have := hfetch 0 (by simp); simpa using this
      cases hva : eval τ a with
      | none =>
          -- the head insert faults ⇒ `Faulting` right at `⟨s0, τ⟩`
          exact Or.inl ⟨⟨s0, τ⟩, Steps.refl, tempFor P a, a, s0 + 0 + 1, by simpa using hf0, hva⟩
      | some va =>
          have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
            have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
          have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → tempFor P x ≠ tempFor P y :=
            fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
          have hfetch' : ∀ k (hk : k < rest.length),
              Q.fetch ((s0 + 1) + k) = some (.assign (tempFor P (rest[k]'hk)) (rest[k]'hk) ((s0 + 1) + k + 1)) := by
            intro k hk
            have hk' : k + 1 < (a :: rest).length := by simp; omega
            have := hfetch (k + 1) hk'
            have hidx : (a :: rest)[k+1]'hk' = rest[k]'hk := by simp
            rw [hidx] at this
            rw [show s0 + 1 + k = s0 + (k + 1) from by omega]; exact this
          have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, exprReadsVar x (tempFor P y) = false :=
            fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
          have hkeep : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b = eval τ b := fun b hb =>
            eval_update_not_read (hfresh b (List.mem_cons_of_mem _ hb) a ha_mem)
          rcases ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hfresh' with
            hfault | hclean
          · obtain ⟨cf, hsteps, hflt⟩ := hfault
            exact Or.inl ⟨cf, steps_trans (Steps.tail Steps.refl hstep0) hsteps, hflt⟩
          · obtain ⟨τ', hsteps, hoff, hon⟩ := hclean
            refine Or.inr ⟨τ', ?_, ?_, ?_⟩
            · have hlen : (s0 + 1) + rest.length = s0 + (a :: rest).length := by simp; omega
              rw [hlen] at hsteps
              exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
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

theorem steps_exitSeg_fault {Q : Program} (P : Program) (target : Nat) :
    ∀ (m : List Expr) (s0 : Nat) (τ : Store),
    m.Nodup →
    (∀ e ∈ m, ∀ e' ∈ m, e ≠ e' → tempFor P e ≠ tempFor P e') →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (tempFor P (m[k]'hk)) (m[k]'hk)
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ e ∈ m, ∀ e' ∈ m, exprReadsVar e (tempFor P e') = false) →
    (∃ cf, Steps Q ⟨s0, τ⟩ cf ∧ Faulting Q cf)
    ∨ (∃ τ', Steps Q ⟨s0, τ⟩ ⟨(if m.isEmpty then s0 else target), τ'⟩
        ∧ (∀ v, (∀ e ∈ m, tempFor P e ≠ v) → τ' v = τ v)
        ∧ (∀ e ∈ m, some (τ' (tempFor P e)) = eval τ e)) := by
  intro m
  induction m with
  | nil =>
      intro s0 τ _ _ _ _
      exact Or.inr ⟨τ, by simpa using Steps.refl, fun v _ => rfl, fun a h => by simp at h⟩
  | cons a rest ih =>
      intro s0 τ hnodup hdist hfetch hfresh
      have ha_mem : a ∈ a :: rest := List.mem_cons_self ..
      have hnotin : a ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      by_cases hre : rest = []
      · subst hre
        have hf0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a target) := by
          have := hfetch 0 (by simp); simpa using this
        cases hva : eval τ a with
        | none =>
            exact Or.inl ⟨⟨s0, τ⟩, Steps.refl, tempFor P a, a, target, by simpa using hf0, hva⟩
        | some va =>
            have hstep0 : Step Q ⟨s0, τ⟩ ⟨target, τ.update (tempFor P a) va⟩ := by
              have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
            refine Or.inr ⟨τ.update (tempFor P a) va, ?_, ?_, ?_⟩
            · simpa using Steps.tail Steps.refl hstep0
            · intro v hv; rw [Store.update, if_neg (fun h => (hv a ha_mem) h.symm)]
            · intro x hx
              rcases List.mem_cons.mp hx with heq | hx
              · subst heq; rw [Store.update, if_pos rfl, hva]
              · simp at hx
      · have hlen2 : 1 < (a :: rest).length := by
          cases rest with | nil => exact absurd rfl hre | cons _ _ => simp
        have hf0 : Q.fetch (s0 + 0) = some (.assign (tempFor P a) a (s0 + 0 + 1)) := by
          have := hfetch 0 (by simp)
          rw [if_neg (by simp; omega)] at this; simpa using this
        cases hva : eval τ a with
        | none =>
            exact Or.inl ⟨⟨s0, τ⟩, Steps.refl, tempFor P a, a, s0 + 0 + 1, by simpa using hf0, hva⟩
        | some va =>
            have hstep0 : Step Q ⟨s0, τ⟩ ⟨s0 + 1, τ.update (tempFor P a) va⟩ := by
              have := Step.assign (by simpa using hf0) (by simpa using hva); simpa using this
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
            have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, exprReadsVar x (tempFor P y) = false :=
              fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
            have hkeep : ∀ b ∈ rest, eval (τ.update (tempFor P a) va) b = eval τ b := fun b hb =>
              eval_update_not_read (hfresh b (List.mem_cons_of_mem _ hb) a ha_mem)
            rcases ih (s0 + 1) (τ.update (tempFor P a) va) hrest_nodup hdist' hfetch' hfresh' with
              hfault | hclean
            · obtain ⟨cf, hsteps, hflt⟩ := hfault
              exact Or.inl ⟨cf, steps_trans (Steps.tail Steps.refl hstep0) hsteps, hflt⟩
            · obtain ⟨τ', hsteps, hoff, hon⟩ := hclean
              rw [if_neg (by simpa using hre)] at hsteps
              refine Or.inr ⟨τ', ?_, ?_, ?_⟩
              · rw [show (a :: rest).isEmpty = false from by simp, if_neg (by simp)]
                exact steps_trans (Steps.tail Steps.refl hstep0) hsteps
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

/-! ## Bridging `Assignments.toList` to set membership

The insert chain is `(insertBefore P S i).toList` of a `Assignments` set; this exposes membership and no-dup. -/

theorem Assignments.mem_toList {F : Assignments} {e : Expr} : e ∈ F.toList ↔ e ∈ F :=
  Std.HashSet.mem_toList

theorem Assignments.nodup_toList {F : Assignments} : F.toList.Nodup :=
  Std.HashSet.distinct_toList.imp (fun {a b} h hab => by subst hab; simp at h)

theorem mem_insertBefore {P : Program} {S : LcmSpec P} {i : Node} {e : Expr} :
    e ∈ (insertBefore P S i).toList ↔
      (e ∈ latestNode P S.ηₚ S.τₚ i ∧ e ∉ latestOut P S i) ∧ e ∈ S.τᵤK i := by
  rw [Assignments.mem_toList]; unfold insertBefore; rw [Assignments.mem_inter, Assignments.mem_sdiff]

/-- `insertBefore ⊆ latestNode` (the entry frontier is `latestNode` minus the exit carry). -/
theorem insertBefore_sub_latestNode {P : Program} {S : LcmSpec P} {i : Node} {e : Expr}
    (he : e ∈ (insertBefore P S i).toList) : e ∈ latestNode P S.ηₚ S.τₚ i :=
  (mem_insertBefore.mp he).1.1

theorem mem_recoverable {P : Program} {S : LcmSpec P} {i : Node} {e : Expr} :
    e ∈ recoverable P S i ↔ e ∈ gateSet P S i ∨ e ∈ insertBefore P S i := by
  unfold recoverable; rw [Assignments.mem_union]

/-- **The replace gate only ever fires on a hoistable expression.** Both halves of `recoverable` are
    filtered by `keep` — under **either** `GateMode`, since `gateSet` is `πᵤK` or `ηₘK` and both carry the
    filter. That is exactly what keeps insertion and replacement consistent: an expression the mode
    declines to hoist is also never rewritten to read a temp. -/
theorem recoverable_keep {P : Program} {S : LcmSpec P} {i : Node} {e : Expr}
    (h : e ∈ recoverable P S i) : S.keep e = true := by
  rcases mem_recoverable.mp h with hu | hib
  · unfold gateSet at hu
    cases hg : S.gate with
    | demand       => rw [hg] at hu; exact (mem_πᵤK.mp hu).2
    | materialized => rw [hg] at hu; exact (mem_ηₘK.mp hu).2
  · exact (mem_τᵤK.mp (mem_insertBefore.mp (Assignments.mem_toList.2 hib)).2).2

/-! ## The block-level insert executor

Runs node `i`'s `insChain` straight-line from the block head to the control slot, materializing every
inserted temp to its intended value (the abstract `vals`), via `steps_insSeg` + the offset layout. -/

/-- Indexing into the `insChain` prefix of a block. -/
theorem block_getElem?_insChain {P : Program} {S : LcmSpec P} {i : Node} {k : Nat}
    (hk : k < (insChain P (insertBefore P S i).toList (blockOff P S i)).length) :
    (block P S i)[k]? = (insChain P (insertBefore P S i).toList (blockOff P S i))[k]? := by
  simp only [block]; rw [List.getElem?_append_left hk]

/-- The `insChain` materialization of node `i` runs from the block head to the control slot
    `blockOff i + |insertBefore i|`, making each `tempFor e` **hold** `e`'s value (in `τ`) and leaving the
    rest of the store untouched. -/
theorem insBlock_exec {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size)
    {τ : Store}
    (hdist : ∀ e ∈ (insertBefore P S i).toList, ∀ e' ∈ (insertBefore P S i).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e')
    (hrec : ∀ e ∈ (insertBefore P S i).toList, eval τ e ≠ none)
    (hfresh : ∀ e ∈ (insertBefore P S i).toList, ∀ e' ∈ (insertBefore P S i).toList,
      exprReadsVar e (tempFor P e') = false) :
    ∃ τ1, Steps (transform P S) ⟨blockOff P S i, τ⟩
            ⟨blockOff P S i + (insertBefore P S i).toList.length, τ1⟩
        ∧ (∀ v, (∀ e ∈ (insertBefore P S i).toList, tempFor P e ≠ v) → τ1 v = τ v)
        ∧ (∀ e ∈ (insertBefore P S i).toList, some (τ1 (tempFor P e)) = eval τ e) := by
  refine steps_insSeg (insertBefore P S i).toList (blockOff P S i) τ
    Assignments.nodup_toList hdist ?_ hrec hfresh
  intro k hk
  have hkb : k < (block P S i).length := by
    rw [block_length]; unfold blockLen; omega
  have hml : k < (insChain P (insertBefore P S i).toList (blockOff P S i)).length := by
    rw [insChain_length]; exact hk
  rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]

/-! ## The block-level exit executor

Runs node `i`'s `exitChain` straight-line from the slot just after the (floated) control to `blockOff next`,
materializing every exit-inserted temp with the **post-control** store. The analogue of `insBlock_exec`
for the trailing edge chain (`assign`/`noop` only). -/

/-- Indexing into the `exitChain` suffix of a block (after the `insChain` prefix and the control slot). -/
theorem getElem?_block_exit {P : Program} {S : LcmSpec P} {i : Node} {k : Nat} {next : Node}
    (hfi : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next)) :
    (block P S i)[(insertBefore P S i).toList.length + 1 + k]?
      = (exitChain P (insertAfter P S i).toList
          (blockOff P S i + (insertBefore P S i).toList.length + 1) (blockOff P S next))[k]? := by
  have happ : (insChain P (insertBefore P S i).toList (blockOff P S i)).length
      ≤ (insertBefore P S i).toList.length + 1 + k := by rw [insChain_length]; omega
  rcases hfi with h | ⟨x, e, h⟩ <;>
  · simp only [block, h]
    rw [List.getElem?_append_right happ, insChain_length,
        show (insertBefore P S i).toList.length + 1 + k - (insertBefore P S i).toList.length = k + 1 from by omega,
        List.getElem?_cons_succ]

/-- The `exitChain` materialization of node `i` (`assign`/`noop`) runs from the post-control slot
    `blockOff i + |insertBefore i| + 1` to `blockOff next`, making each exit temp **hold** `e`'s value (in the
    post-control store `τ`) and leaving the rest untouched. Empty exit chain ⇒ control already jumped to
    `blockOff next` (the `isEmpty` branch). -/
theorem exitBlock_exec {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size) {next : Node}
    (hfi : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next))
    {τ : Store}
    (hdist : ∀ e ∈ (insertAfter P S i).toList, ∀ e' ∈ (insertAfter P S i).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e')
    (hrec : ∀ e ∈ (insertAfter P S i).toList, eval τ e ≠ none)
    (hfresh : ∀ e ∈ (insertAfter P S i).toList, ∀ e' ∈ (insertAfter P S i).toList,
      exprReadsVar e (tempFor P e') = false) :
    ∃ τ2, Steps (transform P S)
            ⟨blockOff P S i + (insertBefore P S i).toList.length + 1, τ⟩
            ⟨(if (insertAfter P S i).toList.isEmpty
                then blockOff P S i + (insertBefore P S i).toList.length + 1
                else blockOff P S next), τ2⟩
        ∧ (∀ v, (∀ e ∈ (insertAfter P S i).toList, tempFor P e ≠ v) → τ2 v = τ v)
        ∧ (∀ e ∈ (insertAfter P S i).toList, some (τ2 (tempFor P e)) = eval τ e) := by
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
  exact steps_exitSeg (blockOff P S next) (insertAfter P S i).toList
    (blockOff P S i + (insertBefore P S i).toList.length + 1) τ
    Assignments.nodup_toList hdist hfetch hrec hfresh

/-! ## `allExprs` members are fetched-assign RHSs — the freshness discharge

Every inserted expression `e ∈ insertBefore ⊆ allExprs` is the numbered RHS of some assign of `P`, whose
operands are pre-existing vars; `tempFor` temps are structurally fresh, so `e` never reads any
`tempFor e'`. This discharges the `exprReadsVar e (tempFor e') = false` side-condition of
`steps_insSeg`/`insBlock_exec`. -/

theorem Assignments.mem_singleton {a b : Expr} : a ∈ Assignments.singleton b ↔ a = b := by
  unfold Assignments.singleton
  rw [Std.HashSet.mem_insert]
  constructor
  · rintro (h | h)
    · exact (eq_of_beq h).symm
    · exact absurd h Std.HashSet.not_mem_empty
  · rintro rfl; exact Or.inl (beq_self_eq_true _)

/-- `e ∈ ue P n` ⇒ node `n` is the numbered assign computing `e`. -/
theorem mem_ue {P : Program} {n : Node} {e : Expr} (h : e ∈ ue P n) :
    ∃ x next, P.fetch n = some (.assign x e next) ∧ isNumbered e = true := by
  unfold ue at h
  split at h
  · next x e' next heq =>
      by_cases hn : isNumbered e' = true
      · rw [if_pos hn] at h
        rw [Assignments.mem_singleton] at h; subst h
        exact ⟨x, next, heq, hn⟩
      · rw [if_neg hn] at h; exact absurd h Std.HashSet.not_mem_empty
  · exact absurd h Std.HashSet.not_mem_empty

/-- Membership in `allExprs = ⋃ₙ ue(n)`: `e` is contributed by some node's `ue`. -/
theorem mem_allExprs_range {P : Program} {e : Expr} :
    e ∈ allExprs P ↔ ∃ n ∈ List.range P.size, e ∈ ue P n := by
  unfold allExprs
  have gen : ∀ (l : List Node) (init : Assignments),
      (e ∈ l.foldl (fun acc n => acc.union (ue P n)) init) ↔ e ∈ init ∨ ∃ n ∈ l, e ∈ ue P n := by
    intro l
    induction l with
    | nil => intro init; simp
    | cons c cs ih =>
        intro init
        rw [List.foldl_cons, ih, Assignments.mem_union]
        constructor
        · rintro ((hi | hc) | ⟨m, hm, he⟩)
          · exact Or.inl hi
          · exact Or.inr ⟨c, List.mem_cons_self .., hc⟩
          · exact Or.inr ⟨m, List.mem_cons_of_mem _ hm, he⟩
        · rintro (hi | ⟨m, hm, he⟩)
          · exact Or.inl (Or.inl hi)
          · rcases List.mem_cons.mp hm with rfl | hm
            · exact Or.inl (Or.inr he)
            · exact Or.inr ⟨m, hm, he⟩
  rw [gen (List.range P.size) ∅]
  simp only [Std.HashSet.not_mem_empty, false_or]

/-- A member of `allExprs P` is the numbered RHS of a fetched assign of `P`. -/
theorem mem_allExprs {P : Program} {e : Expr} (h : e ∈ allExprs P) :
    ∃ nd x next, P.fetch nd = some (.assign x e next) := by
  obtain ⟨nd, _, he⟩ := mem_allExprs_range.mp h
  obtain ⟨x, next, hf, _⟩ := mem_ue he
  exact ⟨nd, x, next, hf⟩

/-- **Freshness discharge.** An inserted `e ∈ allExprs P` reads no `tempFor` temp. -/
theorem insert_fresh {P : Program} {e e' : Expr} (he : e ∈ allExprs P) :
    exprReadsVar e (tempFor P e') = false := by
  obtain ⟨nd, x, next, hf⟩ := mem_allExprs he
  have hun : tempFor P e' ∉ instrUsedVars (.assign x e next) := tempFor_unread P e' hf
  cases hc : exprReadsVar e (tempFor P e') with
  | false => rfl
  | true => exact absurd (readsVar_imp_mem hc) hun


end BaseLanguage.Analyses.LCM
