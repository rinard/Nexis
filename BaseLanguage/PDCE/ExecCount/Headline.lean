-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.ExecCount.Bounds

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
set_option linter.unusedVariables false

/-! ## The operational fold `execCount(transform) a = matCount`

Fuel-level block-simulation bricks with counting — the `run`/`stepCount` analogues of LCM's
`run_insChain`/`run_exitChain` (`EvalCount.lean:58/140`) and the `Correctness.lean` relational executors
(`steps_assignSeg`/`steps_edgeSeg`), which are `Steps`-level and so cannot carry fuel or a count. The PDCE
version is thinner than LCM's: the transform materializes the **real** assignment `⟨x,e⟩` (not a `tempFor`
temp), so `firesAsgn (transform P S) a` at a chain slot is `decide (a = m[k])` and the per-segment count is
`(m.filter (·=a)).length = [a ∈ m]` (`count_filter_eq_nodup`). These feed the per-block execCount lemmas
(the source `.assign` floats to a `.noop` control ⇒ per block, `execCount a = [a∈matNode] + [a∈matEdge succ]`
= `matCount`'s per-step contribution) and the fold `execCount(transform) a = matCount`. -/

/-- Count of an `Asgn` list filtered by equality-to-`a`, on a nodup list, is the 0/1 membership indicator. -/
theorem count_filter_eq_nodup {l : List Asgn} (hnd : l.Nodup) (a : Asgn) :
    (l.filter (fun x => decide (a = x))).length = if a ∈ l then 1 else 0 := by
  induction l with
  | nil => simp
  | cons b rest ih =>
      rw [List.filter_cons]
      have hrest_nd : rest.Nodup := (List.nodup_cons.mp hnd).2
      have hnotin : b ∉ rest := (List.nodup_cons.mp hnd).1
      by_cases hab : a = b
      · subst hab
        rw [if_pos (by simp), List.length_cons, ih hrest_nd, if_neg hnotin,
            if_pos (List.mem_cons_self ..)]
      · have hbeq : decide (a = b) = false := by simp [hab]
        simp only [hbeq, Bool.false_eq_true, if_false]
        rw [ih hrest_nd]
        by_cases hb : a ∈ rest
        · rw [if_pos hb, if_pos (List.mem_cons_of_mem _ hb)]
        · rw [if_neg hb, if_neg (by rw [List.mem_cons]; rintro (h | h); exact hab h; exact hb h)]

-- `run_add` (generic run additivity; fuel-level composition of segment runs) is a shared
-- reference-semantics lemma hoisted to `IR.TAC` (`namespace Semantics`).

/-- **Fuel-level `matChain` executor with count.** A straight-line assignment segment (each slot jumps to
    the next) runs over `m.length` fuel, materializing every `b ∈ m` to `vals b.lhs`, and fires the query
    assignment `a0` exactly `(m.filter (·=a0)).length` times. The `run`/`stepCount` analogue of
    `steps_assignSeg`. -/
theorem run_matChainSeg {Q : Program} (a0 : Asgn) :
    ∀ (m : List Asgn) (s0 : Nat) (τ : Store) (vals : Var → Val),
    m.Nodup →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs (s0 + k + 1))) →
    (∀ b ∈ m, eval τ b.rhs = some (vals b.lhs)) →
    (∀ b ∈ m, ∀ c ∈ m, b ≠ c → exprReadsVar b.rhs c.lhs = false) →
    (∀ b ∈ m, ∀ c ∈ m, b ≠ c → b.lhs ≠ c.lhs) →
    ∃ τ', run Q ⟨s0, τ⟩ m.length = (⟨s0 + m.length, τ'⟩, .next ⟨s0 + m.length, τ'⟩)
        ∧ (∀ v, (∀ b ∈ m, b.lhs ≠ v) → τ' v = τ v)
        ∧ (∀ b ∈ m, τ' b.lhs = vals b.lhs)
        ∧ stepCount Q (firesAsgn Q a0) ⟨s0, τ⟩ m.length
            = (m.filter (fun x => decide (a0 = x))).length := by
  intro m
  induction m with
  | nil =>
      intro s0 τ vals _ _ _ _ _
      exact ⟨τ, by simp [run], fun v _ => rfl, fun b h => by simp at h, by simp [stepCount]⟩
  | cons b rest ih =>
      intro s0 τ vals hnodup hfetch hrec hfresh hdist
      have hb_mem : b ∈ b :: rest := List.mem_cons_self ..
      have hnotin : b ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have hfetch0 : Q.fetch s0 = some (.assign b.lhs b.rhs (s0 + 1)) := by
        have := hfetch 0 (by simp); simpa using this
      have heval0 : eval τ b.rhs = some (vals b.lhs) := hrec b hb_mem
      have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨s0 + 1, τ.update b.lhs (vals b.lhs)⟩ := by
        simp only [step1, hfetch0, heval0]
      have hfetch' : ∀ k (hk : k < rest.length),
          Q.fetch ((s0 + 1) + k) = some (.assign (rest[k]'hk).lhs (rest[k]'hk).rhs ((s0 + 1) + k + 1)) := by
        intro k hk
        have hk' : k + 1 < (b :: rest).length := by simp; omega
        have := hfetch (k + 1) hk'
        have hidx : (b :: rest)[k+1]'hk' = rest[k]'hk := by simp
        rw [hidx] at this
        rw [show s0 + 1 + k = s0 + (k + 1) from by omega]; exact this
      have hrec' : ∀ c ∈ rest, eval (τ.update b.lhs (vals b.lhs)) c.rhs = some (vals c.lhs) := by
        intro c hc
        have hbc : b ≠ c := fun h => hnotin (h ▸ hc)
        have hbr : exprReadsVar c.rhs b.lhs = false :=
          hfresh c (List.mem_cons_of_mem _ hc) b hb_mem (Ne.symm hbc)
        rw [eval_update_not_read hbr]; exact hrec c (List.mem_cons_of_mem _ hc)
      have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → exprReadsVar x.rhs y.lhs = false :=
        fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → x.lhs ≠ y.lhs :=
        fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
      obtain ⟨τ', hrun, hoff, hon, hcnt⟩ :=
        ih (s0 + 1) (τ.update b.lhs (vals b.lhs)) vals hrest_nodup hfetch' hrec' hfresh' hdist'
      refine ⟨τ', ?_, ?_, ?_, ?_⟩
      · show run Q ⟨s0, τ⟩ (rest.length + 1) = _
        rw [show run Q ⟨s0, τ⟩ (rest.length + 1)
              = run Q ⟨s0 + 1, τ.update b.lhs (vals b.lhs)⟩ rest.length from by simp only [run, hstep0]]
        rw [hrun, show (s0 + 1) + rest.length = s0 + (b :: rest).length from by simp; omega]
      · intro v hv
        have hbv : b.lhs ≠ v := hv b hb_mem
        have heq : τ' v = (τ.update b.lhs (vals b.lhs)) v :=
          hoff v (fun c hc => hv c (List.mem_cons_of_mem _ hc))
        rw [heq, Store.update, if_neg (fun h => hbv h.symm)]
      · intro x hx
        rcases List.mem_cons.mp hx with heq | hx
        · rw [heq]
          have hno : ∀ c ∈ rest, c.lhs ≠ b.lhs := fun c hc =>
            hdist c (List.mem_cons_of_mem _ hc) b hb_mem (fun h => hnotin (h ▸ hc))
          have heq2 : τ' b.lhs = (τ.update b.lhs (vals b.lhs)) b.lhs := hoff b.lhs hno
          rw [heq2, Store.update, if_pos rfl]
        · exact hon x hx
      · show stepCount Q (firesAsgn Q a0) ⟨s0, τ⟩ (rest.length + 1) = _
        rw [stepCount_next hstep0, hcnt]
        have hfire : firesAsgn Q a0 (⟨s0, τ⟩ : Config).node = decide (a0 = b) := by
          show firesAsgn Q a0 s0 = decide (a0 = b)
          unfold firesAsgn; rw [hfetch0]
        rw [hfire, List.filter_cons]
        by_cases hab : a0 = b
        · have hc : decide (a0 = b) = true := by simp [hab]
          rw [if_pos hc, if_pos hc, List.length_cons]; omega
        · have hc : ¬ (decide (a0 = b) = true) := by simp [hab]
          rw [if_neg hc, if_neg hc]; omega

/-- **Fuel-level `edgeChain` executor with count.** Like `run_matChainSeg`, but the **last** slot jumps to
    `target` (= `blockOff s`); a non-empty chain runs to `⟨target, τ'⟩`, an empty one stays at `s0`. Fires
    the query `a0` exactly `(m.filter (·=a0)).length` times. The `run`/`stepCount` analogue of `steps_edgeSeg`. -/
theorem run_edgeChainSeg {Q : Program} (a0 : Asgn) (target : Nat) :
    ∀ (m : List Asgn) (s0 : Nat) (τ : Store) (vals : Var → Val),
    m.Nodup →
    (∀ k (hk : k < m.length),
      Q.fetch (s0 + k) = some (.assign (m[k]'hk).lhs (m[k]'hk).rhs
        (if k + 1 == m.length then target else s0 + k + 1))) →
    (∀ b ∈ m, eval τ b.rhs = some (vals b.lhs)) →
    (∀ b ∈ m, ∀ c ∈ m, b ≠ c → exprReadsVar b.rhs c.lhs = false) →
    (∀ b ∈ m, ∀ c ∈ m, b ≠ c → b.lhs ≠ c.lhs) →
    ∃ τ', run Q ⟨s0, τ⟩ m.length
            = (⟨(if m.isEmpty then s0 else target), τ'⟩, .next ⟨(if m.isEmpty then s0 else target), τ'⟩)
        ∧ (∀ v, (∀ b ∈ m, b.lhs ≠ v) → τ' v = τ v)
        ∧ (∀ b ∈ m, τ' b.lhs = vals b.lhs)
        ∧ stepCount Q (firesAsgn Q a0) ⟨s0, τ⟩ m.length
            = (m.filter (fun x => decide (a0 = x))).length := by
  intro m
  induction m with
  | nil =>
      intro s0 τ vals _ _ _ _ _
      exact ⟨τ, by simp [run], fun v _ => rfl, fun b h => by simp at h, by simp [stepCount]⟩
  | cons b rest ih =>
      intro s0 τ vals hnodup hfetch hrec hfresh hdist
      have hb_mem : b ∈ b :: rest := List.mem_cons_self ..
      have hnotin : b ∉ rest := by simpa using (List.nodup_cons.mp hnodup).1
      have hrest_nodup : rest.Nodup := (List.nodup_cons.mp hnodup).2
      have heval0 : eval τ b.rhs = some (vals b.lhs) := hrec b hb_mem
      have hcount : ∀ {t : Nat} {τ1 : Store} {tgt0 : Nat},
          step1 Q ⟨s0, τ⟩ = .next ⟨t, τ1⟩ →
          Q.fetch s0 = some (.assign b.lhs b.rhs tgt0) →
          stepCount Q (firesAsgn Q a0) ⟨t, τ1⟩ rest.length
            = (rest.filter (fun x => decide (a0 = x))).length →
          stepCount Q (firesAsgn Q a0) ⟨s0, τ⟩ (rest.length + 1)
            = ((b :: rest).filter (fun x => decide (a0 = x))).length := by
        intro t τ1 tgt0 hstep0 hf0 hcnt
        rw [stepCount_next hstep0, hcnt]
        have hfire : firesAsgn Q a0 (⟨s0, τ⟩ : Config).node = decide (a0 = b) := by
          show firesAsgn Q a0 s0 = decide (a0 = b); unfold firesAsgn; rw [hf0]
        rw [hfire, List.filter_cons]
        by_cases hab : a0 = b
        · have hc : decide (a0 = b) = true := by simp [hab]
          rw [if_pos hc, if_pos hc, List.length_cons]; omega
        · have hc : ¬ (decide (a0 = b) = true) := by simp [hab]
          rw [if_neg hc, if_neg hc]; omega
      by_cases hre : rest = []
      · subst hre
        have hf0 : Q.fetch (s0 + 0) = some (.assign b.lhs b.rhs target) := by
          have := hfetch 0 (by simp); simpa using this
        have hf0' : Q.fetch s0 = some (.assign b.lhs b.rhs target) := by simpa using hf0
        have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨target, τ.update b.lhs (vals b.lhs)⟩ := by
          simp only [step1, hf0', heval0]
        refine ⟨τ.update b.lhs (vals b.lhs), ?_, ?_, ?_, ?_⟩
        · simp only [List.isEmpty_cons, Bool.false_eq_true, if_false]
          show run Q ⟨s0, τ⟩ 1 = _; simp only [run, hstep0]
        · intro v hv; rw [Store.update, if_neg (fun h => (hv b hb_mem) h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · rw [heq, Store.update, if_pos rfl]
          · simp at hx
        · show stepCount Q (firesAsgn Q a0) ⟨s0, τ⟩ (0 + 1) = _
          exact hcount hstep0 hf0' (by simp [stepCount])
      · have hf0 : Q.fetch (s0 + 0) = some (.assign b.lhs b.rhs (s0 + 0 + 1)) := by
          have := hfetch 0 (by simp)
          rw [if_neg (by simp; omega)] at this; simpa using this
        have hf0' : Q.fetch s0 = some (.assign b.lhs b.rhs (s0 + 1)) := by simpa using hf0
        have hstep0 : step1 Q ⟨s0, τ⟩ = .next ⟨s0 + 1, τ.update b.lhs (vals b.lhs)⟩ := by
          simp only [step1, hf0', heval0]
        have hfetch' : ∀ k (hk : k < rest.length),
            Q.fetch ((s0 + 1) + k) = some (.assign (rest[k]'hk).lhs (rest[k]'hk).rhs
              (if k + 1 == rest.length then target else (s0 + 1) + k + 1)) := by
          intro k hk
          have hk' : k + 1 < (b :: rest).length := by simp; omega
          have := hfetch (k + 1) hk'
          have hidx : (b :: rest)[k+1]'hk' = rest[k]'hk := by simp
          rw [hidx] at this
          rw [show s0 + 1 + k = s0 + (k + 1) from by omega]
          have hcond : (k + 1 + 1 == (b :: rest).length) = (k + 1 == rest.length) := by
            simp [List.length_cons]
          rw [hcond] at this
          rcases Nat.decEq (k + 1) rest.length with hc | hc
          · rw [if_neg (by simpa using hc)] at this ⊢; exact this
          · rw [if_pos (by simpa using hc)] at this ⊢; exact this
        have hrec' : ∀ c ∈ rest, eval (τ.update b.lhs (vals b.lhs)) c.rhs = some (vals c.lhs) := by
          intro c hc
          have hbc : b ≠ c := fun h => hnotin (h ▸ hc)
          have hbr : exprReadsVar c.rhs b.lhs = false :=
            hfresh c (List.mem_cons_of_mem _ hc) b hb_mem (Ne.symm hbc)
          rw [eval_update_not_read hbr]; exact hrec c (List.mem_cons_of_mem _ hc)
        have hfresh' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → exprReadsVar x.rhs y.lhs = false :=
          fun x hx y hy => hfresh x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        have hdist' : ∀ x ∈ rest, ∀ y ∈ rest, x ≠ y → x.lhs ≠ y.lhs :=
          fun x hx y hy => hdist x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
        obtain ⟨τ', hrun, hoff, hon, hcnt⟩ :=
          ih (s0 + 1) (τ.update b.lhs (vals b.lhs)) vals hrest_nodup hfetch' hrec' hfresh' hdist'
        rw [if_neg (by simpa using hre)] at hrun
        refine ⟨τ', ?_, ?_, ?_, ?_⟩
        · rw [show (b :: rest).isEmpty = false from by simp, if_neg (by simp)]
          show run Q ⟨s0, τ⟩ (rest.length + 1) = _
          rw [show run Q ⟨s0, τ⟩ (rest.length + 1)
                = run Q ⟨s0 + 1, τ.update b.lhs (vals b.lhs)⟩ rest.length from by simp only [run, hstep0]]
          exact hrun
        · intro v hv
          have hbv : b.lhs ≠ v := hv b hb_mem
          have heq : τ' v = (τ.update b.lhs (vals b.lhs)) v :=
            hoff v (fun c hc => hv c (List.mem_cons_of_mem _ hc))
          rw [heq, Store.update, if_neg (fun h => hbv h.symm)]
        · intro x hx
          rcases List.mem_cons.mp hx with heq | hx
          · rw [heq]
            have hno : ∀ c ∈ rest, c.lhs ≠ b.lhs := fun c hc =>
              hdist c (List.mem_cons_of_mem _ hc) b hb_mem (fun h => hnotin (h ▸ hc))
            have heq2 : τ' b.lhs = (τ.update b.lhs (vals b.lhs)) b.lhs := hoff b.lhs hno
            rw [heq2, Store.update, if_pos rfl]
          · exact hon x hx
        · exact hcount hstep0 hf0' hcnt

/-! ## Per-block fold, `execCount_fold`, and THE HEADLINE

Mirrors `Correctness.match_step` with the relational executors replaced by the fuel+count ones above; the
source `.assign` floats to a `.noop` control so per block `execCount a = [a∈matNode]+[a∈matEdge succ]` = `matCount`'s
per-step contribution. `execCount_fold` composes blocks over the source run; `transform_execCount_le_safe` is the
headline (compose the fold with `matCount_le_pl`). -/

/-- **Fuel+count `matNode` executor.** The `run`/`stepCount` version of `matNode_exec` (same fetch/fresh/dist
    setup, calling `run_matChainSeg`): runs the node-entry chain, materializing each blocked-live in-flight
    candidate to its source value, and fires `a0` exactly `[a0 ∈ matNode i]`-many times. -/
theorem matNode_execF {P : Program} (S : PdceSpec P) (a0 : Asgn) {i : Node} (hi : i < P.size) {τ σ : Store}
    (hrec : ∀ a ∈ matNode P S i, eval τ a.rhs = some (σ a.lhs)) (hindep : Indep (S.η i)) :
    ∃ τ1, run (transform P S) ⟨blockOff P S i, τ⟩ (matNode P S i).length
            = (⟨blockOff P S i + (matNode P S i).length, τ1⟩,
               .next ⟨blockOff P S i + (matNode P S i).length, τ1⟩)
        ∧ (∀ v, (∀ a ∈ matNode P S i, a.lhs ≠ v) → τ1 v = τ v)
        ∧ (∀ a ∈ matNode P S i, τ1 a.lhs = σ a.lhs)
        ∧ stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨blockOff P S i, τ⟩ (matNode P S i).length
            = ((matNode P S i).filter (fun x => decide (a0 = x))).length := by
  have hsink : ∀ a ∈ matNode P S i, a ∈ S.η i := fun a ha => (mem_matNode.mp ha).1
  refine run_matChainSeg a0 (matNode P S i) (blockOff P S i) τ σ matNode_nodup ?_ hrec ?_ ?_
  · intro k hk
    have hkb : k < (block P S i).length := by rw [block_length]; unfold blockLen; omega
    have hml : k < (matChain (matNode P S i) (blockOff P S i)).length := by
      rw [matChain_length]; exact hk
    have happ : (block P S i)[k]? = (matChain (matNode P S i) (blockOff P S i))[k]? := by
      simp only [block]; rw [List.getElem?_append_left hml]
    rw [transform_fetch hi hkb, happ, matChain_getElem? hk]
  · intro a ha b hb hab
    exact (hindep b (hsink b hb) a (hsink a ha) (Ne.symm hab)).2
  · intro a ha b hb hab
    exact (hindep a (hsink a ha) b (hsink b hb) hab).1

/-- **Fuel+count `edgeChain` executor.** The `run`/`stepCount` version of `edge_run` (calling
    `run_edgeChainSeg`): runs a per-successor edge chain, materializing it to `vals`, firing `a0` exactly
    `[a0 ∈ matEdge i s]`-many times. -/
theorem edge_runF {P : Program} (S : PdceSpec P) (a0 : Asgn) {i s : Node} (hindep : Indep (S.η i))
    (τ1 : Store) (vals : Var → Val) (est : Nat)
    (hfetch : ∀ k (hk : k < (matEdge P S i s).length),
      (transform P S).fetch (est + k) = some (.assign ((matEdge P S i s)[k]'hk).lhs
        ((matEdge P S i s)[k]'hk).rhs
        (if k + 1 == (matEdge P S i s).length then blockOff P S s else est + k + 1)))
    (hrec : ∀ a ∈ matEdge P S i s, eval τ1 a.rhs = some (vals a.lhs)) :
    ∃ τ2, run (transform P S) ⟨est, τ1⟩ (matEdge P S i s).length
            = (⟨(if (matEdge P S i s).isEmpty then est else blockOff P S s), τ2⟩,
               .next ⟨(if (matEdge P S i s).isEmpty then est else blockOff P S s), τ2⟩)
        ∧ (∀ v, (∀ a ∈ matEdge P S i s, a.lhs ≠ v) → τ2 v = τ1 v)
        ∧ (∀ a ∈ matEdge P S i s, τ2 a.lhs = vals a.lhs)
        ∧ stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨est, τ1⟩ (matEdge P S i s).length
            = ((matEdge P S i s).filter (fun x => decide (a0 = x))).length :=
  run_edgeChainSeg a0 (blockOff P S s) (matEdge P S i s) est τ1 vals matEdge_nodup hfetch hrec
    (fun _ ha _ hb hab => (Indep_delayedExit S hindep (mem_matEdge.mp hb).1 (mem_matEdge.mp ha).1 (Ne.symm hab)).2)
    (fun _ ha _ hb hab => (Indep_delayedExit S hindep (mem_matEdge.mp ha).1 (mem_matEdge.mp hb).1 hab).1)

/-- **Control + edge run with count**, shared by all four control cases. Given the control step (noop or
    ifz, already resolved to the taken successor's edge chain) and the edge fetch facts, runs `1 + |matEdge|`
    fuel from the control slot to `⟨blockOff next, τ2⟩`, firing `a0` exactly `[a0 ∈ matEdge nd next]` times
    (the control slot fires nothing). -/
theorem ctrlEdge_run {P : Program} (S : PdceSpec P) (a0 : Asgn) {nd next : Node}
    (hindep : Indep (S.η nd)) (τ1 : Store) (vals : Var → Val) (est : Nat)
    (hctlstep : step1 (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
        = .next ⟨(if (matEdge P S nd next).isEmpty then blockOff P S next else est), τ1⟩)
    (hctlfire : firesAsgn (transform P S) a0 (blockOff P S nd + (matNode P S nd).length) = false)
    (hef : ∀ k (hk : k < (matEdge P S nd next).length),
      (transform P S).fetch (est + k)
        = some (.assign ((matEdge P S nd next)[k]'hk).lhs ((matEdge P S nd next)[k]'hk).rhs
          (if k + 1 == (matEdge P S nd next).length then blockOff P S next else est + k + 1)))
    (her : ∀ a ∈ matEdge P S nd next, eval τ1 a.rhs = some (vals a.lhs)) :
    ∃ τ2, run (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
              ((matEdge P S nd next).length + 1)
            = (⟨blockOff P S next, τ2⟩, .next ⟨blockOff P S next, τ2⟩)
        ∧ (∀ v, (∀ a ∈ matEdge P S nd next, a.lhs ≠ v) → τ2 v = τ1 v)
        ∧ (∀ a ∈ matEdge P S nd next, τ2 a.lhs = vals a.lhs)
        ∧ stepCount (transform P S) (firesAsgn (transform P S) a0)
            ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩ ((matEdge P S nd next).length + 1)
            = ((matEdge P S nd next).filter (fun x => decide (a0 = x))).length := by
  by_cases he : (matEdge P S nd next).isEmpty
  · have hemp : matEdge P S nd next = [] := List.isEmpty_iff.mp he
    have hlen0 : (matEdge P S nd next).length = 0 := by rw [hemp]; rfl
    refine ⟨τ1, ?_, fun v _ => rfl, ?_, ?_⟩
    · rw [hlen0]; simp only [run, hctlstep, if_pos he]
    · intro a ha; rw [hemp] at ha; simp at ha
    · rw [hlen0, stepCount_next hctlstep, hemp]; simp [hctlfire, stepCount]
  · obtain ⟨τ2, hrun2, hoff2, hon2, hcnt2⟩ := edge_runF S a0 hindep τ1 vals est hef her
    rw [if_neg he] at hrun2
    refine ⟨τ2, ?_, hoff2, hon2, ?_⟩
    · simp only [run, hctlstep, if_neg he]; exact hrun2
    · rw [stepCount_next hctlstep, if_neg he, hcnt2]; simp [hctlfire]

/-- Per-block fuel to the **taken** successor: the matNode chain, the control, and the taken edge chain
    (the other `ifz` edge chain is jumped over, so it is not in the fuel). -/
def blockFuelTo (P : Program) (S : PdceSpec P) (nd succ : Node) : Nat :=
  (matNode P S nd).length + ((matEdge P S nd succ).length + 1)

/-- **The per-block fold with count.** Mirrors `Correctness.match_step` with the relational executors
    (`matNode_exec`/`edge_run`) replaced by the fuel+count ones (`matNode_execF`/`ctrlEdge_run`): a source step
    `c → c'` runs `c`'s block to `⟨blockOff c'.node, τF⟩`, preserves `Match`, and executes `a0` exactly
    `[a0∈matNode c.node] + [a0∈matEdge c.node c'.node]` times. The `Match`-clause derivations are verbatim from
    `match_step` (they use only the executor store facts, identical in both). -/
theorem block_execCount {P : Program} (S : PdceSpec P) (wf : WellFormed P) (a0 : Asgn)
    {c c' d : Config} (hm : Match P S c d) (hstep : Step P c c') :
    ∃ τF, run (transform P S) d (blockFuelTo P S c.node c'.node)
            = (⟨blockOff P S c'.node, τF⟩, .next ⟨blockOff P S c'.node, τF⟩)
        ∧ Match P S c' ⟨blockOff P S c'.node, τF⟩
        ∧ execCount (transform P S) a0 d (blockFuelTo P S c.node c'.node)
            = (if a0 ∈ matNode P S c.node then 1 else 0)
              + (if a0 ∈ matEdge P S c.node c'.node then 1 else 0) := by
  obtain ⟨hnode, h2, hrec, hindep⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  cases hstep with
  | noop hf =>
    rename_i nd σ next
    subst hnode
    have hi : nd < P.size := fetch_lt hf
    have hnext : next < P.size := wf.succ_lt hf (by simp [Cmd.succs])
    have hstp : Step P (⟨nd, σ⟩ : Config) ⟨next, σ⟩ := Step.noop hf
    have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
    have hkills : ∀ a : Asgn, kills P nd a = false := by
      intro a; simp [kills, useV, defV, hf, instrUsedVars, instrDefVar]
    have hsink_transp : ∀ a, a ∈ S.η nd → a ∈ pass P nd := fun a ha =>
      mem_transp.mpr ⟨hbound nd a ha, hkills a⟩
    have hlive_mono : ∀ x, x ∈ S.π next → x ∈ S.π nd := by
      intro x hx
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x hx) with h | h
      · exact h
      · simp only [defVars, defV, instrDefVar, hf, Variables.empty] at h
        exact absurd h Std.HashSet.not_mem_empty
    have hsink_next : ∀ a, a ∈ S.η next → a ∈ S.η nd ∧ a ∈ pass P nd := by
      intro a ha
      have := S.isSink.update _ _ hstp a ha
      rcases mem_delayedExit.mp this with hb | h
      · rw [show born P nd = (∅ : Assignments) from by unfold born; rw [hf]] at hb
        exact absurd hb Std.HashSet.not_mem_empty
      · exact h
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hrun1, hoff1, hon1, hcnt1⟩ := matNode_execF S a0 hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1
      simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have her : ∀ a ∈ matEdge P S nd next, eval τ1 a.rhs = some (σ a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [show born P nd = (∅ : Assignments) from by unfold born; rw [hf]] at hb
        exact absurd hb Std.HashSet.not_mem_empty
      · have hli : a.lhs ∈ S.π nd := hlive_mono a.lhs hls
        have hr : eval dσ a.rhs = some (σ a.lhs) := hrec a.lhs a.rhs has hli
        rw [eval_congr (fun v hv => ?_)]
        · exact hr
        · refine hoff1 v (fun m hm hmv => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (mem_matNode.mp hm |>.1) a has (hmne)).2
          rw [hmv] at this; rw [this] at hv; exact absurd hv (by simp)
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
    have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
        = .next ⟨(if (matEdge P S nd next).isEmpty then blockOff P S next
                  else blockOff P S nd + (matNode P S nd).length + 1), τ1⟩ := by
      simp only [step1, hctl]
    have hctlfire : firesAsgn (transform P S) a0 (blockOff P S nd + (matNode P S nd).length) = false := by
      simp only [firesAsgn, hctl]
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
    obtain ⟨τ2, hrune, hoffe, hone, hcnte⟩ :=
      ctrlEdge_run S a0 hindep τ1 σ (blockOff P S nd + (matNode P S nd).length + 1) hctlstep hctlfire hef her
    refine ⟨τ2, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd next) = _
      rw [show blockFuelTo P S nd next
            = (matNode P S nd).length + ((matEdge P S nd next).length + 1) from rfl,
          run_add hrun1 ((matEdge P S nd next).length + 1)]
      exact hrune
    · intro x hxlive hxnf
      show τ2 x = σ x
      by_cases hxe : ∃ a ∈ matEdge P S nd next, a.lhs = x
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · have hτ2x : τ2 x = τ1 x := hoffe x (fun a ha hax => hxe ⟨a, ha, hax⟩)
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x
        · obtain ⟨m, hm, rfl⟩ := hxn; rw [hτ2x]; exact hon1 m hm
        · rw [hτ2x, hoff1 x (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x (hlive_mono x hxlive) (fun e' hmem => ?_)
          have hat : (⟨x, e'⟩ : Asgn) ∈ pass P nd := hsink_transp _ hmem
          have hde : (⟨x, e'⟩ : Asgn) ∈ delayedExit P S nd := mem_delayedExit.mpr (Or.inr ⟨hmem, hat⟩)
          have hns : (⟨x, e'⟩ : Asgn) ∉ S.η next := hxnf e'
          have hin : (⟨x, e'⟩ : Asgn) ∈ matEdge P S nd next := mem_matEdge.mpr ⟨hde, hns, hxlive⟩
          exact hxe ⟨⟨x, e'⟩, hin, rfl⟩
    · intro x e hmem hxlive
      show eval τ2 e = some (σ x)
      have hupd := hsink_next _ hmem
      have hli : x ∈ S.π nd := hlive_mono x hxlive
      have hr : eval dσ e = some (σ x) := hrec x e hupd.1 hli
      rw [eval_congr (fun v hv => ?_)]
      · exact hr
      · have hvne_edge : ∀ a ∈ matEdge P S nd next, a.lhs ≠ v := by
          intro a ha hav
          have hane : a ≠ ⟨x, e⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
          have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
            (mem_delayedExit.mpr (Or.inr hupd)) hane).2
          rw [hav] at this; rw [this] at hv; exact absurd hv (by simp)
        have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ v := by
          intro m hm hmv
          have hmne : m ≠ (⟨x, e⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hupd.2)
          have := (hindep m (mem_matNode.mp hm).1 ⟨x, e⟩ hupd.1 hmne).2
          rw [hmv] at this; rw [this] at hv; exact absurd hv (by simp)
        rw [hoffe v hvne_edge, hoff1 v hvne_node]
    · exact Indep_step S (Step.noop hf) hindep
    · show execCount (transform P S) a0 ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd next) = _
      show stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨blockOff P S nd, dσ⟩
          (blockFuelTo P S nd next) = _
      rw [show blockFuelTo P S nd next
            = (matNode P S nd).length + ((matEdge P S nd next).length + 1) from rfl,
          stepCount_add hrun1 ((matEdge P S nd next).length + 1), hcnt1, hcnte,
          count_filter_eq_nodup matNode_nodup, count_filter_eq_nodup matEdge_nodup]
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
    have hpred : ∀ x', x' ∈ S.π next → x' ∈ S.π nd ∨ x' = x := by
      intro x' hx'
      rcases Variables.mem_union.mp (S.isLive.predict _ _ hstp x' hx') with h | h
      · exact Or.inl h
      · right; simp only [defVars, hdefV] at h; exact Variables.mem_singleton.mp h
    have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (σ a.lhs) := by
      intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
    obtain ⟨τ1, hrun1, hoff1, hon1, hcnt1⟩ := matNode_execF S a0 hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.η nd
      · obtain ⟨ew, hew⟩ := hwf
        have hk : kills P nd ⟨w, ew⟩ = true := by
          simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        have hmn : (⟨w, ew⟩ : Asgn) ∈ matNode P S nd :=
          mem_matNode.mpr ⟨hew, by simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hew, hntr⟩, hwl⟩
        exact hon1 ⟨w, ew⟩ hmn
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.η nd := fun e' h => hwf ⟨e', h⟩
        rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
        exact h2 w hwl hnf
    have hgate_live : x ∈ S.π next → ∀ w, w ∈ useV P nd → w ∈ S.π nd := by
      intro hxln w hw
      refine S.isLive.gate _ _ hstp ⟨x, ?_, hxln⟩ w ?_
      · simp only [defVars, hdefV]; exact Variables.mem_singleton.mpr rfl
      · simp only [rhsVars, hf, usedVars]; exact Variables.mem_ofList.mpr hw
    have her : ∀ a ∈ matEdge P S nd next, eval τ1 a.rhs = some ((σ.update x v) a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [hbornx, Assignments.mem_singleton] at hb; subst hb
        show eval τ1 e = some ((σ.update x v) x)
        rw [show (σ.update x v) x = v from by rw [Store.update, if_pos rfl]]
        rw [eval_congr (fun w hw => ?_)]
        · exact hv
        · exact hop_fresh w (huseV ▸ readsVar_imp_mem hw) (hgate_live hls _ (huseV ▸ readsVar_imp_mem hw))
      · have hxne : a.lhs ≠ x := fun h => (transp_facts hat).2.1 (by rw [hdefV, h])
        rw [show (σ.update x v) a.lhs = σ a.lhs from by rw [Store.update, if_neg hxne]]
        have hli : a.lhs ∈ S.π nd := (hpred a.lhs hls).resolve_right hxne
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec a.lhs a.rhs has hli
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (mem_matNode.mp hm).1 a has hmne).2
          rw [hmw] at this; rw [this] at hw; exact absurd hw (by simp)
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
    have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
        = .next ⟨(if (matEdge P S nd next).isEmpty then blockOff P S next
                  else blockOff P S nd + (matNode P S nd).length + 1), τ1⟩ := by
      simp only [step1, hctl]
    have hctlfire : firesAsgn (transform P S) a0 (blockOff P S nd + (matNode P S nd).length) = false := by
      simp only [firesAsgn, hctl]
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
    obtain ⟨τ2, hrune, hoffe, hone, hcnte⟩ :=
      ctrlEdge_run S a0 hindep τ1 (σ.update x v) (blockOff P S nd + (matNode P S nd).length + 1)
        hctlstep hctlfire hef her
    refine ⟨τ2, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd next) = _
      rw [show blockFuelTo P S nd next
            = (matNode P S nd).length + ((matEdge P S nd next).length + 1) from rfl,
          run_add hrun1 ((matEdge P S nd next).length + 1)]
      exact hrune
    · intro x' hxlive hxnf
      show τ2 x' = (σ.update x v) x'
      by_cases hxe : ∃ a ∈ matEdge P S nd next, a.lhs = x'
      · obtain ⟨a, ha, rfl⟩ := hxe; exact hone a ha
      · have hx'x : x' ≠ x := fun h => hxe ⟨⟨x, e⟩,
          mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inl (by rw [hbornx]; exact Assignments.mem_singleton.mpr rfl)),
            h ▸ hxnf e, h ▸ hxlive⟩, h.symm⟩
        rw [hoffe x' (fun a ha hax => hxe ⟨a, ha, hax⟩),
            show (σ.update x v) x' = σ x' from by rw [Store.update, if_neg hx'x]]
        by_cases hxn : ∃ m ∈ matNode P S nd, m.lhs = x'
        · obtain ⟨m, hm, rfl⟩ := hxn; exact hon1 m hm
        · rw [hoff1 x' (fun m hm hmx => hxn ⟨m, hm, hmx⟩)]
          refine h2 x' ((hpred x' hxlive).resolve_right hx'x) (fun e' hmem => ?_)
          by_cases htr : (⟨x', e'⟩ : Asgn) ∈ pass P nd
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, (hpred x' hxlive).resolve_right hx'x⟩, rfl⟩
            simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hmem, htr⟩
    · intro x' e' hmem hxlive
      show eval τ2 e' = some ((σ.update x v) x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ hmem
      rcases mem_delayedExit.mp hupd with hb | ⟨has, hat⟩
      · rw [hbornx, Assignments.mem_singleton] at hb
        injection hb with hxx hee
        have hmemxe : (⟨x, e⟩ : Asgn) ∈ S.η next := by rw [← hxx, ← hee]; exact hmem
        rw [show (σ.update x v) x' = v from by rw [hxx, Store.update, if_pos rfl], hee]
        rw [eval_congr (fun w hw => ?_)]
        · exact hv
        · have hwu : w ∈ useV P nd := huseV ▸ readsVar_imp_mem hw
          have hwne : ∀ a ∈ matEdge P S nd next, a.lhs ≠ w := by
            intro a ha haw
            rcases mem_delayedExit.mp (mem_matEdge.mp ha).1 with hab | ⟨_, hatr⟩
            · rw [hbornx, Assignments.mem_singleton] at hab
              rw [hab] at ha; exact (mem_matEdge.mp ha).2.1 hmemxe
            · exact (transp_facts hatr).1 (haw ▸ hwu)
          rw [hoffe w hwne]; exact hop_fresh w hwu (hgate_live (hxx ▸ hxlive) _ hwu)
      · have hxne : x' ≠ x := fun h => (transp_facts hat).2.1 (by rw [hdefV, h])
        rw [show (σ.update x v) x' = σ x' from by rw [Store.update, if_neg hxne]]
        have hli : x' ∈ S.π nd := (hpred x' hxlive).resolve_right hxne
        rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' has hli
        · have hvne_edge : ∀ a ∈ matEdge P S nd next, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨has, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (mem_matNode.mp hm).1 ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep
    · show execCount (transform P S) a0 ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd next) = _
      show stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨blockOff P S nd, dσ⟩
          (blockFuelTo P S nd next) = _
      rw [show blockFuelTo P S nd next
            = (matNode P S nd).length + ((matEdge P S nd next).length + 1) from rfl,
          stepCount_add hrun1 ((matEdge P S nd next).length + 1), hcnt1, hcnte,
          count_filter_eq_nodup matNode_nodup, count_filter_eq_nodup matEdge_nodup]
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
    obtain ⟨τ1, hrun1, hoff1, hon1, hcnt1⟩ := matNode_execF S a0 hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.η nd
      · obtain ⟨ew, hew⟩ := hwf
        have hk : kills P nd ⟨w, ew⟩ = true := by simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        exact hon1 ⟨w, ew⟩ (mem_matNode.mpr ⟨hew,
          by simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hew, hntr⟩, hwl⟩)
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.η nd := fun e' h => hwf ⟨e', h⟩
        rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
        exact h2 w hwl hnf
    have hxlive_nd : x ∈ S.π nd := S.isLive.check nd x (by
      simp only [condVars, hf, usedVars]; exact Variables.mem_ofList.mpr (by rw [huseV]; simp))
    have hxsync : τ1 x = 0 := by rw [hop_fresh x (by rw [huseV]; simp) hxlive_nd]; exact hz
    have her : ∀ a ∈ matEdge P S nd z, eval τ1 a.rhs = some (σ a.lhs) := by
      intro a ha
      obtain ⟨hde, hns, hls⟩ := mem_matEdge.mp ha
      rcases mem_delayedExit.mp hde with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · rw [eval_congr (fun w hw => ?_)]
        · exact hrec a.lhs a.rhs has (hlive_mono a.lhs hls)
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (mem_matNode.mp hm).1 a has hmne).2
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
    have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
        = .next ⟨(if (matEdge P S nd z).isEmpty then blockOff P S z
                  else blockOff P S nd + (matNode P S nd).length + 1), τ1⟩ := by
      simp only [step1, hctl, if_pos hxsync]
    have hctlfire : firesAsgn (transform P S) a0 (blockOff P S nd + (matNode P S nd).length) = false := by
      simp only [firesAsgn, hctl]
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
    obtain ⟨τ2, hrune, hoffe, hone, hcnte⟩ :=
      ctrlEdge_run S a0 hindep τ1 σ (blockOff P S nd + (matNode P S nd).length + 1) hctlstep hctlfire hef her
    refine ⟨τ2, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd z) = _
      rw [show blockFuelTo P S nd z
            = (matNode P S nd).length + ((matEdge P S nd z).length + 1) from rfl,
          run_add hrun1 ((matEdge P S nd z).length + 1)]
      exact hrune
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
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, hlive_mono x' hxlive⟩, rfl⟩
            simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hmem, htr⟩
    · intro x' e' hmem hxlive
      show eval τ2 e' = some (σ x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ hmem
      rcases mem_delayedExit.mp hupd with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' has (hlive_mono x' hxlive)
        · have hvne_edge : ∀ a ∈ matEdge P S nd z, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨has, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (mem_matNode.mp hm).1 ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep
    · show execCount (transform P S) a0 ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd z) = _
      show stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨blockOff P S nd, dσ⟩
          (blockFuelTo P S nd z) = _
      rw [show blockFuelTo P S nd z
            = (matNode P S nd).length + ((matEdge P S nd z).length + 1) from rfl,
          stepCount_add hrun1 ((matEdge P S nd z).length + 1), hcnt1, hcnte,
          count_filter_eq_nodup matNode_nodup, count_filter_eq_nodup matEdge_nodup]
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
    obtain ⟨τ1, hrun1, hoff1, hon1, hcnt1⟩ := matNode_execF S a0 hi hrn hindep
    have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
      intro m hm hmt
      have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
      exact (Assignments.mem_sdiff.mp hb).2 hmt
    have hop_fresh : ∀ w, w ∈ useV P nd → w ∈ S.π nd → τ1 w = σ w := by
      intro w hw hwl
      by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.η nd
      · obtain ⟨ew, hew⟩ := hwf
        have hk : kills P nd ⟨w, ew⟩ = true := by simp [kills, List.contains_eq_mem, hw]
        have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
          have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
        exact hon1 ⟨w, ew⟩ (mem_matNode.mpr ⟨hew,
          by simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hew, hntr⟩, hwl⟩)
      · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.η nd := fun e' h => hwf ⟨e', h⟩
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
        · exact hrec a.lhs a.rhs has (hlive_mono a.lhs hls)
        · refine hoff1 w (fun m hm hmw => ?_)
          have hmne : m ≠ a := fun h => hmat_ntransp m hm (h ▸ hat)
          have := (hindep m (mem_matNode.mp hm).1 a has hmne).2
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
    have hctlstep : step1 (transform P S) ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
        = .next ⟨(if (matEdge P S nd nz).isEmpty then blockOff P S nz
                  else blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length), τ1⟩ := by
      simp only [step1, hctl, if_neg hxsync]
    have hctlfire : firesAsgn (transform P S) a0 (blockOff P S nd + (matNode P S nd).length) = false := by
      simp only [firesAsgn, hctl]
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
    obtain ⟨τ2, hrune, hoffe, hone, hcnte⟩ :=
      ctrlEdge_run S a0 hindep τ1 σ
        (blockOff P S nd + (matNode P S nd).length + 1 + (matEdge P S nd z).length)
        hctlstep hctlfire hef her
    refine ⟨τ2, ?_, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
    · show run (transform P S) ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd nz) = _
      rw [show blockFuelTo P S nd nz
            = (matNode P S nd).length + ((matEdge P S nd nz).length + 1) from rfl,
          run_add hrun1 ((matEdge P S nd nz).length + 1)]
      exact hrune
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
          · exact hxe ⟨⟨x', e'⟩, mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inr ⟨hmem, htr⟩), hxnf e', hxlive⟩, rfl⟩
          · refine hxn ⟨⟨x', e'⟩, mem_matNode.mpr ⟨hmem, ?_, hlive_mono x' hxlive⟩, rfl⟩
            simp only [blockedSet, hf]; exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hmem, htr⟩
    · intro x' e' hmem hxlive
      show eval τ2 e' = some (σ x')
      have hupd := S.isSink.update _ _ hstp ⟨x', e'⟩ hmem
      rcases mem_delayedExit.mp hupd with hb | ⟨has, hat⟩
      · rw [hborn0] at hb; exact absurd hb Std.HashSet.not_mem_empty
      · rw [eval_congr (fun w hw => ?_)]
        · exact hrec x' e' has (hlive_mono x' hxlive)
        · have hvne_edge : ∀ a ∈ matEdge P S nd nz, a.lhs ≠ w := by
            intro a ha hav
            have hane : a ≠ ⟨x', e'⟩ := fun h => (mem_matEdge.mp ha).2.1 (h ▸ hmem)
            have := (Indep_delayedExit S hindep (mem_matEdge.mp ha).1
              (mem_delayedExit.mpr (Or.inr ⟨has, hat⟩)) hane).2
            rw [hav] at this; rw [this] at hw; exact absurd hw (by simp)
          have hvne_node : ∀ m ∈ matNode P S nd, m.lhs ≠ w := by
            intro m hm hmv
            have hmne : m ≠ (⟨x', e'⟩ : Asgn) := fun h => hmat_ntransp m hm (h ▸ hat)
            have := (hindep m (mem_matNode.mp hm).1 ⟨x', e'⟩ has hmne).2
            rw [hmv] at this; rw [this] at hw; exact absurd hw (by simp)
          rw [hoffe w hvne_edge, hoff1 w hvne_node]
    · exact Indep_step S hstp hindep
    · show execCount (transform P S) a0 ⟨blockOff P S nd, dσ⟩ (blockFuelTo P S nd nz) = _
      show stepCount (transform P S) (firesAsgn (transform P S) a0) ⟨blockOff P S nd, dσ⟩
          (blockFuelTo P S nd nz) = _
      rw [show blockFuelTo P S nd nz
            = (matNode P S nd).length + ((matEdge P S nd nz).length + 1) from rfl,
          stepCount_add hrun1 ((matEdge P S nd nz).length + 1), hcnt1, hcnte,
          count_filter_eq_nodup matNode_nodup, count_filter_eq_nodup matEdge_nodup]

/-- **The fold.** Along a halting source run of `ks` steps, the transform's whole-run execution count
    of `a0` equals `matCount` over the source run (each source block-visit contributes `[matNode]+[matEdge]`).
    Fuel-induction composing `block_execCount` via `run_add`/`execCount_add`; dual of LCM `evalCount_fold`. -/
theorem execCount_fold {P : Program} (S : PdceSpec P) (wf : WellFormed P) (a0 : Asgn) :
    ∀ (ks : Nat) (c d c_f : Config), Match P S c d → Final P c_f →
      run P c ks = (c_f, .next c_f) →
    ∃ kt τf, run (transform P S) d kt
              = (⟨blockOff P S c_f.node, τf⟩, .next ⟨blockOff P S c_f.node, τf⟩)
          ∧ execCount (transform P S) a0 d kt = matCount P S a0 c ks := by
  intro ks
  induction ks with
  | zero =>
      intro c d c_f hm hfin hks
      obtain ⟨dn, dσ⟩ := d
      obtain ⟨hd, -, -, -⟩ := hm
      subst hd
      have hcc : c = c_f := by
        have h := hks; simp only [run] at h; exact (Prod.ext_iff.mp h).1
      subst hcc
      exact ⟨0, dσ, rfl, rfl⟩
  | succ k ih =>
      intro c d c_f hm hfin hks
      cases hstep : step1 P c with
      | next c1 =>
          have hstepR : Step P c c1 := step1_next_iff.mp hstep
          have hk : run P c1 k = (c_f, .next c_f) := by
            rw [show run P c (k + 1) = run P c1 k from by simp [run, hstep]] at hks; exact hks
          obtain ⟨τF, hblockrun, hmatch, hcount⟩ := block_execCount S wf a0 hm hstepR
          obtain ⟨kt1, τf, hrun1, hcnt1⟩ := ih c1 ⟨blockOff P S c1.node, τF⟩ c_f hmatch hfin hk
          refine ⟨blockFuelTo P S c.node c1.node + kt1, τf, ?_, ?_⟩
          · rw [run_add hblockrun kt1]; exact hrun1
          · rw [execCount_add hblockrun kt1, hcount, hcnt1, matCount_next hstep]; omega
      | halt => rw [show run P c (k + 1) = (c, .halt) from by simp [run, hstep]] at hks; simp at hks
      | fault => rw [show run P c (k + 1) = (c, .fault) from by simp [run, hstep]] at hks; simp at hks
      | stuck => rw [show run P c (k + 1) = (c, .stuck) from by simp [run, hstep]] at hks; simp at hks

/-- **THE HEADLINE — computational (execution-count) optimality of PDCE.** Along every terminating run, the
    transform executes each assignment `a` no more often than any safe covering placement `pl` computes it over
    the source path. Composes the fold (`execCount(transform) = matCount`) with `matCount_le_pl`
    (`#mat ≤ #pl`). The sinking dual of LCM's `transform_evalCount_le_safe`. -/
theorem transform_execCount_le_safe {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    (a : Asgn) (pl : Node → Bool) {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f)
    (ks : Nat) (hks : run P ⟨P.entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCoversAsgn P S a pl ⟨P.entry, σ⟩ ks false) :
    ∃ kt, execCount (transform P S) a ⟨blockOff P S P.entry, σ⟩ kt
            ≤ ((runNodes P ⟨P.entry, σ⟩ ks).filter pl).length := by
  obtain ⟨kt, τf, hrunT, hcnt⟩ :=
    execCount_fold S wf a ks ⟨P.entry, σ⟩ ⟨blockOff P S P.entry, σ⟩ c_f (match_init S σ) hfin hks
  exact ⟨kt, by rw [hcnt]; exact matCount_le_pl S a pl σ ks hcov⟩


end BaseLanguage.Analyses.PDCE
