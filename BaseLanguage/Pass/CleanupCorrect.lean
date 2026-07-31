-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Cleanup
import BaseLanguage.IR.Cfg
import BaseLanguage.Backend.Correctness.CodegenForward
import BaseLanguage.Behavior.Outcomes

/-!
# `Pass.CleanupCorrect` — verification of the noop-elim + compaction pass

Foundational lemmas toward `cleanup_preserves_halt`. Reachability is
handled through the inductive `FReach` (no analysis/fixpoint); `noop`-following (`chase`/
`resolve`) is a structural graph traversal whose *semantic* content is `resolve_steps` below: the
machine walks a `noop` chain to `resolve`'s target without changing the store.
-/

namespace BaseLanguage
namespace Pass
namespace Cleanup

open Tac Semantics

variable {P : Program}

/-- One `Step` is a `Steps`. -/
theorem oneStep {c c' : Config} (h : Step P c c') : Steps P c c' := Steps.tail Steps.refl h

/-! ## Range: `chase`/`resolve` keep a node in range. -/

theorem chase_lt (wf : WellFormed P) {fuel nd : Node} (h : nd < P.size) :
    chase P fuel nd < P.size := by
  induction fuel generalizing nd with
  | zero => exact h
  | succ f ih =>
      unfold chase
      cases hf : P.fetch nd with
      | none => simpa [hf] using h
      | some c =>
          cases c with
          | noop next =>
              exact ih (wf.succ_lt hf (by simp [Cmd.succs]))
          | assign x e nx => simpa [hf] using h
          | ifz x z nz => simpa [hf] using h
          | halt => simpa [hf] using h

theorem resolve_lt (wf : WellFormed P) {nd : Node} (h : nd < P.size) : resolve P nd < P.size :=
  chase_lt wf h

/-! ## Semantic core: following a `noop` chain preserves the store. -/

theorem chase_steps {fuel nd : Node} {σ : Store} :
    Steps P ⟨nd, σ⟩ ⟨chase P fuel nd, σ⟩ := by
  induction fuel generalizing nd with
  | zero => exact Steps.refl
  | succ f ih =>
      unfold chase
      cases hf : P.fetch nd with
      | none => exact Steps.refl
      | some c =>
          cases c with
          | noop next =>
              exact steps_trans (oneStep (Step.noop hf)) ih
          | assign x e nx => exact Steps.refl
          | ifz x z nz => exact Steps.refl
          | halt => exact Steps.refl

/-- **The original machine reaches `resolve nd` from `nd` with the store unchanged.** -/
theorem resolve_steps {nd : Node} {σ : Store} : Steps P ⟨nd, σ⟩ ⟨resolve P nd, σ⟩ := chase_steps

/-! ## `chase` algebra: composition and stabilization at a non-`noop`. -/

/-- A non-`noop` node is a fixpoint of `chase` (nothing to follow). -/
theorem chase_stuck {nd : Node} (h : ∀ nx, P.fetch nd ≠ some (.noop nx)) {b : Nat} :
    chase P b nd = nd := by
  cases b with
  | zero => rfl
  | succ b =>
      unfold chase
      cases hf : P.fetch nd with
      | none => rfl
      | some c => cases c with
        | noop nx => exact absurd hf (h nx)
        | assign x e nx => rfl
        | ifz x z nz => rfl
        | halt => rfl

/-- `chase` composes: chasing `a+b` is chasing `a` then `b`. -/
theorem chase_add {a b nd : Node} : chase P (a + b) nd = chase P b (chase P a nd) := by
  induction a generalizing nd with
  | zero => simp only [Nat.zero_add, chase]
  | succ a ih =>
      have e : a + 1 + b = (a + b) + 1 := by omega
      rw [e]
      cases hf : P.fetch nd with
      | none => simp only [chase, hf]; exact (chase_stuck (by simp [hf])).symm
      | some c => cases c with
        | noop nx => simp only [chase, hf]; exact ih
        | assign x e' nx => simp only [chase, hf]; exact (chase_stuck (by simp [hf])).symm
        | ifz x z nz => simp only [chase, hf]; exact (chase_stuck (by simp [hf])).symm
        | halt => simp only [chase, hf]; exact (chase_stuck (by simp [hf])).symm

/-- Once `chase a` has reached a non-`noop`, extra fuel does nothing. -/
theorem chase_stabilizes {a b nd : Node} (h : ∀ nx, P.fetch (chase P a nd) ≠ some (.noop nx)) :
    chase P (a + b) nd = chase P a nd := by
  rw [chase_add]; exact chase_stuck h

/-! ## `resolve` lands on a kept node (the pigeonhole / cycle-stability core). -/

/-- Is this node a `noop`? (Boolean, so we can take a least witness without Mathlib's `Nat.find`.) -/
def isNoopN (P : Program) (nd : Node) : Bool :=
  match P.fetch nd with | some (.noop _) => true | _ => false

theorem not_noop_of_isNoopN_false {nd : Node} (h : isNoopN P nd = false) (nx : Node) :
    P.fetch nd ≠ some (.noop nx) := by
  intro hf
  have h1 : isNoopN P nd = true := by unfold isNoopN; rw [hf]
  rw [h1] at h; simp at h

/-! ### Core-only helpers (this project is Mathlib-free). -/

/-- From a failure of a bounded `∀`, extract a witness (decidable, core-only). -/
theorem exists_lt_true_of_not_ball {q : Nat → Bool} : ∀ {k}, ¬(∀ i, i < k → q i = false) →
    ∃ i, i < k ∧ q i = true := by
  intro k
  induction k with
  | zero => intro h; exact absurd (fun i hi => absurd hi (Nat.not_lt_zero i)) h
  | succ k ih =>
      intro h
      cases hk : q k with
      | true => exact ⟨k, Nat.lt_succ_self k, hk⟩
      | false =>
          have hnb : ¬ (∀ i, i < k → q i = false) := by
            intro hall; apply h; intro i hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h' | h'
            · exact hall i h'
            · subst h'; exact hk
          obtain ⟨i, hik, hi⟩ := ih hnb
          exact ⟨i, Nat.lt_succ_of_lt hik, hi⟩

/-- Least witness of a decidable `Bool` predicate over `Nat` (core-only `Nat.find` replacement). -/
theorem exists_least_bool {q : Nat → Bool} : ∀ {k}, q k = true →
    ∃ m, q m = true ∧ ∀ i, i < m → q i = false := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
      intro hk
      by_cases h : ∀ i, i < k → q i = false
      · exact ⟨k, hk, h⟩
      · obtain ⟨i, hik, hi⟩ := exists_lt_true_of_not_ball h; exact ih i hik hi

/-- A range-`map` with an injective-on-`[0,n)` function is `Nodup`. -/
theorem nodup_map_range {f : Nat → Node} {n : Nat}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ((List.range n).map f).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.nodup_append]
      refine ⟨ih (fun i j hi hj => hinj i j (Nat.lt_succ_of_lt hi) (Nat.lt_succ_of_lt hj)), by simp, ?_⟩
      intro a ha b hb heq
      rw [List.mem_map] at ha; obtain ⟨i, hi, hfi⟩ := ha
      rw [List.mem_range] at hi
      rw [List.mem_map] at hb; obtain ⟨j, hj, hfj⟩ := hb
      rw [List.mem_singleton] at hj; rw [hj] at hfj
      have : i = n := hinj i n (Nat.lt_succ_of_lt hi) (Nat.lt_succ_self n) (hfi.trans (heq.trans hfj.symm))
      omega

/-- The `noop`-prefix before the first non-`noop` visits distinct nodes, so its length ≤ `P.size`. -/
theorem noopPrefix_bound (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) {m : Node}
    (hpre : ∀ i, i < m → isNoopN P (chase P i nd) = true)
    (hm : isNoopN P (chase P m nd) = false) : m < P.size := by
  have key : ∀ i j, i < j → j ≤ m → chase P i nd = chase P j nd → False := by
    intro i j hij hjm heq
    have h1 : j + (m - j) = m := Nat.add_sub_cancel' hjm
    have hchase_m : chase P m nd = chase P (i + (m - j)) nd := by
      calc chase P m nd = chase P (j + (m - j)) nd := by rw [h1]
        _ = chase P (m - j) (chase P j nd) := chase_add
        _ = chase P (m - j) (chase P i nd) := by rw [heq]
        _ = chase P (i + (m - j)) nd := chase_add.symm
    have hp : i + (m - j) < m := by
      have hlt := Nat.add_lt_add_right hij (m - j); rwa [h1] at hlt
    have ht := hpre _ hp
    rw [← hchase_m, hm] at ht
    simp at ht
  have hinj : ∀ i j, i < m + 1 → j < m + 1 → chase P i nd = chase P j nd → i = j := by
    intro i j hi hj heq
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact (key i j h (Nat.lt_succ_iff.mp hj) heq).elim
    · exact h
    · exact (key j i h (Nat.lt_succ_iff.mp hi) heq.symm).elim
  have hnodup := nodup_map_range (f := fun i => chase P i nd) (n := m + 1) hinj
  have hsub : ((List.range (m + 1)).map (fun i => chase P i nd)) ⊆ List.range P.size := by
    intro x hx; rw [List.mem_map] at hx; obtain ⟨i, _, rfl⟩ := hx
    exact List.mem_range.mpr (chase_lt wf hnd)
  have hlen := nodup_length_le_of_subset' hnodup hsub
  rw [List.length_map, List.length_range, List.length_range] at hlen
  exact Nat.lt_of_succ_le hlen

/-- If `chase k` ever reaches a non-`noop`, then `chase P.size` already has (the prefix is ≤ size). -/
theorem isNoopN_chase_size (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) {k : Node}
    (hk : isNoopN P (chase P k nd) = false) : isNoopN P (chase P P.size nd) = false := by
  have hk' : (!isNoopN P (chase P k nd)) = true := by rw [hk]; rfl
  obtain ⟨m, hm, hpre⟩ := exists_least_bool (q := fun i => !isNoopN P (chase P i nd)) hk'
  have hm' : isNoopN P (chase P m nd) = false := by
    cases hb : isNoopN P (chase P m nd) with
    | false => rfl
    | true => rw [hb] at hm; simp at hm
  have hpre' : ∀ i, i < m → isNoopN P (chase P i nd) = true := by
    intro i hi
    have hp := hpre i hi
    cases hb : isNoopN P (chase P i nd) with
    | true => rfl
    | false => rw [hb] at hp; simp at hp
  have hmlt : m < P.size := noopPrefix_bound wf hnd hpre' hm'
  have hstab : chase P P.size nd = chase P m nd := by
    have h1 : P.size = m + (P.size - m) := (Nat.add_sub_cancel' (Nat.le_of_lt hmlt)).symm
    rw [h1]; exact chase_stabilizes (not_noop_of_isNoopN_false hm')
  rw [hstab]; exact hm'

/-- Contrapositive: if `chase P.size` is a `noop`, every `chase k` is (a cycle — never escapes). -/
theorem isNoopN_chase_all (wf : WellFormed P) {nd : Node} (hnd : nd < P.size)
    (hsize : isNoopN P (chase P P.size nd) = true) (k : Node) :
    isNoopN P (chase P k nd) = true := by
  cases hb : isNoopN P (chase P k nd) with
  | true => rfl
  | false =>
      have := isNoopN_chase_size wf hnd hb
      rw [this] at hsize; simp at hsize

/-- **`resolve nd` is never droppable** — it is a non-`noop`, or a `noop` on a cycle (which stays a
    `noop` under `resolve`). This is what makes compaction well-formed. -/
theorem not_droppable_resolve (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) :
    droppable P (resolve P nd) = false := by
  unfold droppable
  cases hf : P.fetch (resolve P nd) with
  | none => rfl
  | some c => cases c with
    | assign x e nx => rfl
    | ifz x z nz => rfl
    | halt => rfl
    | noop nx =>
        have h2 : isNoopN P (chase P P.size nd) = true := by
          show isNoopN P (resolve P nd) = true
          unfold isNoopN; rw [hf]
        have hall := isNoopN_chase_all wf hnd h2
        have h3 : resolve P (resolve P nd) = chase P (P.size + P.size) nd := by
          show chase P P.size (resolve P nd) = chase P (P.size + P.size) nd
          rw [chase_add]; rfl
        have h4 : isNoopN P (resolve P (resolve P nd)) = true := by rw [h3]; exact hall _
        cases hf2 : P.fetch (resolve P (resolve P nd)) with
        | some c2 => cases c2 with
          | noop m => rfl
          | assign x e nx => simp [isNoopN, hf2] at h4
          | ifz x z nz => simp [isNoopN, hf2] at h4
          | halt => simp [isNoopN, hf2] at h4
        | none => simp [isNoopN, hf2] at h4

/-- **`resolve nd` is a kept node.** (Discharges the well-formedness obligation for compaction.) -/
theorem resolve_kept (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) :
    resolve P nd ∈ keptList P :=
  Compact.mem_keptList.mpr ⟨resolve_lt wf hnd, by simp [cleanKeep, not_droppable_resolve wf hnd]⟩

/-! ## `cleanup` is well-formed. -/

theorem keptList_lt {nd : Node} (h : nd ∈ keptList P) : nd < P.size := Compact.keptList_lt h

/-- A remapped node is a valid index into the compacted program. -/
theorem remap_lt (wf : WellFormed P) {nd : Node} (h : nd < P.size) :
    remap P (keptList P) nd < (keptList P).length :=
  Compact.remap_lt (resolve_kept wf h)

/-- The compacted program fetches the remapped instruction of the `n`-th kept node. -/
theorem cleanup_fetch {n : Node} (h : n < (keptList P).length) :
    (cleanup P).fetch n
      = some (remapCmd P (keptList P) ((P.fetch ((keptList P)[n]'h)).getD .halt)) :=
  Compact.compactBy_fetch h

/-- Well-formedness is the shared `Compact.compactBy_wellFormed`, via the resolve interface: the entry and
    every kept node's successors all `resolve` to kept nodes. -/
theorem cleanup_wellFormed (wf : WellFormed P) : WellFormed (cleanup P) :=
  Compact.compactBy_wellFormed
    { entry_rep_kept := resolve_kept wf wf.entry_lt,
      succ_rep_kept  := fun _ hf hs => resolve_kept wf (wf.succ_lt hf hs) }

/-! ## On a halting run, no node resolves into a `noop` cycle. -/

theorem isNoopN_true_fetch {nd : Node} (h : isNoopN P nd = true) :
    ∃ m, P.fetch nd = some (.noop m) := by
  unfold isNoopN at h
  split at h
  · next m hf => exact ⟨m, hf⟩
  · next => simp at h

/-- If every `chase` step from `nd` is a `noop`, any run from `nd` stays on the (all-`noop`) trajectory. -/
theorem noop_steps_stay {nd : Node} {σ : Store} {d : Config}
    (hall : ∀ k, isNoopN P (chase P k nd) = true) (h : Steps P ⟨nd, σ⟩ d) :
    ∃ k, d.node = chase P k nd ∧ d.store = σ := by
  induction h with
  | refl => exact ⟨0, rfl, rfl⟩
  | tail hs hstep ih =>
      obtain ⟨k, hnode, hstore⟩ := ih
      obtain ⟨m, hfm⟩ := isNoopN_true_fetch (hall k)
      have hstep1 := step1_next_iff.mpr hstep
      simp only [step1, hnode, hfm] at hstep1
      have hd := Status.next.inj hstep1
      refine ⟨k + 1, ?_, ?_⟩
      · rw [← hd]; show m = chase P (k + 1) nd; rw [chase_add]; simp only [chase, hfm]
      · rw [← hd]; exact hstore

/-- **A node on a run that reaches a non-`noop` terminal resolves to a real (non-`noop`) node.** So the
    simulation never meets a `noop` cycle — a cycle diverges, never reaching a non-`noop`. -/
theorem resolve_real (wf : WellFormed P) {nd : Node} {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨nd, σ⟩ c_f) (hterm : isNoopN P c_f.node = false) (hnd : nd < P.size) :
    isNoopN P (resolve P nd) = false := by
  cases hb : isNoopN P (resolve P nd) with
  | false => rfl
  | true =>
      exfalso
      have hall := isNoopN_chase_all wf hnd hb
      obtain ⟨k, hnode, _⟩ := noop_steps_stay hall hrun
      rw [hnode, hall k] at hterm; simp at hterm

/-- `halt` and `assign` (Final / Faulting nodes) are non-`noop`. -/
theorem isNoopN_of_final {c : Config} (h : Final P c) : isNoopN P c.node = false := by
  have h' : P.fetch c.node = some .halt := h
  unfold isNoopN; rw [h']

theorem isNoopN_of_faulting {c : Config} (h : Faulting P c) : isNoopN P c.node = false := by
  obtain ⟨x, e, next, hf, _⟩ := h
  unfold isNoopN; rw [hf]

/-! ## Per-step simulation. -/

/-- The compacted node an original node maps to. -/
abbrev newNode (P : Program) (nd : Node) : Node := remap P (keptList P) nd

/-- The kept node at slot `remap nd` is `resolve nd`. -/
theorem getElem_remap (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) :
    (keptList P)[remap P (keptList P) nd]'(remap_lt wf hnd) = resolve P nd :=
  Compact.getElem_remap (resolve_kept wf hnd)

/-- The compacted program fetches the *resolved* node's remapped instruction. -/
theorem cleaned_fetch (wf : WellFormed P) {nd : Node} (hnd : nd < P.size) {c : Cmd}
    (hc : P.fetch (resolve P nd) = some c) :
    (cleanup P).fetch (newNode P nd) = some (remapCmd P (keptList P) c) :=
  Compact.compacted_fetch (resolve_kept wf hnd) hc

/-- A non-`noop` node resolves to itself. -/
theorem resolve_self {nd : Node} (h : ∀ m, P.fetch nd ≠ some (.noop m)) : resolve P nd = nd :=
  chase_stuck h

/-- **Per-step forward simulation** (identity store relation): one original step is matched by
    0-or-1 compacted steps to the remapped node. Needs `resolve nd` real (holds on a halting run). -/
theorem cleanup_step_sim (wf : WellFormed P) {nd nd' : Node} {σ σ' : Store}
    (hstep : Step P ⟨nd, σ⟩ ⟨nd', σ'⟩) (hreal : isNoopN P (resolve P nd) = false) (hnd : nd < P.size) :
    Steps (cleanup P) ⟨newNode P nd, σ⟩ ⟨newNode P nd', σ'⟩ := by
  cases hstep with
  | @assign _ _ x e _ v hf hv =>
      have hrn : resolve P nd = nd := resolve_self (fun m => by rw [hf]; simp)
      have hcf : (cleanup P).fetch (newNode P nd) = some (.assign x e (remap P (keptList P) nd')) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .assign x e nd') (by rw [hrn]; exact hf)
      exact oneStep (Step.assign hcf hv)
  | @ifzT _ _ x _ nz hf hz =>
      have hrn : resolve P nd = nd := resolve_self (fun m => by rw [hf]; simp)
      have hcf : (cleanup P).fetch (newNode P nd)
          = some (.ifz x (remap P (keptList P) nd') (remap P (keptList P) nz)) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .ifz x nd' nz) (by rw [hrn]; exact hf)
      exact oneStep (Step.ifzT hcf hz)
  | @ifzF _ _ x z _ hf hz =>
      have hrn : resolve P nd = nd := resolve_self (fun m => by rw [hf]; simp)
      have hcf : (cleanup P).fetch (newNode P nd)
          = some (.ifz x (remap P (keptList P) z) (remap P (keptList P) nd')) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .ifz x z nd') (by rw [hrn]; exact hf)
      exact oneStep (Step.ifzF hcf hz)
  | noop hf =>
      have hc1 : chase P 1 nd = nd' := by simp only [chase, hf]
      have hrn : resolve P nd' = resolve P nd := by
        show chase P P.size nd' = chase P P.size nd
        rw [← hc1, ← chase_add, Nat.add_comm 1 P.size]
        exact chase_stabilizes (not_noop_of_isNoopN_false hreal)
      have he : newNode P nd = newNode P nd' := by simp only [newNode, remap, Compact.remap, hrn]
      rw [he]; exact Steps.refl

/-! ## Lift the per-step simulation over a halting run. -/

/-- Head-structured counted steps (peels the *first* step). -/
def StepsN (P : Program) : Config → Config → Nat → Prop
  | c, c', 0     => c = c'
  | c, c', n + 1 => ∃ c'', Step P c c'' ∧ StepsN P c'' c' n

theorem stepsN_to_steps {n : Nat} {c cf : Config} (h : StepsN P c cf n) : Steps P c cf := by
  induction n generalizing c with
  | zero => simp only [StepsN] at h; exact h ▸ Steps.refl
  | succ n ih => obtain ⟨c'', hstep, hrest⟩ := h; exact steps_trans (oneStep hstep) (ih hrest)

theorem stepsN_tail {n : Nat} {a b c : Config} (h : StepsN P a b n) (hs : Step P b c) :
    StepsN P a c (n + 1) := by
  induction n generalizing a with
  | zero => simp only [StepsN] at h; subst h; exact ⟨c, hs, rfl⟩
  | succ n ih => obtain ⟨a'', hstep, hrest⟩ := h; exact ⟨a'', hstep, ih hrest⟩

theorem steps_to_stepsN {c cf : Config} (h : Steps P c cf) : ∃ n, StepsN P c cf n := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail hab hbc ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, stepsN_tail hn hbc⟩

/-- **The compacted program simulates a run to any non-`noop` terminal.** -/
theorem cleanup_sim (wf : WellFormed P) {cf : Config} (hterm : isNoopN P cf.node = false) :
    ∀ {n : Nat} {c : Config}, StepsN P c cf n → c.node < P.size →
      Steps (cleanup P) ⟨newNode P c.node, c.store⟩ ⟨newNode P cf.node, cf.store⟩ := by
  intro n
  induction n with
  | zero => intro c h _; simp only [StepsN] at h; subst h; exact Steps.refl
  | succ n ih =>
      intro c h hnd
      obtain ⟨c'', hstep, hrest⟩ := h
      have hrun : Steps P c cf := steps_trans (oneStep hstep) (stepsN_to_steps hrest)
      have hreal : isNoopN P (resolve P c.node) = false := resolve_real wf hrun hterm hnd
      exact steps_trans (cleanup_step_sim wf hstep hreal hnd) (ih hrest (step_in_range wf hstep))

/-- **Cleanup preserves halting** — same observables (PDCE `transform_preserves_halt` shape). -/
theorem cleanup_preserves_halt (wf : WellFormed P) {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (cleanup P) ⟨(cleanup P).entry, σ⟩ d_f ∧ Final (cleanup P) d_f ∧
           ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  obtain ⟨n, hn⟩ := steps_to_stepsN hrun
  have hsim := cleanup_sim wf (isNoopN_of_final hfin) hn wf.entry_lt
  refine ⟨⟨newNode P c_f.node, c_f.store⟩, ?_, ?_, fun v _ => rfl⟩
  · rw [show (cleanup P).entry = newNode P P.entry from cleanup_entry P]; exact hsim
  · have hcn : c_f.node < P.size := fetch_lt hfin
    have hrn : resolve P c_f.node = c_f.node := resolve_self (fun m => by rw [hfin]; simp)
    show (cleanup P).fetch (newNode P c_f.node) = some .halt
    simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hcn (c := .halt) (by rw [hrn]; exact hfin)

/-- **Cleanup preserves faulting** — if `P` faults (div/mod by zero), so does the compacted program.
    The faulting `assign`'s expression is carried through unchanged (only its successor is remapped),
    and the store is identical, so the same `eval … = none` fault occurs. -/
theorem cleanup_preserves_faults (wf : WellFormed P) {σ : Store} {c_f : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfault : Faulting P c_f) :
    ∃ d_f, Steps (cleanup P) ⟨(cleanup P).entry, σ⟩ d_f ∧ Faulting (cleanup P) d_f := by
  obtain ⟨n, hn⟩ := steps_to_stepsN hrun
  have hsim := cleanup_sim wf (isNoopN_of_faulting hfault) hn wf.entry_lt
  refine ⟨⟨newNode P c_f.node, c_f.store⟩, ?_, ?_⟩
  · rw [show (cleanup P).entry = newNode P P.entry from cleanup_entry P]; exact hsim
  · obtain ⟨x, e, next, hf, hev⟩ := hfault
    have hcn : c_f.node < P.size := fetch_lt hf
    have hrn : resolve P c_f.node = c_f.node := resolve_self (fun m => by rw [hf]; simp)
    refine ⟨x, e, remap P (keptList P) next, ?_, hev⟩
    show (cleanup P).fetch (newNode P c_f.node) = some (.assign x e (remap P (keptList P) next))
    simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hcn (c := .assign x e next) (by rw [hrn]; exact hf)

/-! ## Divergence preservation. -/

/-- Divergence is preserved along a finite forward path (`Step` is deterministic). -/
theorem diverges_of_steps_fwd {c c' : Config} (hd : Diverges P c) (hs : Steps P c c') :
    Diverges P c' := by
  induction hs with
  | refl => exact hd
  | tail _ hstep ih =>
      obtain ⟨d, hstepd, hdivd⟩ := diverges_step ih
      rw [Step.deterministic hstep hstepd]; exact hdivd

/-- **One compacted step preserving divergence.** From a diverging `⟨nd, σ⟩`, the compacted machine
    steps to `⟨newNode nd', σ'⟩` with `⟨nd', σ'⟩` still diverging — the machine runs `resolve nd`'s
    instruction (a real op, or a step around a kept `noop` cycle), always advancing exactly one step. -/
theorem cleanup_div_step (wf : WellFormed P) {nd : Node} {σ : Store}
    (hdiv : Diverges P ⟨nd, σ⟩) (hnd : nd < P.size) :
    ∃ nd' σ', step1 (cleanup P) ⟨newNode P nd, σ⟩ = .next ⟨newNode P nd', σ'⟩
            ∧ Diverges P ⟨nd', σ'⟩ ∧ nd' < P.size := by
  have hdivR : Diverges P ⟨resolve P nd, σ⟩ := diverges_of_steps_fwd hdiv resolve_steps
  obtain ⟨cnext, hstepR, hdivnext⟩ := diverges_step hdivR
  cases hstepR with
  | @assign _ _ x e next v hf hv =>
      refine ⟨next, σ.update x v, ?_, hdivnext, wf.succ_lt hf (by simp [Cmd.succs])⟩
      have hcf : (cleanup P).fetch (newNode P nd) = some (.assign x e (remap P (keptList P) next)) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .assign x e next) hf
      exact step1_next_iff.mpr (Step.assign hcf hv)
  | @ifzT _ _ x z nz hf hz =>
      refine ⟨z, σ, ?_, hdivnext, wf.succ_lt hf (by simp [Cmd.succs])⟩
      have hcf : (cleanup P).fetch (newNode P nd)
          = some (.ifz x (remap P (keptList P) z) (remap P (keptList P) nz)) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .ifz x z nz) hf
      exact step1_next_iff.mpr (Step.ifzT hcf hz)
  | @ifzF _ _ x z nz hf hz =>
      refine ⟨nz, σ, ?_, hdivnext, wf.succ_lt hf (by simp [Cmd.succs])⟩
      have hcf : (cleanup P).fetch (newNode P nd)
          = some (.ifz x (remap P (keptList P) z) (remap P (keptList P) nz)) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .ifz x z nz) hf
      exact step1_next_iff.mpr (Step.ifzF hcf hz)
  | @noop _ _ m hf =>
      refine ⟨m, σ, ?_, hdivnext, wf.succ_lt hf (by simp [Cmd.succs])⟩
      have hcf : (cleanup P).fetch (newNode P nd) = some (.noop (remap P (keptList P) m)) := by
        simpa only [remapCmd, Compact.remapCmd, remap] using cleaned_fetch wf hnd (c := .noop m) hf
      exact step1_next_iff.mpr (Step.noop hcf)

theorem cleanup_runsFor (wf : WellFormed P) :
    ∀ (n : Nat) {nd : Node} {σ : Store}, Diverges P ⟨nd, σ⟩ → nd < P.size →
      RunsFor (cleanup P) ⟨newNode P nd, σ⟩ n := by
  intro n
  induction n with
  | zero => intro _ _ _ _; exact ⟨_, rfl⟩
  | succ n ih =>
      intro nd σ hdiv hnd
      obtain ⟨nd', σ', hstep1, hdiv', hnd'⟩ := cleanup_div_step wf hdiv hnd
      exact runsFor_step hstep1 (ih hdiv' hnd')

/-- **Cleanup preserves divergence** — if `P` runs forever, so does the compacted program. -/
theorem cleanup_preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (cleanup P) ⟨(cleanup P).entry, σ⟩ := by
  rw [show (cleanup P).entry = newNode P P.entry from cleanup_entry P]
  exact diverges_of_runsFor (fun n => cleanup_runsFor wf n hdiv wf.entry_lt)

/-- **End-to-end codegen correctness of the cleanup pass.** If `P` halts at `c_f`, the assembly
    generated from `cleanup P` halts with the source's observable values — so cleanup is a verified
    codegen-preserving pass, composable before `TacToAsm.codegen`. -/
theorem cleanup_codegen (wf : WellFormed P) {c_f : Config}
    (hrun : Steps P ⟨P.entry, Store.init⟩ c_f) (hfin : Final P c_f) :
    ∃ fuel sf, Asm.run (TacToAsm.codegen (cleanup P)) fuel (TacToAsm.initState (cleanup P) Store.init)
                 = .halted sf
             ∧ ∀ v ∈ P.obs,
                 sf.mem (TacToAsm.slot (TacToAsm.collectVars (cleanup P)) v) = TacToAsm.encode (c_f.store v) := by
  obtain ⟨d_f, hsteps, hfin', hobs⟩ := cleanup_preserves_halt wf hrun hfin
  obtain ⟨fuel, sf, hrun', hmem⟩ := TacToAsm.codegen_simulates hsteps hfin'
  exact ⟨fuel, sf, hrun', fun v hv => by rw [hmem v, hobs v hv]⟩

end Cleanup
end Pass
end BaseLanguage
