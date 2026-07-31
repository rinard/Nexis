-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Cfg

/-!
# `Pass.ReachBFS` — a graph BFS deciding forward reachability (`FReach`)

A plain successor-list traversal: the nodes forward-reachable from the entry, computed as the
`P.size`-round closure of `[entry]` under `succList` (a fixpoint by then — the reachability diameter is
below `P.size`). This is an **isolated graph algorithm**: no dataflow lattice, no analysis domain, no MTC
solver — just `succList`, dedup, and the `FReach` inductive. Its whole contract is
`mem_reachList_iff_FReach`: membership in `reachList` decides `FReach` exactly. From that, the abstract
`UCE.ReachSpec` obligations (`entry` / `closed` / `sound`) are one-liners, so UCE consumes reachability
via a BFS instead of the ancestor-set dataflow solve.
-/
namespace BaseLanguage
namespace Pass
namespace ReachBFS
open Tac

variable {P : Program}

/-- `List.eraseDups` produces a `Nodup` list (core has `mem_eraseDups` but not this). -/
private theorem eraseDups_nodup {α} [BEq α] [LawfulBEq α] : (l : List α) → l.eraseDups.Nodup
  | []      => by simp
  | a :: as => by
      rw [List.eraseDups_cons, List.nodup_cons]
      refine ⟨?_, eraseDups_nodup (as.filter fun b => !b == a)⟩
      rw [List.mem_eraseDups, List.mem_filter]
      rintro ⟨-, hne⟩; simp at hne
  termination_by l => l.length
  decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- One BFS round: the current set plus every `succList` successor of a current node, deduplicated. -/
def bfsRound (P : Program) (s : List Node) : List Node := (s ++ s.flatMap (succList P)).eraseDups

theorem mem_bfsRound {s : List Node} {x : Node} :
    x ∈ bfsRound P s ↔ x ∈ s ∨ ∃ p ∈ s, x ∈ succList P p := by
  unfold bfsRound; rw [List.mem_eraseDups, List.mem_append, List.mem_flatMap]

theorem bfsRound_nodup (s : List Node) : (bfsRound P s).Nodup := eraseDups_nodup _

theorem subset_bfsRound {s : List Node} : s ⊆ bfsRound P s :=
  fun _ hx => mem_bfsRound.mpr (Or.inl hx)

/-- `bfsRound` depends only on the membership of its argument. -/
theorem bfsRound_congr {s t : List Node} (h : ∀ x, x ∈ s ↔ x ∈ t) (x : Node) :
    x ∈ bfsRound P s ↔ x ∈ bfsRound P t := by
  simp only [mem_bfsRound]
  constructor <;> rintro (hx | ⟨p, hp, hs⟩)
  · exact Or.inl ((h x).mp hx)
  · exact Or.inr ⟨p, (h p).mp hp, hs⟩
  · exact Or.inl ((h x).mpr hx)
  · exact Or.inr ⟨p, (h p).mpr hp, hs⟩

/-- The reachable list after `k` BFS rounds from `[entry]`. -/
def reachIter (P : Program) : Nat → List Node
  | 0     => [P.entry]
  | k + 1 => bfsRound P (reachIter P k)

/-- The reachable set: `P.size` rounds (a fixpoint by then). -/
def reachList (P : Program) : List Node := reachIter P P.size

theorem reachIter_nodup : ∀ k, (reachIter P k).Nodup
  | 0     => by simp [reachIter]
  | _ + 1 => bfsRound_nodup _

theorem reachIter_mono {k : Nat} : reachIter P k ⊆ reachIter P (k + 1) := subset_bfsRound

/-- Soundness invariant: every element of every round is forward-reachable. -/
theorem reachIter_FReach : ∀ k, ∀ x ∈ reachIter P k, FReach P x
  | 0     => by intro x hx; simp only [reachIter, List.mem_singleton] at hx; exact hx ▸ FReach.entry
  | k + 1 => by
      intro x hx
      rw [reachIter, mem_bfsRound] at hx
      rcases hx with hx | ⟨p, hp, hs⟩
      · exact reachIter_FReach k x hx
      · exact FReach.step (reachIter_FReach k p hp) hs

theorem reachList_FReach {x : Node} (hx : x ∈ reachList P) : FReach P x :=
  reachIter_FReach P.size x hx

theorem entry_mem_reachIter : ∀ k, P.entry ∈ reachIter P k
  | 0     => by simp [reachIter]
  | k + 1 => reachIter_mono (entry_mem_reachIter k)

theorem entry_mem_reachList : P.entry ∈ reachList P := entry_mem_reachIter P.size

theorem reachIter_lt (wf : WellFormed P) {k : Nat} {x : Node} (hx : x ∈ reachIter P k) : x < P.size :=
  FReach_lt wf (reachIter_FReach k x hx)

theorem reachIter_len (wf : WellFormed P) (k : Nat) : (reachIter P k).length ≤ P.size := by
  have hsub : reachIter P k ⊆ List.range P.size :=
    fun x hx => List.mem_range.mpr (reachIter_lt wf hx)
  calc (reachIter P k).length
      ≤ (List.range P.size).length := nodup_length_le_of_subset' (reachIter_nodup k) hsub
    _ = P.size := List.length_range

/-- An equal-length superset of a `Nodup` list is contained in it (⇒ same elements). -/
theorem superset_of_len {a b : List Node} (hnda : a.Nodup) (hsub : a ⊆ b)
    (hlen : b.length ≤ a.length) : b ⊆ a := by
  intro x hxb
  apply Classical.byContradiction
  intro hxa
  have hae : a ⊆ b.erase x := by
    intro y hy
    have hyne : y ≠ x := by intro h; subst h; exact hxa hy
    exact (List.mem_erase_of_ne hyne).mpr (hsub hy)
  have h1 := nodup_length_le_of_subset' hnda hae
  have hb : 0 < b.length := List.length_pos_of_mem hxb
  rw [List.length_erase_of_mem hxb] at h1
  omega

/-- If a round does not grow the length, it is a membership-fixpoint (`s` is closed). -/
theorem stable_of_len_eq {k : Nat} (heq : (reachIter P (k + 1)).length ≤ (reachIter P k).length)
    (x : Node) : x ∈ reachIter P (k + 1) ↔ x ∈ reachIter P k :=
  ⟨fun hx => superset_of_len (reachIter_nodup k) reachIter_mono heq hx, fun hx => reachIter_mono hx⟩

/-- Once a round is a membership-fixpoint, every later round has the same members. -/
theorem members_const {k : Nat} (hfix : ∀ x, x ∈ reachIter P (k + 1) ↔ x ∈ reachIter P k) :
    ∀ j, ∀ x, x ∈ reachIter P (k + j) ↔ x ∈ reachIter P k
  | 0     => fun _ => Iff.rfl
  | j + 1 => by
      intro x
      have ih := members_const hfix j
      have e1 : reachIter P (k + (j + 1)) = bfsRound P (reachIter P (k + j)) := by
        rw [show k + (j + 1) = (k + j) + 1 from by omega]; rfl
      calc x ∈ reachIter P (k + (j + 1))
          ↔ x ∈ bfsRound P (reachIter P (k + j)) := by rw [e1]
        _ ↔ x ∈ bfsRound P (reachIter P k)       := bfsRound_congr ih x
        _ ↔ x ∈ reachIter P (k + 1)              := Iff.rfl
        _ ↔ x ∈ reachIter P k                    := hfix x

/-- Length strictly increases each round up to a fixpoint — bounded, so it stabilizes within `P.size`. -/
theorem len_ge_of_strict
    (hstrict : ∀ i < P.size, (reachIter P i).length < (reachIter P (i + 1)).length) :
    ∀ k ≤ P.size, k + 1 ≤ (reachIter P k).length := by
  intro k hk
  induction k with
  | zero => rw [reachIter]; simp
  | succ n ih =>
      have hn : n < P.size := Nat.lt_of_succ_le hk
      have h1 := ih (Nat.le_of_lt hn)
      have h2 := hstrict n hn
      omega

/-- **The BFS reaches a fixpoint by round `P.size`.** -/
theorem reachIter_fix (wf : WellFormed P) (x : Node) :
    x ∈ reachIter P (P.size + 1) ↔ x ∈ reachIter P P.size := by
  -- a round that does not grow exists within `P.size` (else the length would exceed `P.size`)
  have hstab : ∃ i, i ≤ P.size ∧ (reachIter P (i + 1)).length ≤ (reachIter P i).length := by
    apply Classical.byContradiction
    intro hcon
    have hstrict : ∀ i, i < P.size → (reachIter P i).length < (reachIter P (i + 1)).length := by
      intro i hi
      have hmono : (reachIter P i).length ≤ (reachIter P (i + 1)).length :=
        nodup_length_le_of_subset' (reachIter_nodup i) reachIter_mono
      have hnle : ¬ (reachIter P (i + 1)).length ≤ (reachIter P i).length :=
        fun hle => hcon ⟨i, Nat.le_of_lt hi, hle⟩
      omega
    have hge := len_ge_of_strict hstrict P.size (Nat.le_refl _)
    have hle := reachIter_len wf P.size
    omega
  obtain ⟨i, _, hnotlt⟩ := hstab
  have hconst := members_const (stable_of_len_eq hnotlt)
  have h1 : x ∈ reachIter P P.size ↔ x ∈ reachIter P i := by
    have := hconst (P.size - i) x; rwa [show i + (P.size - i) = P.size from by omega] at this
  have h2 : x ∈ reachIter P (P.size + 1) ↔ x ∈ reachIter P i := by
    have := hconst (P.size + 1 - i) x; rwa [show i + (P.size + 1 - i) = P.size + 1 from by omega] at this
  exact h2.trans h1.symm

/-- **`reachList` is closed under `succList`** (the `ReachSpec.closed` obligation). -/
theorem reachList_closed (wf : WellFormed P) {p nd : Node}
    (hp : p ∈ reachList P) (hs : nd ∈ succList P p) : nd ∈ reachList P := by
  have hnd : nd ∈ reachIter P (P.size + 1) := by
    rw [reachIter]; exact mem_bfsRound.mpr (Or.inr ⟨p, hp, hs⟩)
  exact (reachIter_fix wf nd).mp hnd

/-- **`reachList` decides `FReach`.** -/
theorem mem_reachList_iff_FReach (wf : WellFormed P) (n : Node) :
    n ∈ reachList P ↔ FReach P n := by
  refine ⟨reachList_FReach, fun h => ?_⟩
  induction h with
  | entry => exact entry_mem_reachList
  | step _ hs ih => exact reachList_closed wf ih hs

end ReachBFS
end Pass
end BaseLanguage
