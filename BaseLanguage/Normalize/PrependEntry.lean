-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Constraints

/-!
# `Normalize.PrependEntry` — the fresh-entry pre-pass

Prepends a brand-new entry node — a `noop P.entry` at index `P.size`, made the new entry. The result
has a **fresh entry** (`EntryNoIncoming`: the successor of no node) that **reads nothing**
(`EntryUnused`), and the pass preserves `WellFormed`/`DistinctSuccs`/`NoSelfRead`/`AllReachable`.
Structural facts only; dataflow-free.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

variable {P : Program}

/-- **The fresh-entry pre-pass.** Append a `noop P.entry` at index `P.size` and make it the entry. -/
def prependEntry (P : Program) : Program where
  entry := P.size
  code  := P.code ++ #[Cmd.noop P.entry]
  obs   := P.obs

@[simp] theorem prependEntry_entry (P : Program) : (prependEntry P).entry = P.size := rfl

@[simp] theorem prependEntry_size (P : Program) : (prependEntry P).size = P.size + 1 := by
  show (P.code ++ #[Cmd.noop P.entry]).size = P.size + 1
  simp [Program.size]

@[simp] theorem prependEntry_obs (P : Program) : (prependEntry P).obs = P.obs := rfl

/-- The original prefix verbatim, the new `noop` at `P.size`. -/
theorem prependEntry_fetch (P : Program) (n : Node) :
    (prependEntry P).fetch n =
      if n < P.size then P.fetch n
      else if n = P.size then some (.noop P.entry) else none := by
  show (P.code ++ #[Cmd.noop P.entry])[n]? = _
  by_cases h1 : n < P.size
  · rw [Array.getElem?_append_left h1]; simp [h1, Program.fetch]
  · rw [Array.getElem?_append_right (Nat.le_of_not_lt h1)]
    by_cases h2 : n = P.size
    · subst h2; simp [Program.size]
    · have hk : n - P.code.size ≠ 0 := by
        have hlt' : P.size < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) (Ne.symm h2)
        exact Nat.sub_ne_zero_of_lt hlt'
      simp only [if_neg h1, if_neg h2]
      rcases Nat.exists_eq_succ_of_ne_zero hk with ⟨k, hk'⟩
      show (#[Cmd.noop P.entry])[n - P.code.size]? = none
      rw [hk']; rfl

theorem prependEntry_fetch_lt {n : Node} (h : n < P.size) :
    (prependEntry P).fetch n = P.fetch n := by rw [prependEntry_fetch]; simp [h]

theorem prependEntry_fetch_size (P : Program) :
    (prependEntry P).fetch P.size = some (.noop P.entry) := by
  rw [prependEntry_fetch]; simp

/-- Successors agree on the original region. -/
theorem prependEntry_succList_lt {m : Node} (h : m < P.size) :
    succList (prependEntry P) m = succList P m := by
  unfold succList; rw [prependEntry_fetch_lt h]

/-- Successors of `prependEntry P` land in the **original** range `< P.size`. -/
theorem prependEntry_succ_lt_old (hwf : WellFormed P) {m : Node} {instr : Cmd} {s : Node}
    (hf : (prependEntry P).fetch m = some instr) (hs : s ∈ instr.succs) : s < P.size := by
  have hmlt : m < P.size + 1 := by
    rw [← prependEntry_size]; exact fetch_some_iff_lt.mp ⟨instr, hf⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hmlt with hlt | heq
  · rw [prependEntry_fetch_lt hlt] at hf; exact hwf.succ_lt hf hs
  · subst heq; rw [prependEntry_fetch_size] at hf
    injection hf with hf; subst hf
    simp only [Cmd.succs, List.mem_singleton] at hs; subst hs; exact hwf.entry_lt

/-! ## Establishing + preserving the normal-form fields -/

/-- **EntryNoIncoming.** The entry of `prependEntry P` is the successor of no node. -/
theorem prependEntry_freshEntry (hwf : WellFormed P) : EntryNoIncoming (prependEntry P) := by
  intro m hmem
  rw [prependEntry_entry] at hmem
  obtain ⟨instr, hf, hsi⟩ := mem_succList hmem
  exact absurd (prependEntry_succ_lt_old hwf hf hsi) (Nat.lt_irrefl _)

/-- **EntryUnused.** The fresh entry carries a `noop`, which reads nothing. Independent of `P`. -/
theorem prependEntry_entryUnused (P : Program) : EntryUnused (prependEntry P) := by
  intro instr hf
  rw [prependEntry_entry, prependEntry_fetch_size] at hf
  injection hf with hf; subst hf
  rfl

theorem prependEntry_wellFormed (hwf : WellFormed P) : WellFormed (prependEntry P) where
  entry_lt := by rw [prependEntry_entry, prependEntry_size]; exact Nat.lt_succ_self _
  succ_lt := by
    intro n instr s hf hs
    rw [prependEntry_size]; exact Nat.lt_succ_of_lt (prependEntry_succ_lt_old hwf hf hs)

theorem prependEntry_distinctSuccs (hsd : DistinctSuccs P) : DistinctSuccs (prependEntry P) := by
  intro nd
  by_cases h1 : nd < P.size
  · rw [prependEntry_succList_lt h1]; exact hsd nd
  · by_cases h2 : nd = P.size
    · subst h2; unfold succList; rw [prependEntry_fetch_size]; simp [Cmd.succs]
    · unfold succList; rw [prependEntry_fetch]
      simp only [if_neg h1, if_neg h2, Option.elim, List.nodup_nil]

theorem prependEntry_noSelfRead (hns : NoSelfRead P) : NoSelfRead (prependEntry P) := by
  intro nd x e next hf hnum
  rw [prependEntry_fetch] at hf
  by_cases h1 : nd < P.size
  · rw [if_pos h1] at hf; exact hns hf hnum
  · rw [if_neg h1] at hf
    by_cases h2 : nd = P.size
    · rw [if_pos h2] at hf; simp at hf
    · rw [if_neg h2] at hf; simp at hf

/-- `FReach` transfers from `P` into `prependEntry P` (via the new entry edge `P.size → P.entry`). -/
theorem prependEntry_freach (hwf : WellFormed P) {nd : Node} (hr : FReach P nd) :
    FReach (prependEntry P) nd := by
  induction hr with
  | entry =>
      apply FReach.step (p := P.size) FReach.entry
      unfold succList; rw [prependEntry_fetch_size]; simp [Cmd.succs]
  | @step p nd hp hs ih =>
      have hplt : p < P.size := FReach_lt hwf hp
      exact FReach.step ih (by rw [prependEntry_succList_lt hplt]; exact hs)

theorem prependEntry_allReach (hwf : WellFormed P) (hr : AllReachable P) :
    AllReachable (prependEntry P) := by
  intro nd hnd
  rw [prependEntry_size] at hnd
  rcases Nat.lt_succ_iff_lt_or_eq.mp hnd with hlt | heq
  · exact prependEntry_freach hwf (hr nd hlt)
  · subst heq; rw [← prependEntry_entry]; exact FReach.entry

end Normalize
end BaseLanguage
