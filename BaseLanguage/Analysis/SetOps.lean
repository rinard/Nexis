-- Copyright (c) 2026 Martin Rinard
import Std.Data.HashSet
import BaseLanguage.IR.Hashable

/-! # `Analysis.SetOps` — the generic `HashSet` set-algebra lemmas

The LCM and PDCE analysis domains (`Analyses.LCM.Assignments`, `Analyses.PDCE.{Assignments,Variables}`) are all
`HashSet α` for some `DecidableEq`/`Hashable` element type, with the same membership/monotonicity algebra.
The *operations* stay defined per-domain (their exact definitional unfolding is relied on by `simp`/`unfold`
throughout the proofs, and dot-notation resolves on the domain name), but the *lemma proofs* are shared
here once and each domain's lemmas delegate to them. -/

namespace BaseLanguage.Analysis.SetOps

open Std
set_option linter.unusedSectionVars false

variable {α : Type _} [BEq α] [Hashable α] [LawfulBEq α]

/-- Generic subset predicate: every element of `a` is in `b`. -/
def Subset (a b : HashSet α) : Prop := ∀ x ∈ a, x ∈ b

@[refl] theorem subset_refl {a : HashSet α} : Subset a a := fun _ h => h
theorem subset_trans {a b c : HashSet α} (h1 : Subset a b) (h2 : Subset b c) : Subset a c :=
  fun x hx => h2 x (h1 x hx)

theorem mem_union {a b : HashSet α} {x : α} : x ∈ HashSet.union a b ↔ x ∈ a ∨ x ∈ b :=
  Std.HashSet.mem_union_iff

theorem mem_filter' {m : HashSet α} {f : α → Bool} {x : α} :
    x ∈ m.filter f ↔ x ∈ m ∧ f x = true := by
  rw [Std.HashSet.mem_filter]
  exact ⟨fun ⟨h, hf⟩ => ⟨h, by rwa [Std.HashSet.get_eq h] at hf⟩,
         fun ⟨h, hf⟩ => ⟨h, by rwa [Std.HashSet.get_eq h]⟩⟩

theorem mem_inter {a b : HashSet α} {x : α} :
    x ∈ a.filter (fun y => b.contains y) ↔ x ∈ a ∧ x ∈ b := by
  rw [mem_filter', Std.HashSet.contains_iff_mem]

theorem mem_sdiff {a b : HashSet α} {x : α} :
    x ∈ a.filter (fun y => !b.contains y) ↔ x ∈ a ∧ x ∉ b := by
  rw [mem_filter', Bool.not_eq_true', Std.HashSet.contains_eq_false_iff_not_mem]

theorem union_subset_union {a a' b b' : HashSet α} (h1 : Subset a a') (h2 : Subset b b') :
    Subset (HashSet.union a b) (HashSet.union a' b') := by
  intro x hx; rw [mem_union] at hx ⊢; exact hx.imp (h1 x) (h2 x)

theorem inter_subset_inter {a a' b b' : HashSet α} (h1 : Subset a a') (h2 : Subset b b') :
    Subset (a.filter (fun y => b.contains y)) (a'.filter (fun y => b'.contains y)) := by
  intro x hx; rw [mem_inter] at hx ⊢; exact ⟨h1 x hx.1, h2 x hx.2⟩

theorem sdiff_subset_sdiff {a a' b : HashSet α} (h : Subset a a') :
    Subset (a.filter (fun y => !b.contains y)) (a'.filter (fun y => !b.contains y)) := by
  intro x hx; rw [mem_sdiff] at hx ⊢; exact ⟨h x hx.1, hx.2⟩

theorem mem_singleton {x y : α} : x ∈ (∅ : HashSet α).insert y ↔ x = y := by
  rw [Std.HashSet.mem_insert]
  constructor
  · rintro (h | h)
    · exact (eq_of_beq h).symm
    · exact absurd h Std.HashSet.not_mem_empty
  · rintro rfl; exact Or.inl (beq_self_eq_true _)

theorem mem_ofList {l : List α} {x : α} :
    x ∈ l.foldl (fun acc y => acc.insert y) (∅ : HashSet α) ↔ x ∈ l := by
  have gen : ∀ s : HashSet α, x ∈ l.foldl (fun acc y => acc.insert y) s ↔ x ∈ s ∨ x ∈ l := by
    induction l with
    | nil => intro s; simp
    | cons a as ih =>
        intro s
        rw [List.foldl_cons, ih (s.insert a), Std.HashSet.mem_insert, List.mem_cons]
        constructor
        · rintro ((h | h) | h)
          · exact Or.inr (Or.inl (eq_of_beq h).symm)
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
        · rintro (h | (rfl | h))
          · exact Or.inl (Or.inr h)
          · exact Or.inl (Or.inl (beq_self_eq_true _))
          · exact Or.inr h
  rw [gen ∅]; simp [Std.HashSet.not_mem_empty]

end BaseLanguage.Analysis.SetOps
