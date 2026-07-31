-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import Std.Data.HashSet

/-!
# `Analysis.Solver.Fold` — generic `union`-fold contribution.

The two analysis-agnostic facts behind every "gen/kill family ⊆ universe" obligation, over a `union`-fold
`l.foldl (fun acc n => acc.union (f n)) init`: the fold's `init` survives it (`foldl_union_infl`), and so
does any contributor `f k` for `k ∈ l` (`foldl_union_contrib`). Stated over an abstract set `S` with its
membership and `union`, so it instantiates at `Variables`/`Assignments` alike. The generator emits the
per-family `_sub` proofs as thin instances — for bare-fold universes (LCM `allExprs`) and seeded
`seed ∪ ⋃…` ones (PDCE `allVars`) alike — nothing analysis-specific is hand-written.
-/

namespace BaseLanguage.IR.SetFold
open BaseLanguage Tac

variable {α S : Type} (mem : α → S → Prop) (u : S → S → S)
  (mem_u : ∀ (a b : S) (x : α), mem x (u a b) ↔ mem x a ∨ mem x b)

include mem_u

/-- Inflation: seed elements survive a `union`-fold. -/
theorem foldl_union_infl (f : Node → S) :
    ∀ (l : List Node) (init : S) {x}, mem x init →
      mem x (l.foldl (fun acc n => u acc (f n)) init) := by
  intro l
  induction l with
  | nil => intro init x hx; simpa using hx
  | cons y ys ih =>
      intro init x hx
      simp only [List.foldl_cons]
      exact ih _ ((mem_u _ _ _).mpr (Or.inl hx))

/-- Contribution: `f k` for any `k` in the list survives the fold. -/
theorem foldl_union_contrib (f : Node → S) :
    ∀ (l : List Node) (init : S) {k}, k ∈ l → ∀ {x}, mem x (f k) →
      mem x (l.foldl (fun acc n => u acc (f n)) init) := by
  intro l
  induction l with
  | nil => intro init k hk; simp at hk
  | cons y ys ih =>
      intro init k hk x hx
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hk with h | h
      · subst h; exact foldl_union_infl mem u mem_u f ys _ ((mem_u _ _ _).mpr (Or.inr hx))
      · exact ih _ h hx

end BaseLanguage.IR.SetFold
