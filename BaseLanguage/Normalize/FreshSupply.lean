-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Constraints

/-!
# `Normalize.FreshSupply` — a concrete disjoint fresh-temp supply

Builds an **offset** supply `freshN P i := .tmp (tmpBound P + i)` whose temp index is strictly above
every temp index occurring in `P`, and discharges `FreshForN P (freshN P)` and `Nonobs (freshN P)` for
**any** program — no `WellFormed`, no source restriction. Pure syntax + arithmetic (no analysis): the
companion to the per-pass `FreshForN` discipline a later optimization consumes.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

/-- A strict upper-bound contribution for one variable: `k+1` for `.tmp k`, `0` for an original. -/
def varTmpSucc : Var → Nat
  | .tmp k  => k + 1
  | .orig _ => 0

/-- The pointwise max of `f` over a list (`0` on the empty list). -/
def foldrMax {α : Type _} (f : α → Nat) (l : List α) : Nat :=
  l.foldr (fun a acc => max (f a) acc) 0

/-- Every member's `f`-value is bounded by the list's `foldrMax`. -/
theorem mem_le_foldrMax {α : Type _} (f : α → Nat) {a : α} {l : List α} (h : a ∈ l) :
    f a ≤ foldrMax f l := by
  induction l with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
      rw [foldrMax, List.foldr_cons]
      rcases List.mem_cons.mp h with hx | hxs
      · rw [hx]; exact Nat.le_max_left _ _
      · exact Nat.le_trans (ih hxs) (Nat.le_max_right _ _)

/-- A strict upper bound on every temp index read or defined by `instr`. -/
def instrBound (instr : Cmd) : Nat :=
  foldrMax varTmpSucc (instrUsedVars instr ++ (instrDefVar instr).toList)

/-- A strict upper bound on every temp index occurring (read or defined) anywhere in `P`. -/
def tmpBound (P : Program) : Nat :=
  foldrMax instrBound P.code.toList

/-- **The offset fresh supply.** `freshN P i = .tmp (tmpBound P + i)`, disjoint from `vars(P)`. -/
def freshN (P : Program) : Nat → Var :=
  fun i => .tmp (tmpBound P + i)

/-- A fetched instruction is a member of the code list. -/
theorem fetch_mem_code {P : Program} {nd : Node} {instr : Cmd}
    (h : P.fetch nd = some instr) : instr ∈ P.code.toList := by
  have hlt : nd < P.size := fetch_some_iff_lt.mp ⟨instr, h⟩
  have hge : P.code[nd]? = some instr := h
  have heq : P.code[nd]'hlt = instr := by
    rw [Array.getElem?_eq_getElem (show nd < P.code.size from hlt)] at hge
    exact Option.some.inj hge
  rw [List.mem_iff_getElem]
  exact ⟨nd, by rw [Array.length_toList]; exact hlt, by rw [Array.getElem_toList]; exact heq⟩

/-- **The core bound.** Every temp index occurring in a fetched instruction of `P` is `< tmpBound P`. -/
theorem tmp_lt_tmpBound {P : Program} {nd : Node} {instr : Cmd} {k : Nat}
    (h : P.fetch nd = some instr)
    (hmem : (Var.tmp k) ∈ instrUsedVars instr ++ (instrDefVar instr).toList) :
    k < tmpBound P := by
  have h1 : k + 1 ≤ instrBound instr := mem_le_foldrMax varTmpSucc hmem
  have h2 : instrBound instr ≤ tmpBound P := mem_le_foldrMax instrBound (fetch_mem_code h)
  omega

/-- **The offset supply discharges `FreshForN` — for ANY program.** Every `freshN P i` sits strictly
    above the temp bound, so no instruction reads it (`unread`) or defines it (`noClash`); and the
    offset is injective. -/
theorem freshN_freshForN (P : Program) : FreshForN P (freshN P) where
  unread := by
    intro nd instr i hfetch hmem
    have hmem2 : (Var.tmp (tmpBound P + i)) ∈ instrUsedVars instr ++ (instrDefVar instr).toList :=
      List.mem_append.mpr (Or.inl hmem)
    have hlt : tmpBound P + i < tmpBound P := tmp_lt_tmpBound hfetch hmem2
    omega
  noClash := by
    intro nd instr i hfetch hdef
    have hmem : (freshN P i) ∈ (instrDefVar instr).toList := by rw [hdef]; simp [Option.toList]
    have hmem2 : (Var.tmp (tmpBound P + i)) ∈ instrUsedVars instr ++ (instrDefVar instr).toList :=
      List.mem_append.mpr (Or.inr hmem)
    have hlt : tmpBound P + i < tmpBound P := tmp_lt_tmpBound hfetch hmem2
    omega
  inj := by
    intro a b h
    injection h with h4
    omega

/-- **`Nonobs` is free.** The offset supply consists entirely of compiler temps. -/
theorem freshN_nonobs (P : Program) : Nonobs (freshN P) := fun _ => rfl

end Normalize
end BaseLanguage
