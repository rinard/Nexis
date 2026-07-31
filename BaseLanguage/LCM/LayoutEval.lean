-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.IR.Cost

/-!
# `LayoutEval` — the layout/eval connection

Characterizes `computesExpr (transform P S) slot e` (does the transform's slot evaluate `e`?) purely
in terms of the placements `insertBefore`/`insertAfter` and the kept-original control. This lets the run-fold
(`evalCount_next`) attribute each evaluation to a placement, for the eval-count optimality theorem.

Three slot kinds compute `e`:
* an `insChain` materialization slot — iff its expression is `e` (so `e ∈ insertBefore i`);
* an `exitChain` materialization slot — iff its expression is `e` (so `e ∈ insertAfter i`);
* the floated control of an **unreplaced** `assign` whose original RHS is `e` (a necessary kept original).
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-- **Materialization (entry).** At `insChain` slot `k` of node `i`, the transform evaluates `e` iff the
    `k`-th inserted expression is `e`. -/
theorem computesExpr_insChain {P : Program} {S : LcmSpec P} {i : Node} (hi : i < P.size)
    {k : Nat} (hk : k < (insertBefore P S i).toList.length) (e : Expr) :
    computesExpr (transform P S) (blockOff P S i + k) e
      = ((insertBefore P S i).toList[k]'hk == e) := by
  have hkb : k < (block P S i).length := by rw [block_length]; unfold blockLen; omega
  have hml : k < (insChain P (insertBefore P S i).toList (blockOff P S i)).length := by
    rw [insChain_length]; exact hk
  have hfetch : (transform P S).fetch (blockOff P S i + k)
      = some (.assign (tempFor P ((insertBefore P S i).toList[k]'hk)) ((insertBefore P S i).toList[k]'hk)
          (blockOff P S i + k + 1)) := by
    rw [transform_fetch hi hkb, block_getElem?_insChain hml, insChain_getElem? hk]
  unfold computesExpr; rw [hfetch]

/-- **Materialization (exit).** At `exitChain` slot `k` of node `i` (an `assign`/`noop`), the transform
    evaluates `e` iff the `k`-th exit-inserted expression is `e`. -/
theorem computesExpr_exitChain {P : Program} {S : LcmSpec P} {i : Node} (hi : i < P.size) {next : Node}
    (hfi : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next))
    {k : Nat} (hk : k < (insertAfter P S i).toList.length) (e : Expr) :
    computesExpr (transform P S) (blockOff P S i + (insertBefore P S i).toList.length + 1 + k) e
      = ((insertAfter P S i).toList[k]'hk == e) := by
  have hkb : (insertBefore P S i).toList.length + 1 + k < (block P S i).length := by
    rw [block_length]; unfold blockLen
    rcases hfi with h | ⟨x, e', h⟩ <;> simp only [h] <;> omega
  have hfetch : (transform P S).fetch (blockOff P S i + (insertBefore P S i).toList.length + 1 + k)
      = some (.assign (tempFor P ((insertAfter P S i).toList[k]'hk)) ((insertAfter P S i).toList[k]'hk)
          (if k + 1 == (insertAfter P S i).toList.length then blockOff P S next
           else (blockOff P S i + (insertBefore P S i).toList.length + 1) + k + 1)) := by
    rw [show blockOff P S i + (insertBefore P S i).toList.length + 1 + k
          = blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) from by omega]
    rw [transform_fetch hi hkb, getElem?_block_exit hfi, exitChain_getElem? hk]
    rw [show blockOff P S i + ((insertBefore P S i).toList.length + 1 + k) + 1
          = (blockOff P S i + (insertBefore P S i).toList.length + 1) + k + 1 from by omega]
  unfold computesExpr; rw [hfetch]

/-- **Control.** The floated control of node `i` evaluates `e` iff `i` is an `assign x e₀ next` whose
    original RHS `e₀ = e` is **kept** (not `numbered`-and-`recoverable`, hence not rewritten to `x := h_{e₀}`).
    A replaced control reads the temp `h_{e₀}` (a fresh atom ≠ any original `e`), so it recomputes nothing. -/
theorem computesExpr_ctrl {P : Program} {S : LcmSpec P} {i : Node} (hi : i < P.size) (e : Expr) :
    computesExpr (transform P S) (blockOff P S i + (insertBefore P S i).toList.length) e
      = (match P.fetch i with
         | some (.assign _ e0 _) =>
             if isNumbered e0 && (recoverable P S i).contains e0
             then (Expr.atom (.var (tempFor P e0)) == e)
             else (e0 == e)
         | _ => false) := by
  unfold computesExpr
  rw [ctrl_slot_fetch S hi]
  unfold ctrlCmd
  cases hf : P.fetch i with
  | none => rfl
  | some instr =>
      cases instr with
      | assign x e0 next => by_cases hc : isNumbered e0 && (recoverable P S i).contains e0 <;> simp [hc]
      | ifz x z nz => rfl
      | noop next => rfl
      | halt => rfl

/-- **The gate, at the level of `Assignments` membership.** Node `i`'s entry block evaluates `e` at some
    `insChain` slot **iff** `e ∈ insertBefore i`. (The `exitChain`/`insertAfter` statement is identical.) This is
    the form the run-fold consumes: each materialization evaluation is attributable to a placement. -/
theorem insChain_computes_iff {P : Program} {S : LcmSpec P} {i : Node} (hi : i < P.size) (e : Expr) :
    (∃ k, ∃ _hk : k < (insertBefore P S i).toList.length,
        computesExpr (transform P S) (blockOff P S i + k) e = true)
      ↔ e ∈ insertBefore P S i := by
  constructor
  · rintro ⟨k, hk, hc⟩
    rw [computesExpr_insChain hi hk] at hc
    exact (eq_of_beq hc) ▸ Assignments.mem_toList.mp (List.getElem_mem hk)
  · intro he
    obtain ⟨k, hk, hke⟩ := List.mem_iff_getElem.mp (Assignments.mem_toList.mpr he)
    exact ⟨k, hk, by rw [computesExpr_insChain hi hk, hke]; exact beq_self_eq_true e⟩

end BaseLanguage.Analyses.LCM
