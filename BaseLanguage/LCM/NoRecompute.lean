-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.IR.Cost

/-!
# `NoRecompute` — the no-recompute crux for the (1-extend) transform

The eval-count optimality crux: along a run, `(insertBefore n ∪ insertAfter n) ∩ M = ∅`, where `M` is
`Match`'s materialized set (this-path availability) — equivalently, S computes `e` at most once per
fresh-need interval.

The crux reduces to the invariant `e ∈ M ⇒ e ∉ ηₚ(node)` (⇒ `M ∩ insertBefore = ∅` via
`insertBefore ⊆ latestNode ⊆ ηₚ`, and `M ∩ insertAfter = ∅` via `insertAfter_postp_disjoint`). Its
maintenance rests on `ηₚ c' ⊆ earliest(c→c') ∪ (ηₚ c ∖ ue c)`: with `e ∉ ηₚ c`, `e ∈ ηₚ c'` forces
`e ∈ earliest(c→c')`, and `earliest_excludes_transferable` kills that whenever `e` is still
anticipated-in (`e ∈ πₐ c`) — the held-and-still-needed case. So `e` re-enters `ηₚ` only
at a genuine fresh-need boundary (a kill or an anticipation gap), i.e. once per interval.

Worked CFG (`e=y+z`, transparent everywhere):
`0:noop→1 · 1:ifz→{2,3} · 2(A):a:=e→4 · 3(B):noop→4 · 4(J):noop→5 · 5(K):b:=e→6 · 6:halt`.
* **Branch:** the greatest `ηₚ` defers `e` to every using successor ⇒ `e ∈ τₚ` ⇒ `e ∉ latestNode(branch)`.
* **Join + post-join use:** reduces to `insertBefore(5) ∋ e ⟺ e ∈ ηₚ(5)`. The greatest ηₚ has
  `e ∈ ηₚ(1,2,3)` (earliest at the entry edge, carried) and `e ∉ ηₚ(4)` (join merge — from pred 2,
  `availableOut(2)∋e ⇒ e∉earliest(2,4)` and `∖ue(2)` drops it). Then `e ∈ ηₚ(5) ⟺ e ∈ earliest(4,5)`; since
  `e ∈ πₐ(4)` (anticipated-in: `e ∈ πₐ(5)` and `e ∈ pass(4)`), `earliest`'s third conjunct
  `¬πₐ(4)` excludes `e`, so `e ∉ earliest(4,5) ⇒ e ∉ ηₚ(5) ⇒ insertBefore(5)` does not fire.
  `e` is placed once per path — node 2 (via `ue`) on the A-path, node 3 (via `¬τₚ(3)`, since `e∉ηₚ(4)`) on
  the B-path — and read at the use 5. This is textbook PRE.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-- **Carry anchor.** The exit-carry never lands where the expression stays postponable: for an
    `assign`/`noop` `i → next`, `insertAfter i ∩ ηₚ next = ∅`. Immediate from `latestEdge`'s `∖ ηₚ next` —
    this is the half of `M ∩ ηₚ = ∅` that is a clean projection (no run dependence). -/
theorem insertAfter_postp_disjoint {P : Program} (S : LcmSpec P) {i next : Node} {e : Expr}
    (he : e ∈ insertAfter P S i)
    (hf : (∃ x ex, P.fetch i = some (.assign x ex next)) ∨ P.fetch i = some (.noop next)) :
    e ∉ S.ηₚ next := by
  have hee : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ i next := by
    unfold insertAfter at he
    rcases hf with ⟨x, ex, hfi⟩ | hfi <;> rw [hfi] at he <;> exact (Assignments.mem_inter.mp he).1
  unfold latestEdge at hee
  exact (Assignments.mem_sdiff.mp hee).2

/-- **Entry reduction.** `insertBefore n ⊆ postp n`, so the invariant `M ∩ postp = ∅` discharges the
    `insertBefore` half of the crux directly. With `insertAfter_postp_disjoint` for the exit half, the whole
    crux `(insertBefore n ∪ insertAfter n) ∩ M = ∅` reduces to **one** operational invariant. -/
theorem insertBefore_sub_postp {P : Program} (S : LcmSpec P) {n : Node} {e : Expr}
    (he : e ∈ (insertBefore P S n).toList) : e ∈ S.ηₚ n :=
  latestNode_sub_postp S n e (insertBefore_sub_latestNode he)

/-- **The blocking mechanism.** A still-anticipated-in expression is NOT "newly earliest" on any non-entry
    edge — `earliest`'s third conjunct `¬πₐ(tail)` excludes it. This is exactly why a held `e` does not
    re-enter `earliest`/`ηₚ` at a post-join use: while `e` is still anticipated at the node's entry
    (`e ∈ πₐ(tail)`), it is not born on the leaving edge. So `e` re-enters `earliest` only at a genuine
    fresh-need boundary (`e ∉ πₐ`: a kill or an anticipation gap) — i.e. once per interval. -/
theorem earliest_excludes_transferable {P : Program} {πₐ ηₐ : Node → Assignments} {tail head : Node}
    (hne : tail ≠ P.entry) {e : Expr} (hpi : e ∈ πₐ tail) :
    e ∉ earliest P πₐ ηₐ tail head := by
  intro he
  unfold earliest at he
  rw [Assignments.mem_inter, if_neg hne] at he
  exact (Assignments.mem_sdiff.mp he.2).2 hpi

end BaseLanguage.Analyses.LCM
