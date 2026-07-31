-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

/-!
# `IR.Cfg` — the dataflow-free **graph view** of the CFG

The CFG-as-graph layer over the IR syntax: successor/predecessor lists and forward/backward
reachability (from the entry / to a `halt`). Everything here needs whole-program (`Program`) context —
it is the level *above* the single-instruction syntactic projections in `IR.TAC` (`Cmd.succs`,
`instrUsedVars`, `exprReadsVar`, …) and *below* both `Normalize.*` and the analysis specs
(`LcmDefs`/`PdceDefs`), all of which are stated over these. Everything is a direct recursive
definition or an inductive predicate — no lattices, no fixpoint iteration, no analysis domain.

Lives in `namespace Tac` alongside `Program`/`Cmd.succs`: these are graph read-offs of the IR, not
facts about any particular pass, so every client (normalization *and* the optimizations) depends on
this module directly rather than reaching through `Normalize`.
-/

namespace BaseLanguage
namespace Tac
open Semantics

/-- Successors of a node (empty off the end of the graph). -/
def succList (P : Program) (nd : Node) : List Node := (P.fetch nd).elim [] Cmd.succs

/-- `nd ∈ succList P p` exposes the underlying fetch and successor. -/
theorem mem_succList {P : Program} {p nd : Node} (h : nd ∈ succList P p) :
    ∃ instr, P.fetch p = some instr ∧ nd ∈ instr.succs := by
  cases hf : P.fetch p with
  | none => simp [succList, hf] at h
  | some instr => exact ⟨instr, rfl, by simpa [succList, hf] using h⟩

/-- The successor list of a node whose fetch is known. -/
theorem succList_eq {P : Program} {nd instr} (hf : P.fetch nd = some instr) :
    succList P nd = instr.succs := by
  simp [succList, hf]

/-- The in-range **predecessors** of `j`: every node whose successor list contains `j`. (A predecessor
    is always in range — an out-of-range node fetches nothing and has no successors — so filtering
    `range P.size` is complete.) Its length is the in-degree counted by distinct predecessor *nodes*;
    under `DistinctSuccs` (no duplicated successor) that coincides with the in-edge count. -/
def predList (P : Program) (j : Node) : List Node :=
  (List.range P.size).filter (fun i => decide (j ∈ succList P i))

theorem mem_predList {P : Program} {j i : Node} :
    i ∈ predList P j ↔ i < P.size ∧ j ∈ succList P i := by
  unfold predList; rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

theorem predList_nodup (P : Program) (j : Node) : (predList P j).Nodup :=
  (List.nodup_range).filter _

/-- An in-range fetch reads the indexed code element. -/
theorem fetch_eq_getElem {P : Program} {nd : Node} (h : nd < P.size) :
    P.fetch nd = some (P.code[nd]'h) := Array.getElem?_eq_getElem h

/-! ## Forward reachability from the entry -/

/-- `FReach P nd`: node `nd` is reachable from `P.entry` by following successor edges. -/
inductive FReach (P : Program) : Node → Prop
  | entry : FReach P P.entry
  | step {p nd : Node} : FReach P p → nd ∈ succList P p → FReach P nd

/-- **AllReachable**: every in-range node is forward-reachable from the entry. (Dead code would
    otherwise break the optimizations' extremality, so the pipeline assumes it.) -/
def AllReachable (P : Program) : Prop := ∀ nd, nd < P.size → FReach P nd

/-- A forward-reachable node of a well-formed program is in range. -/
theorem FReach_lt {P : Program} (hwf : WellFormed P) {nd : Node} (hr : FReach P nd) :
    nd < P.size := by
  induction hr with
  | entry => exact hwf.entry_lt
  | step _ hs _ =>
      obtain ⟨instr, hf, hmem⟩ := mem_succList hs
      exact hwf.succ_lt hf hmem

/-- **Pigeonhole primitive** (Mathlib-free): a `Nodup` list embeds into any superset by length. -/
theorem nodup_length_le_of_subset' {a b : List Node} (hnd : a.Nodup) (hsub : a ⊆ b) :
    a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
      have hx : x ∈ b := hsub (by simp)
      have hxnd : x ∉ xs := (List.nodup_cons.mp hnd).1
      have hxsnd : xs.Nodup := (List.nodup_cons.mp hnd).2
      have hsub' : xs ⊆ b.erase x := by
        intro y hy
        have hyne : y ≠ x := fun he => hxnd (he ▸ hy)
        exact (List.mem_erase_of_ne hyne).mpr (hsub (List.mem_cons_of_mem _ hy))
      have := ih hxsnd hsub'
      have hlen : (b.erase x).length = b.length - 1 := List.length_erase_of_mem hx
      have hb1 : 1 ≤ b.length := List.length_pos_of_mem hx
      simp only [List.length_cons]; omega

end Tac
end BaseLanguage
