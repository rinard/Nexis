-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
/-!
# `Pass.Compact` — the shared CFG-compaction core (keep-predicate + representative map).

Both `Pass.Cleanup` (noop-elimination) and DCE (unreachable-code elimination) do the *same* thing at the
data level: keep a subset of nodes (a `keep` predicate), renumber the survivors densely, and rewrite every
edge through a representative map `rep` (`Node → Node`) into the kept set. They differ only in the pair
they instantiate:

* **Cleanup** — `keep = !droppable` (drop bypassable `noop`s), `rep = resolve` (chase the `noop` chain to a
  kept node).
* **DCE** — `keep = reachable` (drop unreachable nodes), `rep = id`-on-kept with a redirect of dropped
  targets to the entry (a dropped node is only ever the successor of a *faulting* kept node, so the edge is
  never taken; it just needs to point *somewhere* kept for well-formedness).

This module factors the compaction itself (`compactBy`) and its well-formedness, parameterized by
`(keep, rep)` (already specialised to the program `P`) under one interface: **the entry, and every
successor of a kept node, resolves via `rep` to a kept in-range node**. Each pass supplies that interface
and its own behaviour-preservation simulation.
-/
namespace BaseLanguage
namespace Pass
namespace Compact

open Tac Semantics

variable (keep : Node → Bool) (rep : Node → Node)

/-- Kept nodes, in ascending original-index order (compaction preserves program order). -/
def keptList (P : Program) : List Node := (List.range P.size).filter keep

/-- New (compacted) index of a node's representative. -/
def remap (ks : List Node) (nd : Node) : Node := ks.findIdx (fun k => k == rep nd)

/-- Rewrite an instruction's successor edges through `rep` + `remap`. -/
def remapCmd (ks : List Node) : Cmd → Cmd
  | .assign x e next => .assign x e (remap rep ks next)
  | .ifz x z nz      => .ifz x (remap rep ks z) (remap rep ks nz)
  | .noop next       => .noop (remap rep ks next)
  | .halt            => .halt

/-- **Compaction.** Keep the `keep` nodes, renumber densely, rewrite edges through `rep`. -/
def compactBy (P : Program) : Program :=
  let ks := keptList keep P
  { entry := remap rep ks P.entry,
    code  := (ks.map (fun nd => remapCmd rep ks ((P.fetch nd).getD .halt))).toArray,
    obs   := P.obs }

variable {keep rep}

@[simp] theorem compactBy_obs (P : Program) : (compactBy keep rep P).obs = P.obs := rfl
@[simp] theorem compactBy_entry (P : Program) :
    (compactBy keep rep P).entry = remap rep (keptList keep P) P.entry := rfl

theorem compactBy_size (P : Program) : (compactBy keep rep P).size = (keptList keep P).length := by
  simp [compactBy, Program.size, List.length_map]

/-- A kept node is in range. -/
theorem keptList_lt {P : Program} {nd : Node} (h : nd ∈ keptList keep P) : nd < P.size := by
  rw [keptList, List.mem_filter, List.mem_range] at h; exact h.1

/-- `keep`-membership characterization of the kept list. -/
theorem mem_keptList {P : Program} {nd : Node} :
    nd ∈ keptList keep P ↔ nd < P.size ∧ keep nd = true := by
  rw [keptList, List.mem_filter, List.mem_range]

/-- A representative that is kept-and-in-range remaps to a valid compacted index. -/
theorem remap_lt {P : Program} {nd : Node} (h : rep nd ∈ keptList keep P) :
    remap rep (keptList keep P) nd < (keptList keep P).length :=
  List.findIdx_lt_length_of_exists ⟨rep nd, h, by simp⟩

/-- The compacted program fetches the remapped instruction of the `n`-th kept node. -/
theorem compactBy_fetch {P : Program} {n : Node} (h : n < (keptList keep P).length) :
    (compactBy keep rep P).fetch n
      = some (remapCmd rep (keptList keep P) ((P.fetch ((keptList keep P)[n]'h)).getD .halt)) := by
  unfold Program.fetch compactBy
  rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem h]
  rfl

/-- A remapped instruction's successors are the originals, each pushed through `remap`. -/
theorem remapCmd_succs {ks : List Node} (instr : Cmd) :
    (remapCmd rep ks instr).succs = instr.succs.map (remap rep ks) := by
  cases instr <;> rfl

/-- The kept node at slot `remap nd` is `rep nd` (when `rep nd` is kept). -/
theorem getElem_remap {P : Program} {nd : Node} (h : rep nd ∈ keptList keep P) :
    (keptList keep P)[remap rep (keptList keep P) nd]'(remap_lt h) = rep nd := by
  have hb : ((keptList keep P)[remap rep (keptList keep P) nd]'(remap_lt h) == rep nd) = true := by
    unfold remap; exact @List.findIdx_getElem _ (fun k => k == rep nd) (keptList keep P) _
  exact eq_of_beq hb

/-- The compacted program fetches the *representative's* remapped instruction. -/
theorem compacted_fetch {P : Program} {nd : Node} (h : rep nd ∈ keptList keep P) {c : Cmd}
    (hc : P.fetch (rep nd) = some c) :
    (compactBy keep rep P).fetch (remap rep (keptList keep P) nd)
      = some (remapCmd rep (keptList keep P) c) := by
  rw [compactBy_fetch (remap_lt h), getElem_remap h, hc, Option.getD_some]

/-- **The compaction interface.** The entry, and every successor of every kept node, resolves via `rep`
    to a kept (hence in-range) node. This is exactly what makes `compactBy` well-formed. -/
structure Interface (keep : Node → Bool) (rep : Node → Node) (P : Program) : Prop where
  entry_rep_kept : rep P.entry ∈ keptList keep P
  succ_rep_kept  : ∀ {n instr s}, keep n = true → P.fetch n = some instr → s ∈ instr.succs →
                     rep s ∈ keptList keep P

/-- **`compactBy` is well-formed** given the interface. -/
theorem compactBy_wellFormed {P : Program} (I : Interface keep rep P) :
    WellFormed (compactBy keep rep P) := by
  refine ⟨?_, ?_⟩
  · rw [compactBy_entry, compactBy_size]; exact remap_lt I.entry_rep_kept
  · intro n instr s hf hs
    have hn : n < (keptList keep P).length := by have := fetch_lt hf; rwa [compactBy_size] at this
    have hinstr : instr = remapCmd rep (keptList keep P) ((P.fetch ((keptList keep P)[n]'hn)).getD .halt) :=
      Option.some.inj (by rw [← compactBy_fetch hn]; exact hf.symm)
    have hkn : (keptList keep P)[n]'hn ∈ keptList keep P := List.getElem_mem hn
    have hkn_lt : (keptList keep P)[n]'hn < P.size := keptList_lt hkn
    have hkeep : keep ((keptList keep P)[n]'hn) = true := (mem_keptList.mp hkn).2
    obtain ⟨c, hc⟩ : ∃ c, P.fetch ((keptList keep P)[n]'hn) = some c :=
      ⟨_, Array.getElem?_eq_getElem hkn_lt⟩
    rw [hc, Option.getD_some] at hinstr
    subst hinstr
    rw [compactBy_size]
    -- every successor edge of the kept node `c` remaps into range, via the interface
    have edge : ∀ {t}, t ∈ c.succs → remap rep (keptList keep P) t < (keptList keep P).length :=
      fun ht => remap_lt (I.succ_rep_kept hkeep hc ht)
    cases c with
    | assign x e next =>
        simp only [remapCmd, Cmd.succs, List.mem_singleton] at hs; subst hs
        exact edge (by simp [Cmd.succs])
    | ifz x z nz =>
        simp only [remapCmd, Cmd.succs, List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with h | h <;> subst h <;> exact edge (by simp [Cmd.succs])
    | noop next =>
        simp only [remapCmd, Cmd.succs, List.mem_singleton] at hs; subst hs
        exact edge (by simp [Cmd.succs])
    | halt => simp only [remapCmd, Cmd.succs, List.not_mem_nil] at hs

end Compact
end Pass
end BaseLanguage
