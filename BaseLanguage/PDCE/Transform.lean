-- Copyright (c) 2026 Martin Rinard
import analyses.pdce.PdceAdapter

/-!
# `PDCE.Transform` — the KRS partial-dead-code (sinking) transform

Universally quantified over an arbitrary valid PDCE bundle `S : PdceSpec P` (the `live`/`sink` ghosts are
fields of the `PdceSpec` structure authored in `PdceDefs`); it introduces no analysis of its own.

**Placement (KRS, edge-based).** With `DELAYED_exit p = born p ∪ (sink p ∩ pass p)`:

* **node-entry** `matNode n = sink n ∩ blocked n ∩ live n` — candidates delayed to `n` on *every*
  in-edge, no longer delayable past `n`, and live; materialized once before `n`. `blocked` is `¬pass`
  and, at `halt`, *everything* (the exit frontier).
* **edge** `matEdge p s = (DELAYED_exit p ∖ sink s) ∩ live s` — candidates delayed out of `p` but
  dropped by the merge at `s`; materialized on the split edge `p→s`.

**Layout (two-pass, prefix-sum).** Each original node `i` becomes a contiguous *block* at offset
`blockOff i` (a prefix sum of `blockLen`): its `matNode` materialization chain, then the floated control
instruction, then a per-successor `matEdge` chain. External jumps target `blockOff s`; internal jumps stay
within the block. This makes `fetch (transform P S) k` a function of the offset table (not of any fold
state), which the layout/simulation proofs in `Layout.lean`/`Correctness.lean` rely on. Behaviourally it
is the same KRS sinking (different node labels than an in-place layout).
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-! ## Placement sets (read off the bundle) -/

/-- Candidates delayed **leaving** `n` — the `Sink.update` RHS, `born n ∪ (sink n ∩ pass n)`. -/
def delayedExit (P : Program) (S : PdceSpec P) (n : Node) : Assignments :=
  Assignments.union (born P n) (Assignments.inter (S.η n) (pass P n))

/-- Candidates **blocked** at `n` (cannot be delayed past it): the non-transparent ones, and at a
    terminal `halt` *all* of them (the exit frontier). -/
def blockedSet (P : Program) (n : Node) : Assignments :=
  match P.fetch n with
  | some .halt => allAsgns P
  | _          => Assignments.sdiff (allAsgns P) (pass P n)

/-- Node-entry materializations before `n`: in flight, blocked, and live (lhs in `live n`). -/
def matNode (P : Program) (S : PdceSpec P) (n : Node) : List Asgn :=
  (liveFilter (Assignments.inter (S.η n) (blockedSet P n)) (S.π n)).toList

/-- Edge materializations on `p → s`: delayed out of `p`, dropped by the merge at `s`, and live at `s`
    (lhs in `live s`). -/
def matEdge (P : Program) (S : PdceSpec P) (p s : Node) : List Asgn :=
  (liveFilter (Assignments.sdiff (delayedExit P S p) (S.η s)) (S.π s)).toList

/-! ## Materialization chains (straight-line `assign` sequences) -/

/-- A node-entry chain at absolute start `s0`: assignment `k` transfers to `s0 + k + 1` (the next slot;
    the last lands on the control instruction at `s0 + m.length`). -/
def matChain (m : List Asgn) (s0 : Nat) : List Cmd :=
  m.zipIdx.map (fun x => Cmd.assign x.1.lhs x.1.rhs (s0 + x.2 + 1))

/-- An edge chain at absolute start `start`, transferring to `target` after the last assignment. -/
def edgeChain (e : List Asgn) (start target : Nat) : List Cmd :=
  e.zipIdx.map (fun x => Cmd.assign x.1.lhs x.1.rhs (if x.2 + 1 == e.length then target else start + x.2 + 1))

/-! ## Block layout -/

/-- Number of instructions in node `i`'s block: `|matNode|` + the control + the successor edge chains. -/
def blockLen (P : Program) (S : PdceSpec P) (i : Node) : Nat :=
  (matNode P S i).length + 1 +
    (match P.fetch i with
     | some (.assign _ _ next) => (matEdge P S i next).length
     | some (.noop next)       => (matEdge P S i next).length
     | some (.ifz _ z nz)      => (matEdge P S i z).length + (matEdge P S i nz).length
     | _                       => 0)

/-- Absolute offset of node `i`'s block — the prefix sum of earlier block lengths. -/
def blockOff (P : Program) (S : PdceSpec P) (i : Node) : Nat :=
  ((List.range i).map (blockLen P S)).sum

/-- Node `i`'s block: `matNode` chain, the floated control, then per-successor `matEdge` chains. -/
def block (P : Program) (S : PdceSpec P) (i : Node) : List Cmd :=
  let s0 := blockOff P S i
  let c  := s0 + (matNode P S i).length    -- the control slot
  matChain (matNode P S i) s0 ++
    (match P.fetch i with
     | some (.ifz x z nz) =>
         Cmd.ifz x (if (matEdge P S i z).isEmpty then blockOff P S z else c + 1)
                     (if (matEdge P S i nz).isEmpty then blockOff P S nz else c + 1 + (matEdge P S i z).length)
           :: (edgeChain (matEdge P S i z) (c + 1) (blockOff P S z)
               ++ edgeChain (matEdge P S i nz) (c + 1 + (matEdge P S i z).length) (blockOff P S nz))
     | some (.assign _ _ next) =>
         Cmd.noop (if (matEdge P S i next).isEmpty then blockOff P S next else c + 1)
           :: edgeChain (matEdge P S i next) (c + 1) (blockOff P S next)
     | some (.noop next) =>
         Cmd.noop (if (matEdge P S i next).isEmpty then blockOff P S next else c + 1)
           :: edgeChain (matEdge P S i next) (c + 1) (blockOff P S next)
     | _ => [Cmd.halt])

/-- **The KRS PDCE sinking transform**, over an arbitrary valid PDCE bundle `S`. Concatenates the
    per-node blocks; the entry is the entry node's block offset. -/
def transform (P : Program) (S : PdceSpec P) : Program :=
  { entry := blockOff P S P.entry,
    code  := ((List.range P.size).flatMap (block P S)).toArray,
    obs   := P.obs }

/-! ## Executable memoization of `transform` (compiled-only, proven equal)

As in `LCM.Transform`, `blockOff` re-runs `blockLen` `O(n²)` times across the `flatMap`, and each
`blockLen` reads the decoded `S.η`/`S.π` and `allAsgns`/`pass`. Compute the `blockLen` list once,
prefix-sum it, and feed the offset to `blockAt` (= `block` with `blockOff P S` abstracted to a parameter,
defeq at `off = blockOff P S`). `@[csimp]` swaps only the compiled `transform`; all proofs use the
original `def`s. No new analysis — offset caching. -/

/-- `block` with the block offset abstracted to a parameter `off` (defeq to `block` at `off = blockOff P S`). -/
def blockAt (P : Program) (S : PdceSpec P) (off : Node → Nat) (i : Node) : List Cmd :=
  let s0 := off i
  let c  := s0 + (matNode P S i).length
  matChain (matNode P S i) s0 ++
    (match P.fetch i with
     | some (.ifz x z nz) =>
         Cmd.ifz x (if (matEdge P S i z).isEmpty then off z else c + 1)
                     (if (matEdge P S i nz).isEmpty then off nz else c + 1 + (matEdge P S i z).length)
           :: (edgeChain (matEdge P S i z) (c + 1) (off z)
               ++ edgeChain (matEdge P S i nz) (c + 1 + (matEdge P S i z).length) (off nz))
     | some (.assign _ _ next) =>
         Cmd.noop (if (matEdge P S i next).isEmpty then off next else c + 1)
           :: edgeChain (matEdge P S i next) (c + 1) (off next)
     | some (.noop next) =>
         Cmd.noop (if (matEdge P S i next).isEmpty then off next else c + 1)
           :: edgeChain (matEdge P S i next) (c + 1) (off next)
     | _ => [Cmd.halt])

theorem blockAt_blockOff (P : Program) (S : PdceSpec P) : blockAt P S (blockOff P S) = block P S := rfl

/-- The memoized transform: `blockLen` evaluated once per node, offsets are prefix sums over that list. -/
def transformFast (P : Program) (S : PdceSpec P) : Program :=
  let lens := (List.range P.size).map (blockLen P S)
  let off  : Node → Nat := fun i => if i ≤ P.size then (lens.take i).sum else blockOff P S i
  { entry := off P.entry,
    code  := ((List.range P.size).flatMap (blockAt P S off)).toArray,
    obs   := P.obs }

theorem off_memo_app (P : Program) (S : PdceSpec P) (i : Node) :
    (if i ≤ P.size then (((List.range P.size).map (blockLen P S)).take i).sum
     else blockOff P S i) = blockOff P S i := by
  by_cases h : i ≤ P.size
  · rw [if_pos h, blockOff, ← List.map_take, List.take_range, Nat.min_eq_left h]
  · rw [if_neg h]

@[csimp] theorem transform_eq_transformFast : @transform = @transformFast := by
  funext P S
  simp only [transform, transformFast, off_memo_app, blockAt_blockOff]

end BaseLanguage.Analyses.PDCE
