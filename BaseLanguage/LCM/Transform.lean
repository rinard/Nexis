-- Copyright (c) 2026 Martin Rinard
import analyses.lcm.LcmAdapter
import BaseLanguage.Normalize.FreshSupply

/-!
# `LCM.Transform` — the Lazy Code Motion (PRE) hoisting transform

Universally quantified over an arbitrary valid LCM bundle `S : LcmSpec P` (the `πₐ`/`ηₐ`/`ηₚ`/
`πᵤ`/`τₚ`/`τᵤ` ghosts generated from the spec bundle); it introduces **no analysis of its
own** — every set it reads is a projection of `S` or a syntactic function of `P` (the `BaseLanguage.Analyses.LCM.*` node-locals in
`LcmDefs` / the CFG helpers in `IR.Cfg`).

**Placement (KRS — entry AND edge; no critical-edge splitting).** Placement is at node entry (`insertBefore`)
and on the *taken out-edge* (`insertEdge`), realized by a per-branch **edge chain** at `ifz` nodes (and the
`insertAfter` exit chain at `1-successor` `assign`/`noop`). Because the transform materializes edge inserts
directly on the branch edge, no critical-edge splitting is required. LCM **hoists** each numbered expression
`e` into a fresh temp `h_e := tempFor P e`, materializes
it on its KRS placement frontier, and **replaces** every original `x := e` by the copy `x := h_e`.

* **insert (entry)** `insertBefore n = (latestNode n ∖ latestOut n) ∩ τᵤ n` — materialize `h_e := e` at the entry of `n`, for
  every non-isolated `e` on the latest frontier (the `τᵤ` gate is the lazy / lifetime-optimal
  refinement). Realizes every edge insertion that lands at `n`'s entry (prepend / split-node / transparent
  carry).
* **insert (exit)** `insertAfter i = latestEdge(i,next) ∩ τᵤ i` for a `1-successor` source
  (`assign`/`noop`) `i → next` — the KRS edge insertion the merge at `next` drops, carrying BOTH the
  killed/earliest-born part AND the transparent carry `(ηₚ i ∖ ue i) ∖ ηₚ next`; `∅` for
  `ifz`/`halt` (an `ifz`'s edge inserts ride the branch edges via `insertEdge`). The append-to-source case.
* **replace** at node `n` is gated by `recoverable n = πᵤ n ∪ insertBefore n`: rewrite `x := e ↦ x := h_e`
  only when the temp is materialized when control reaches `n` (born here, or demanded from upstream). An
  isolated use (gated out of `insertBefore`, not in `πᵤ`) keeps its original `x := e`.

**Layout (prefix-sum blocks).** Each original node `i` becomes a contiguous *block* at offset `blockOff i`:
its `insChain` (entry inserts), the floated+rewritten control with successors remapped to `blockOff`, then
the exit inserts (`exitChain`): `insertAfter` for `assign`/`noop`, and per-branch `insertEdge` for `ifz`. So
`blockLen i = |insertBefore i| + 1 + tail`, where `tail = |insertAfter i|` for `assign`/`noop`,
`|insertEdge i z| + |insertEdge i nz|` for `ifz`, and `0` for `halt`. Mirrors PDCE's `matNode`/`matEdge`.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## The per-expression fresh temp (bookkeeping, not an analysis) -/

/-- The fresh temp hoisting expression `e`: its slot in `allExprs`, fed to the offset fresh supply. -/
def tempFor (P : Program) (e : Expr) : Var := freshN P ((allExprs P).toList.idxOf e)

/-- Generic `l[l.idxOf a] = a` for a member (any `LawfulBEq` element type). -/
theorem getElem_idxOf' {α} [BEq α] [LawfulBEq α] {l : List α} {a : α} (h : a ∈ l) :
    l[l.idxOf a]'(List.idxOf_lt_length_of_mem h) = a := by
  have hlt : l.findIdx (· == a) < l.length := List.idxOf_lt_length_of_mem h
  have := List.findIdx_getElem (xs := l) (p := (· == a)) (w := hlt)
  simpa [List.idxOf] using this

/-- **`tempFor` is a temp** — hence distinct from every original (observable) variable. -/
theorem tempFor_nonobs (P : Program) (e : Expr) : varIsOrig (tempFor P e) = false :=
  freshN_nonobs P _

/-- **`tempFor` is fresh in `P`** — read by no instruction (so the transform's reads of `h_e` never
    alias a source operand). -/
theorem tempFor_unread (P : Program) (e : Expr) {nd : Node} {instr : Cmd}
    (h : P.fetch nd = some instr) : tempFor P e ∉ instrUsedVars instr :=
  (freshN_freshForN P).unread _ h

/-- **`tempFor` is injective on `allExprs`** — distinct expressions get distinct temps. -/
theorem tempFor_inj (P : Program) {e e' : Expr}
    (he : e ∈ (allExprs P).toList) (he' : e' ∈ (allExprs P).toList)
    (h : tempFor P e = tempFor P e') : e = e' := by
  have hidx : (allExprs P).toList.idxOf e = (allExprs P).toList.idxOf e' :=
    (freshN_freshForN P).inj h
  calc e = (allExprs P).toList[(allExprs P).toList.idxOf e]'(List.idxOf_lt_length_of_mem he) :=
            (getElem_idxOf' he).symm
    _ = (allExprs P).toList[(allExprs P).toList.idxOf e']'(List.idxOf_lt_length_of_mem he') := by
            simp only [hidx]
    _ = e' := getElem_idxOf' he'

/-! ## Placement sets (read off the bundle `S`) -/

/-- **Node-exit placement frontier** (1-extend two-valued isolation, `Latestout`): the full KRS edge
    insertion `LATER(i,next) ∖ LATERin(next) = latestEdge(i,next)` at a `1-successor` source (`assign`/`noop`);
    at an `ifz`, the union `latestEdge(i,z) ∪ latestEdge(i,nz)` over both branch edges; `∅` at `halt`. This is
    the *widened* exit set — it carries BOTH the killed/earliest-born part AND the
    **transparent carry** `(ηₚ i ∖ ue i) ∖ ηₚ next` (which belongs at the exit, not
    the entry — see `insertBefore_disjoint_insertAfter` in `EvalCountOpt.lean`). -/
def latestOut (P : Program) (S : LcmSpec P) (i : Node) : Assignments :=
  match P.fetch i with
  | some (.assign _ _ next) => latestEdge P S.πₐ S.ηₐ S.ηₚ i next
  | some (.noop next)       => latestEdge P S.πₐ S.ηₐ S.ηₚ i next
  | some (.ifz _ z nz)      => Assignments.union (latestEdge P S.πₐ S.ηₐ S.ηₚ i z)
                                                 (latestEdge P S.πₐ S.ηₐ S.ηₚ i nz)
  | _                       => Assignments.empty

/-- **Node-entry** placement before `n` (1-extend `Latestin`): the `latestNode` frontier **minus the exit
    part** (`latestOut`), gated by `τᵤ`. The `∖ latestOut` keeps entry and exit disjoint —
    no expression is placed twice (`insertBefore_disjoint_insertAfter`, `EvalCountOpt.lean`). At an `ifz` the
    subtracted `latestOut` is the union of the two branch edges. -/
def insertBefore (P : Program) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.inter (Assignments.sdiff (latestNode P S.ηₚ S.τₚ n) (latestOut P S n)) (S.τᵤK n)

/-- **Node-exit insert set**: `latestOut ∩ usedOut`. Realized by appending to a 1-successor source
    (`assign`/`noop`); `∅` for `ifz`/`halt`. -/
def insertAfter (P : Program) (S : LcmSpec P) (i : Node) : Assignments :=
  match P.fetch i with
  | some (.assign _ _ next) =>
      Assignments.inter (latestEdge P S.πₐ S.ηₐ S.ηₚ i next) (S.τᵤK i)
  | some (.noop next) =>
      Assignments.inter (latestEdge P S.πₐ S.ηₐ S.ηₚ i next) (S.τᵤK i)
  | _ => Assignments.empty

/-- **Edge-indexed insert set** (edge placement): the KRS edge insertion on an *arbitrary* edge `i → j`,
    gated by `τᵤ`. For a `1-successor` source (`assign`/`noop`) `j = next` this coincides with
    `insertAfter i` (materialized by the trailing exit chain); for an `ifz` source it realizes the insert
    on the branch edge `i → j` via a per-branch **edge chain** (the on-demand critical-edge split), so no
    critical-edge split pre-pass is needed. -/
def insertEdge (P : Program) (S : LcmSpec P) (i j : Node) : Assignments :=
  Assignments.inter (latestEdge P S.πₐ S.ηₐ S.ηₚ i j) (S.τᵤK i)

/-- **Unified node-exit / edge insert set** `latestOut ∩ usedOut`: the demanded part of every insertion
    leaving `n`. For a `1-successor` source (`assign`/`noop`) it is exactly `insertAfter n` (materialized by
    the trailing exit chain); for an `ifz` it is `insertEdge(n,z) ∪ insertEdge(n,nz)` (materialized by the two
    branch edge chains). The coverage layer subtracts this from `πᵤ` (nothing leaving `n` need be carried in
    `M`). -/
def insertOut (P : Program) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.inter (latestOut P S n) (S.τᵤK n)

/-- Expressions whose temp is **recoverable** on entry to `n`: born here (`insertBefore`) or demanded from
    upstream (`πᵤ`). The replace gate — keeps insert/replace consistent. -/
def recoverable (P : Program) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.union (S.πᵤK n) (insertBefore P S n)

/-! ## Materialization chains (straight-line `h_e := e` sequences) -/

/-- A node-entry insert chain at absolute start `s0`: insert `k` materializes `tempFor e_k` and transfers
    to `s0 + k + 1` (the next slot; the last lands on the control instruction at `s0 + m.length`). -/
def insChain (P : Program) (m : List Expr) (s0 : Nat) : List Cmd :=
  m.zipIdx.map (fun x => Cmd.assign (tempFor P x.1) x.1 (s0 + x.2 + 1))

/-- An exit chain at absolute `start`, after the control, transferring to `target` (= `blockOff next`)
    after the last assignment (the others to the next slot). Analogue of PDCE's `edgeChain`. -/
def exitChain (P : Program) (m : List Expr) (start target : Nat) : List Cmd :=
  m.zipIdx.map (fun x => Cmd.assign (tempFor P x.1) x.1
    (if x.2 + 1 == m.length then target else start + x.2 + 1))

/-! ## Block layout -/

/-- Number of instructions in node `i`'s block: `|insertBefore i|` entry inserts + the control + (for an
    `assign`) `|insertAfter i|` exit inserts. -/
def blockLen (P : Program) (S : LcmSpec P) (i : Node) : Nat :=
  (insertBefore P S i).toList.length + 1 +
    (match P.fetch i with
     | some (.assign _ _ _) => (insertAfter P S i).toList.length
     | some (.noop _)       => (insertAfter P S i).toList.length
     | some (.ifz _ z nz)   => (insertEdge P S i z).toList.length + (insertEdge P S i nz).toList.length
     | _                    => 0)

/-- Absolute offset of node `i`'s block — the prefix sum of earlier block lengths. -/
def blockOff (P : Program) (S : LcmSpec P) (i : Node) : Nat :=
  ((List.range i).map (blockLen P S)).sum

/-- The floated control instruction of node `i`, successors remapped to `blockOff`, an original `x := e`
    rewritten to `x := h_e` **iff** `e` is numbered and recoverable, and (for an `assign`) its successor
    pointed at the exit chain if nonempty, else straight to `blockOff next`. -/
def ctrlCmd (P : Program) (S : LcmSpec P) (i : Node) : Cmd :=
  match P.fetch i with
  | some (.assign x e next) =>
      let tgt := if (insertAfter P S i).toList.isEmpty
                 then blockOff P S next
                 else blockOff P S i + (insertBefore P S i).toList.length + 1
      if isNumbered e && (recoverable P S i).contains e
      then Cmd.assign x (.atom (.var (tempFor P e))) tgt
      else Cmd.assign x e tgt
  | some (.ifz x z nz) =>
      let z0 := blockOff P S i + (insertBefore P S i).toList.length + 1
      let n0 := z0 + (insertEdge P S i z).toList.length
      Cmd.ifz x
        (if (insertEdge P S i z).toList.isEmpty then blockOff P S z else z0)
        (if (insertEdge P S i nz).toList.isEmpty then blockOff P S nz else n0)
  | some (.noop next)  =>
      let tgt := if (insertAfter P S i).toList.isEmpty
                 then blockOff P S next
                 else blockOff P S i + (insertBefore P S i).toList.length + 1
      Cmd.noop tgt
  | _                  => Cmd.halt

/-- Node `i`'s block: its `insChain` (lands on the control slot), the rewritten control, then (for an
    `assign`) its `exitChain` (lands on `blockOff next`). -/
def block (P : Program) (S : LcmSpec P) (i : Node) : List Cmd :=
  insChain P (insertBefore P S i).toList (blockOff P S i) ++
    (ctrlCmd P S i ::
      (match P.fetch i with
       | some (.assign _ _ next) =>
           exitChain P (insertAfter P S i).toList
             (blockOff P S i + (insertBefore P S i).toList.length + 1) (blockOff P S next)
       | some (.noop next) =>
           exitChain P (insertAfter P S i).toList
             (blockOff P S i + (insertBefore P S i).toList.length + 1) (blockOff P S next)
       | some (.ifz _ z nz) =>
           let z0 := blockOff P S i + (insertBefore P S i).toList.length + 1
           let n0 := z0 + (insertEdge P S i z).toList.length
           exitChain P (insertEdge P S i z).toList z0 (blockOff P S z) ++
             exitChain P (insertEdge P S i nz).toList n0 (blockOff P S nz)
       | _ => []))

/-- **The KRS LCM hoisting transform**, over an arbitrary valid LCM bundle `S`. Concatenates the
    per-node blocks; the entry is the entry node's block offset. -/
def transform (P : Program) (S : LcmSpec P) : Program :=
  { entry := blockOff P S P.entry,
    code  := ((List.range P.size).flatMap (block P S)).toArray,
    obs   := P.obs }

/-! ## Executable memoization of `transform` (compiled-only, proven equal)

Two recomputations make the reference `transform` roughly `O(n⁴)`:
* `blockOff P S i = ((range i).map (blockLen P S)).sum` is recomputed for every `i`/`next`/`z`/`nz`, so
  across the `flatMap` it re-runs `blockLen` `O(n²)` times; and
* `allExprs P` (the whole expression universe) is rebuilt from scratch inside every
  `compl`/`earliest`/`pass`/`tempFor`, i.e. inside every placement-set computation.

The fix is pure memoization — **no new analysis**: compute `allExprs P` (as `ae`, plus its list `AE`)
**once**, take prefix sums off a single `blockLen` list, and thread all of it through fast variants
`*F` that are the originals with `allExprs P`/`blockOff P S` abstracted to parameters. Every `*F` is
**defeq** to its original at `ae = allExprs P` / `AE = (allExprs P).toList` / `off = blockOff P S`, so
the equality proof is essentially the single offset lemma `off_memo_app`. `@[csimp]` swaps the compiled
`transform` for this version; the `def`s of `transform`/`block`/`blockOff`/`allExprs`/… are untouched,
so every proof in the development still refers to the original spec. -/

/-! ### `allExprs`- and `blockOff`-threaded copies of the `Transform` helpers

The `*F` copies of the placement helpers (`passF`/`complF`/`earliestF`/`latestNodeF`/…)
live in `LcmDefs`; the ones below extend the same `ae`-threading to the layout helpers and add
the `off` (memoized block-offset) parameter. -/
def latestOutF (P : Program) (ae : Assignments) (S : LcmSpec P) (i : Node) : Assignments :=
  match P.fetch i with
  | some (.assign _ _ next) => latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i next
  | some (.noop next)       => latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i next
  | some (.ifz _ z nz)      => Assignments.union (latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i z)
                                                 (latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i nz)
  | _                       => Assignments.empty

def insertBeforeF (P : Program) (ae : Assignments) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.inter (Assignments.sdiff (latestNodeF P ae S.ηₚ S.τₚ n) (latestOutF P ae S n)) (S.τᵤK n)

def insertAfterF (P : Program) (ae : Assignments) (S : LcmSpec P) (i : Node) : Assignments :=
  match P.fetch i with
  | some (.assign _ _ next) => Assignments.inter (latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i next) (S.τᵤK i)
  | some (.noop next)       => Assignments.inter (latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i next) (S.τᵤK i)
  | _ => Assignments.empty

def insertEdgeF (P : Program) (ae : Assignments) (S : LcmSpec P) (i j : Node) : Assignments :=
  Assignments.inter (latestEdgeF P ae S.πₐ S.ηₐ S.ηₚ i j) (S.τᵤK i)

def recoverableF (P : Program) (ae : Assignments) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.union (S.πᵤK n) (insertBeforeF P ae S n)

def tempForF (P : Program) (AE : List Expr) (e : Expr) : Var := freshN P (AE.idxOf e)

def insChainF (P : Program) (AE : List Expr) (m : List Expr) (s0 : Nat) : List Cmd :=
  m.zipIdx.map (fun x => Cmd.assign (tempForF P AE x.1) x.1 (s0 + x.2 + 1))

def exitChainF (P : Program) (AE : List Expr) (m : List Expr) (start target : Nat) : List Cmd :=
  m.zipIdx.map (fun x => Cmd.assign (tempForF P AE x.1) x.1
    (if x.2 + 1 == m.length then target else start + x.2 + 1))

def blockLenF (P : Program) (ae : Assignments) (S : LcmSpec P) (i : Node) : Nat :=
  (insertBeforeF P ae S i).toList.length + 1 +
    (match P.fetch i with
     | some (.assign _ _ _) => (insertAfterF P ae S i).toList.length
     | some (.noop _)       => (insertAfterF P ae S i).toList.length
     | some (.ifz _ z nz)   => (insertEdgeF P ae S i z).toList.length + (insertEdgeF P ae S i nz).toList.length
     | _                    => 0)

def ctrlCmdAtF (P : Program) (ae : Assignments) (AE : List Expr) (S : LcmSpec P) (off : Node → Nat) (i : Node) :
    Cmd :=
  match P.fetch i with
  | some (.assign x e next) =>
      let tgt := if (insertAfterF P ae S i).toList.isEmpty then off next
                 else off i + (insertBeforeF P ae S i).toList.length + 1
      if isNumbered e && (recoverableF P ae S i).contains e
      then Cmd.assign x (.atom (.var (tempForF P AE e))) tgt
      else Cmd.assign x e tgt
  | some (.ifz x z nz) =>
      let z0 := off i + (insertBeforeF P ae S i).toList.length + 1
      let n0 := z0 + (insertEdgeF P ae S i z).toList.length
      Cmd.ifz x
        (if (insertEdgeF P ae S i z).toList.isEmpty then off z else z0)
        (if (insertEdgeF P ae S i nz).toList.isEmpty then off nz else n0)
  | some (.noop next)  =>
      let tgt := if (insertAfterF P ae S i).toList.isEmpty then off next
                 else off i + (insertBeforeF P ae S i).toList.length + 1
      Cmd.noop tgt
  | _                  => Cmd.halt

def blockAtF (P : Program) (ae : Assignments) (AE : List Expr) (S : LcmSpec P) (off : Node → Nat) (i : Node) :
    List Cmd :=
  insChainF P AE (insertBeforeF P ae S i).toList (off i) ++
    (ctrlCmdAtF P ae AE S off i ::
      (match P.fetch i with
       | some (.assign _ _ next) =>
           exitChainF P AE (insertAfterF P ae S i).toList
             (off i + (insertBeforeF P ae S i).toList.length + 1) (off next)
       | some (.noop next) =>
           exitChainF P AE (insertAfterF P ae S i).toList
             (off i + (insertBeforeF P ae S i).toList.length + 1) (off next)
       | some (.ifz _ z nz) =>
           let z0 := off i + (insertBeforeF P ae S i).toList.length + 1
           let n0 := z0 + (insertEdgeF P ae S i z).toList.length
           exitChainF P AE (insertEdgeF P ae S i z).toList z0 (off z) ++
             exitChainF P AE (insertEdgeF P ae S i nz).toList n0 (off nz)
       | _ => []))

/-- Every fast helper collapses to its spec original once `ae`/`AE`/`off` are the real values. -/
theorem blockLenF_eq (P : Program) (S : LcmSpec P) : blockLenF P (allExprs P) S = blockLen P S := rfl

theorem blockAtF_eq (P : Program) (S : LcmSpec P) :
    blockAtF P (allExprs P) ((allExprs P).toList) S (blockOff P S) = block P S := rfl

/-- The memoized transform: `allExprs P` and the `blockLen` list are each evaluated **once**; every
    offset is a prefix sum over that list, and every placement set reuses the shared `ae`/`AE`. -/
def transformFast (P : Program) (S : LcmSpec P) : Program :=
  let ae   := allExprs P
  let AE   := ae.toList
  let lens := (List.range P.size).map (blockLenF P ae S)
  let off  : Node → Nat := fun i => if i ≤ P.size then (lens.take i).sum else blockOff P S i
  { entry := off P.entry,
    code  := ((List.range P.size).flatMap (blockAtF P ae AE S off)).toArray,
    obs   := P.obs }

theorem off_memo_app (P : Program) (S : LcmSpec P) (i : Node) :
    (if i ≤ P.size then (((List.range P.size).map (blockLen P S)).take i).sum
     else blockOff P S i) = blockOff P S i := by
  by_cases h : i ≤ P.size
  · rw [if_pos h, blockOff, ← List.map_take, List.take_range, Nat.min_eq_left h]
  · rw [if_neg h]

@[csimp] theorem transform_eq_transformFast : @transform = @transformFast := by
  funext P S
  simp only [transform, transformFast, blockLenF_eq, off_memo_app, blockAtF_eq]

end BaseLanguage.Analyses.LCM
