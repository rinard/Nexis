-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Cfg

/-!
# `Normalize.Constraints` — the CFG constraint predicates the optimizations require

The structural preconditions a verified optimization pass (PDCE / PRE) assumes, stated as simple
syntactic/graph predicates (no dataflow):

* `WellFormed` (from `IR.TAC`) — entry/successor range discipline; the PDCE precondition.
* `WellNormalized` — the 7-field normal-form bundle the PRE-optimality pipeline assumes.
* `FreshForN` / `Nonobs` — the per-pass fresh-temp-supply discipline (consumed, not preserved).

The constraint hierarchy phrases `entryUnused` directly
("the entry reads nothing") instead of via the optimizer's use-bitvector, and `FreshForN`'s supply is
a plain `Nat`-indexed stream rather than `Fin (ENum P).n → Var` — keeping everything dataflow-free.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

variable {P : Program}

/-- **DistinctSuccs**: no node has a duplicated successor (no degenerate `ifz x z z`). -/
def DistinctSuccs (P : Program) : Prop := ∀ nd, (succList P nd).Nodup

/-- **NoSelfRead**: no *compute* assignment reads its own def var. (A copy like `x := x` is fine; only
    numbered `una`/`bin` computes are constrained — that is what the optimizations need.) -/
def NoSelfRead (P : Program) : Prop :=
  ∀ {nd x e next}, P.fetch nd = some (.assign x e next) → isNumbered e = true →
    exprReadsVar e x = false

/-- **EntryNoIncoming**: nothing branches to the entry. -/
def EntryNoIncoming (P : Program) : Prop := ∀ m, P.entry ∉ succList P m

-- (`NoCriticalEdges` removed: LCM realizes edge placement directly via per-branch `ifz` edge chains, so
--  critical edges need not be eliminated — see `LCM/Transform.lean`.)

/-- **EntryUnused**: the entry instruction reads no variable. -/
def EntryUnused (P : Program) : Prop := ∀ instr, P.fetch P.entry = some instr → instrUsedVars instr = []

/-- **The CFG-normal-form bundle** the PRE-optimality pipeline assumes — the analogue of `WellFormed`,
    intended to be preserved by an optimization transform. `FreshForN`/`Nonobs` is the separate per-pass
    input (not a field; not preserved). -/
structure WellNormalized (P : Program) : Prop where
  /-- Range discipline: entry in range, successors in range. -/
  wf : WellFormed P
  /-- No compute reads its own def var (the `normalizeSelfRead` pre-pass establishes this). -/
  noSelfRead : NoSelfRead P
  /-- Successor lists are duplicate-free (the `deDeg` pre-pass). -/
  distinctSuccs : DistinctSuccs P
  /-- The entry has no incoming edges (the `prependEntry` pre-pass). -/
  entryNoIncoming : EntryNoIncoming P
  /-- Every node is forward-reachable from the entry. -/
  allReach : AllReachable P
  /-- The entry reads nothing (the `prependEntry` pre-pass inserts a `noop`). -/
  entryUnused : EntryUnused P

/-- **FreshForN P fresh** — the per-pass temp supply `fresh : Nat → Var` is fresh for `P`: read by no
    instruction (`unread`), defined by no instruction (`noClash`), and injective. Together `unread` +
    `noClash` say `fresh i ∉ vars(P)` for every `i`. (A plain `Nat`-indexed stream
    rather than a `Fin (ENum P).n → Var` supply — no expression numbering.) -/
structure FreshForN (P : Program) (fresh : Nat → Var) : Prop where
  unread  : ∀ {nd : Node} {instr : Cmd} (i : Nat),
              P.fetch nd = some instr → (fresh i) ∉ instrUsedVars instr
  noClash : ∀ {nd : Node} {instr : Cmd} (i : Nat),
              P.fetch nd = some instr → instrDefVar instr ≠ some (fresh i)
  inj     : Function.Injective fresh

/-- **Nonobs**: every supplied fresh variable is a temporary (non-observable). -/
def Nonobs (fresh : Nat → Var) : Prop := ∀ i, varIsOrig (fresh i) = false

end Normalize
end BaseLanguage
