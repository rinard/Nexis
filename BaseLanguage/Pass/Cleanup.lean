-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.Pass.Compact

/-!
# `Pass.Cleanup` — noop-elimination + index compaction

A late peephole on the CFG IR (run after PDCE, before codegen): it drops *bypassable* `noop` nodes,
renumbers the survivors densely, and rewrites every edge through the `noop`-chase + remap. Because the
backend emits one fixed-size block per node index (`nodePc i = i*B`), removing nodes directly shrinks the
emitted assembly. (Kept nodes = every in-range node except a `noop` whose chain reaches a non-`noop`; a
`noop` cycle is kept — see `droppable`. Unreachable non-`noop` nodes are left in place, which keeps the
transform's verification structural — no reachability traversal.)

**`noop` cycles are preserved.** A chain that loops back on itself (`while 1 {}`) is a divergent infinite
loop; collapsing it would turn divergence into a halt. `resolve` returns a node *on* the cycle, which is
kept, so divergence is preserved by construction.

Status: **verified** (axiom-clean, `Pass/CleanupCorrect.lean`) — `cleanup_wellFormed`, and full
behavioral preservation `cleanup_preserves_halt` / `_faults` / `_diverges`, plus `cleanup_codegen`
(end-to-end). It is spliced into `pipeline_to_asm` (step ④.5), so the whole verified path is
`codegen ∘ cleanup ∘ PDCE ∘ LCM ∘ normalize ∘ lower`. Run **by default** in `prophecyc`; `--no-clean`
skips it.
-/

namespace BaseLanguage
namespace Pass
namespace Cleanup

open Tac

/-- Follow a `noop` chain from `nd` for up to `fuel` steps; return the first non-`noop` node.
    A chain longer than the program is a `noop` cycle — this then returns a node on the cycle. -/
def chase (P : Program) : Nat → Node → Node
  | 0,        nd => nd
  | fuel + 1, nd =>
    match P.fetch nd with
    | some (.noop next) => chase P fuel next
    | _                 => nd

/-- Resolve a node to the real (non-`noop`) node its `noop` chain leads to, or a cycle node.
    Fuel `P.size` suffices: an acyclic `noop` chain has `< P.size` edges, so it terminates at a
    non-`noop`; a chain of `≥ P.size` `noop` steps must repeat a node, i.e. it is a cycle, and then
    `resolve` returns a `noop` node on that cycle. -/
def resolve (P : Program) (nd : Node) : Node := chase P P.size nd

/-- A node is *droppable* iff it is a `noop` whose chain leads to a non-`noop` node (so every edge into
    it can be redirected past it). A `noop` on a cycle (its chain stays on `noop`s) is **not** droppable
    — it is kept, so a divergent `noop` loop (`while 1 {}`) is preserved. -/
def droppable (P : Program) (nd : Node) : Bool :=
  match P.fetch nd with
  | some (.noop _) => match P.fetch (resolve P nd) with
                      | some (.noop _) => false
                      | _              => true
  | _              => false

/-- Cleanup's keep-predicate: drop bypassable `noop`s. -/
def cleanKeep (P : Program) (nd : Node) : Bool := !droppable P nd

/-- Kept nodes, in ascending original-index order (so the compacted program keeps program order):
    every in-range node except droppable `noop`s. A `Compact.keptList` instance. -/
def keptList (P : Program) : List Node := Compact.keptList (cleanKeep P) P

/-- New (compacted) index of a node's resolved representative. A `Compact.remap` instance (`rep = resolve`). -/
def remap (P : Program) (ks : List Node) (nd : Node) : Node := Compact.remap (resolve P) ks nd

/-- Rewrite an instruction's successor edges through resolve + remap. A `Compact.remapCmd` instance. -/
def remapCmd (P : Program) (ks : List Node) : Cmd → Cmd := Compact.remapCmd (resolve P) ks

/-- **Noop-elimination + index compaction** — the shared `Compact.compactBy` with `keep = !droppable`,
    `rep = resolve`. -/
def cleanup (P : Program) : Program := Compact.compactBy (cleanKeep P) (resolve P) P

/-! ## Structural facts (behaviour preservation is future work — see the header). -/

/-- `obs` is untouched. -/
theorem cleanup_obs (P : Program) : (cleanup P).obs = P.obs := rfl

/-- The compacted program has one node per kept node. -/
theorem cleanup_size (P : Program) : (cleanup P).size = (keptList P).length :=
  Compact.compactBy_size P

/-- The entry is the remapped (resolved) original entry. -/
theorem cleanup_entry (P : Program) : (cleanup P).entry = remap P (keptList P) P.entry := rfl

end Cleanup
end Pass
end BaseLanguage
