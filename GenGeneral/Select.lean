-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Lower

/-!
# `GenGeneral.Select` — principled quadrant/mode selection

`AnalysisIR → Res Quadrant`: the 2-bit projection `(mode, direction, extremal) → Quadrant` (a lookup,
not a shape match), with a **fail-fast diagnostic on an inconsistent frame** (the totality contract — a
frame that cannot map to exactly one quadrant is a located error, never a silent default).

The consistency rules encode the Knaster–Tarski reading (`GHOST-SPEC-LANGUAGE.md §4/§9e`): a `must`
(greatest) ghost is clamped from above (a ceiling `hi`, never a floor), a `may` (least) ghost from below
(a floor `lo`, never a ceiling); a confluence reads exactly one foreign ghost and carries no clamp.
-/

namespace GenGeneral

/-- Select the emitted quadrant for an analysis, validating frame consistency. Returns a located error
    (blaming the ghost's implicit position via a synthetic `Pos`) on an inconsistent frame. -/
def selectQuadrant (a : AnalysisIR) : Res Quadrant := do
  let bad (msg : String) : Res Quadrant := err {} s!"ghost '{a.name}': {msg}"
  match a.mode with
  | .confluence =>
    if a.foreigns.length != 1 then
      bad s!"confluence must read exactly one foreign ghost, found {a.foreigns.length}"
    else if a.foreigns.head! == a.carried then
      -- a confluence reading itself (`self ⊆ self'` as a meet/join) is degenerate — almost always an
      -- authoring slip; reject rather than emit a self-referential `tMeet`/`tJoin`.
      bad "confluence must read a DISTINCT foreign ghost, not itself (self-referential meet/join)"
    else match a.clamp with
      | .none => .ok a.quadrant
      | _     => bad "confluence must not carry a floor/ceiling clamp"
  | .fixpoint =>
    -- must ⇏ floor ; may ⇏ ceiling (the polarity would contradict the extremal solution)
    match a.extremal, a.clamp with
    | .must, .lo _ => bad "a `must` (greatest) ghost cannot carry a floor clamp"
    | .may,  .hi _ => bad "a `may` (least) ghost cannot carry a ceiling clamp"
    | _, _ => .ok a.quadrant

/-- Kahn's algorithm on the foreign-dependency graph: repeatedly drop every ghost whose remaining deps are
    resolved; if the list is ever non-empty with no ready node, a cycle remains. Returns `true` on a cycle.
    (The bundle's `solve` threads each foreign's decode *before* the ghost that reads it, so the dep graph
    must be acyclic — a cyclic confluence like `a ⊆ b'`, `b ⊆ a'` has no valid emit order.) -/
partial def foreignCycle (deps : List (String × List String)) : Bool :=
  if deps.isEmpty then false
  else
    let ready := (deps.filter (·.2.isEmpty)).map (·.1)
    if ready.isEmpty then true   -- non-empty but nothing ready ⇒ a cycle
    else foreignCycle ((deps.filter (fun p => !ready.contains p.1)).map (fun p => (p.1, p.2.filter (fun d => !ready.contains d))))

/-- Select quadrants for a whole lowered program (first error wins). Also rejects a **cyclic** foreign
    dependency across ghosts (no topological solve order) — the totality contract at the program level. -/
def selectAll (as : List AnalysisIR) : Res (List (AnalysisIR × Quadrant)) := do
  let names := as.map (·.carried)
  -- self-loops (a confluence reading itself) are handled by `selectQuadrant`'s self-ref check with a
  -- clearer message; the cross-ghost cycle check is for genuine multi-node cycles (`a ⊆ b′, b ⊆ a′`).
  let deps := as.map (fun a => (a.carried, (a.foreigns.filter names.contains).filter (· != a.carried)))
  if foreignCycle deps then
    err {} "cyclic ghost dependency among foreigns — no topological solve order (e.g. a ⊆ b′, b ⊆ a′)"
  as.mapM (fun a => do pure (a, ← selectQuadrant a))

end GenGeneral
