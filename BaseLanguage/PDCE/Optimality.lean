-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Correctness

/-!
# `PDCE.Optimality` — extremality as a comparison principle (KRS §5)

The correctness proof (`Correctness.lean`) needs only **validity** of the ghosts. This file consumes
their **extremality** (`Extremal S`: `.η` greatest, `.π` least) — the witnesses reserved for KRS-style
optimality — and turns them into comparison statements against an arbitrary *admissible* (valid)
alternative analysis.

We prove the **static / first-order** forms (cf. KRS PDCE, the sinking dual of Lazy Code Motion):

* **O1 (maximal sinking).** `sink` defers at least as far as any admissible delayability `sink'`
  (`sink' ⊆ sink`, `sink_maximal`); and — now in the **measured layer** below — `pathSinkDist_le` lifts this
  to the literal per-path form: along *every* path the transform sinks each assignment at least as far as any
  admissible placement.
* **O3 (maximal dead elimination).** Among placements over the same in-flight set, the transform —
  using the *least* faint-aware liveness — materializes (keeps) the **fewest** assignments at every
  node-entry and every split edge, so its eliminated set is maximal. Any valid liveness `live'` keeps a
  superset.

Caveat (KRS, and PDCE.md §5): these are **single-application** results for this extremal analysis.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-- **The transform's in-flight (deferred) set is the greatest admissible one.** Any valid delayability
    `sink'` defers no more than the bundle's `sink`, so the KRS placement sinks each assignment at least
    as far (latest placement). This is `Extremal.η` (`hS.η`) — the *greatest ⇒ latest* comparison principle. The
    per-path computation-count statement it underwrites needs a measured semantics. -/
theorem sink_maximal {P : Program} {S : PdceSpec P} (hS : Extremal S) {sink' : Node → Assignments}
    (h : Sink P sink') (n : Node) : Assignments.Subset (sink' n) (S.η n) :=
  hS.η sink' h n

/-! ## O3 — maximal dead-code elimination -/

/-- **The transform keeps the fewest variables live.** Any valid (faint-aware) liveness `live'` keeps at
    least as much as the bundle's least `live`. This is `Extremal.π` (`hS.π`) — the *least ⇒ smallest* comparison
    principle that drives maximal elimination. -/
theorem live_minimal {P : Program} {S : PdceSpec P} (hS : Extremal S) {live' : Node → Variables}
    (h : Live P live') (n : Node) : Variables.Subset (S.π n) (live' n) :=
  hS.π live' h n

/-- **Maximal dead elimination at a node entry.** Every assignment the transform materializes at node
    `n` is also materialized by the placement using any valid liveness `live'` over the same in-flight
    set (RHS = that placement's `matNode`). Hence the transform's kept set is minimal and its eliminated
    set maximal at every node. -/
theorem matNode_dead_optimal {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    {n : Node} {a : Asgn} (ha : a ∈ matNode P S n) :
    a ∈ liveFilter (Assignments.inter (S.η n) (blockedSet P n)) (S'.π n) := by
  rw [mem_matNode] at ha
  rw [mem_liveFilter, Assignments.mem_inter]
  exact ⟨⟨ha.1, ha.2.1⟩, hS.π S'.π S'.isLive n a.lhs ha.2.2⟩

/-- **Maximal dead elimination on a split edge.** Every assignment the transform materializes on the
    edge `p → s` is also materialized by the placement using any valid liveness `live'` over the same
    delayed set; so the transform's per-edge kept set is minimal. -/
theorem matEdge_dead_optimal {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    {p s : Node} {a : Asgn} (ha : a ∈ matEdge P S p s) :
    a ∈ liveFilter (Assignments.sdiff (delayedExit P S p) (S.η s)) (S'.π s) := by
  rw [mem_matEdge] at ha
  rw [mem_liveFilter, Assignments.mem_sdiff]
  exact ⟨⟨ha.1, ha.2.1⟩, hS.π S'.π S'.isLive s a.lhs ha.2.2⟩

/-! ## The measured layer — per-path sinking distance, and the literal "≥ every P'" form of O1

The dual of `LCM.Optimality`'s per-path live-range measure. `Steps` is `Prop` (no large elimination), so we
measure over the **path as data** (`List Node` — the node-sequence of any execution). The per-path **sinking
distance** of an assignment `a` under a delayability `d` is the number of path nodes where `a` is still
*in flight* (deferred, `a ∈ d n`). Lifting the pointwise `sink_maximal` by filter-monotonicity gives the
literal KRS statement: *along every path, the transform defers (sinks) each assignment **at least as far** as
under every admissible placement.* (Holds for an arbitrary `List Node`, subsuming every real run.) -/

/-- `filter` length is monotone under predicate implication. -/
theorem length_filter_mono {α} {p q : α → Bool} (h : ∀ a, p a = true → q a = true) :
    ∀ l : List α, (l.filter p).length ≤ (l.filter q).length
  | [] => Nat.le_refl 0
  | a :: t => by
      have ih := length_filter_mono h t
      by_cases hp : p a = true
      · simp only [List.filter_cons, hp, h a hp, if_true, List.length_cons]; omega
      · simp only [Bool.not_eq_true] at hp
        by_cases hq : q a = true
        · simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false, if_true,
            List.length_cons]; omega
        · simp only [Bool.not_eq_true] at hq
          simp only [List.filter_cons, hp, hq, Bool.false_eq_true, if_false]; exact ih

/-- The **per-path sinking distance** of `a` under delayability `d`: path nodes where `a` is still in flight. -/
def pathSinkDist (d : Node → Assignments) (a : Asgn) (path : List Node) : Nat :=
  (path.filter (fun n => decide (a ∈ d n))).length

/-- **O1, LITERAL (per-path maximal sinking).** Along *every* path, *every* admissible delayability `sink'`
    defers `a` no farther than the transform — `pathSinkDist sink' ≤ pathSinkDist sink`. The transform sinks
    each assignment as far as possible (latest placement), in the KRS quantified form. -/
theorem pathSinkDist_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (a : Asgn) (path : List Node) :
    pathSinkDist S'.η a path ≤ pathSinkDist S.η a path :=
  length_filter_mono
    (fun n hn => decide_eq_true (hS.η S'.η S'.isSink n a (of_decide_eq_true hn))) path

/-! ## O1+O3, live-range form — the direct dual of LCM's `liveRegion_minimal`

`pathSinkDist_le` measures the *deferral* region (`sink` only). The literal **live range** of the materialized
value is the region where it is **live but no longer in flight** — `a.lhs ∈ live n ∧ a ∉ sink n` — the exact
dual of LCM's `liveRegion = anti ∖ postp` (`LCM/Optimality.lean`). Where LCM holds `anti` fixed and varies the
deferral, PDCE minimizes on **both** ghosts at once: the transform uses the *greatest* `sink` (so `a ∉ sink` is
smallest) and the *least* `live` (so `a.lhs ∈ live` is smallest), hence its live range is contained in that of
**every** admissible placement `(sink', live')`. Same one-line filter-monotonicity as the other axes, now with
the demand side (`live`) folded into the measure. -/

/-- The **per-path live-range length** of `a` under a liveness `live` and delayability `sink`: path nodes
    where `a`'s value is **live and materialized** (`a.lhs ∈ live n`, and `a` no longer in flight `a ∉ sink n`). -/
def pathLiveRange (live : Node → Variables) (sink : Node → Assignments) (a : Asgn) (path : List Node) : Nat :=
  (path.filter (fun n => decide (a.lhs ∈ live n ∧ a ∉ sink n))).length

/-- **Live-range optimality (per-path minimal live range).** Along *every* path, the transform's live range
    for `a` is no longer than that under any valid competitor analysis `S'` — the direct dual of LCM's
    `liveRegion_minimal`. Minimizes on both ghosts: greatest `sink` (`Extremal.η`) ∧ least `live` (`Extremal.π`). -/
theorem pathLiveRange_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (a : Asgn) (path : List Node) :
    pathLiveRange S.π S.η a path ≤ pathLiveRange S'.π S'.η a path :=
  length_filter_mono
    (fun n hn => decide_eq_true (by
      obtain ⟨hlive, hsink⟩ := of_decide_eq_true hn
      exact ⟨hS.π S'.π S'.isLive n a.lhs hlive, fun hc => hsink (hS.η S'.η S'.isSink n a hc)⟩)) path

/-! ### Register-occupancy (variable-level) live range — the register-pressure measure

`pathLiveRange` is per-*assignment*. Register pressure is per-*variable* `x`: the register `x` is occupied by a
live value at `n` when `x` is live **and no assignment to `x` is in flight** (`∀ e, ⟨x,e⟩ ∉ sink n`) — the
exact condition under which the `Match` invariant forces the transform's store to hold `x`'s value (clause 2).
This is the register-occupancy region; the operational realization (`OperationalLiveRange.lean`) shows the
transform actually holds `x` over exactly this region along the run. -/

/-- **Register-occupancy predicate** (decidable Bool): `x` is live at `n` and no assignment to `x` is in
    flight (no member of `sink n` has lhs `x`). The `∀ e` "not in flight" is realized decidably as a
    `.toList.all` over the finite `sink n`. -/
def regOcc (live : Node → Variables) (sink : Node → Assignments) (x : Var) (n : Node) : Bool :=
  (live n).contains x && (sink n).toList.all (fun a => a.lhs != x)

/-- Semantic reading of `regOcc`: register `x` is live and unpending — the exact condition `Match` clause 2
    uses to force the transform's store to hold `x`'s value. -/
theorem regOcc_iff {live : Node → Variables} {sink : Node → Assignments} {x : Var} {n : Node} :
    regOcc live sink x n = true ↔ x ∈ live n ∧ ∀ e : Expr, (⟨x, e⟩ : Asgn) ∉ sink n := by
  unfold regOcc
  rw [Bool.and_eq_true, Std.HashSet.contains_iff_mem, List.all_eq_true]
  constructor
  · rintro ⟨hlive, hall⟩
    refine ⟨hlive, fun e hmem => ?_⟩
    have := hall ⟨x, e⟩ (Assignments.mem_toList.mpr hmem)
    simp at this
  · rintro ⟨hlive, hnf⟩
    refine ⟨hlive, fun a ha => ?_⟩
    have hmem : a ∈ sink n := Assignments.mem_toList.mp ha
    rw [bne_iff_ne]; intro heq; exact hnf a.rhs (by cases a; cases heq; exact hmem)

/-- The **per-path register-occupancy length** of variable `x` under analysis `S`: path nodes where `x` is
    live and no assignment to `x` is in flight (`regOcc S.π S.η x`). -/
def pathVarLiveRange {P : Program} (S : PdceSpec P) (x : Var) (path : List Node) : Nat :=
  (path.filter (regOcc S.π S.η x)).length

/-- **Register-pressure optimality (per-path, variable level).** The transform occupies register `x` over a
    region no larger than under any valid competitor analysis `S'`. Both ghosts: greatest `sink`, least
    `live`. -/
theorem pathVarLiveRange_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (x : Var) (path : List Node) :
    pathVarLiveRange S x path ≤ pathVarLiveRange S' x path :=
  length_filter_mono
    (fun n hn => by
      rw [regOcc_iff] at hn ⊢
      obtain ⟨hlive, hnf⟩ := hn
      exact ⟨hS.π S'.π S'.isLive n x hlive, fun e hc => hnf e (hS.η S'.η S'.isSink n ⟨x, e⟩ hc)⟩) path

/-! ## The execution-count optimality (O3) — the per-path dual of LCM's eval-count

The number of times the transform **executes** an assignment `a` along a path is the number of path nodes
where it materializes `a` (`a ∈ matNode n`) plus the split edges where it does (`a ∈ matEdge p s`). Unlike
LCM's eval-count — whose placement frontier is non-monotone in the deferral, forcing the run-dependent
`earliest`-crossing argument (`EvalCountHeadline.transform_evalCount_le_safe`) — PDCE's materialization
frontier is **monotone in the liveness** (`matNode`/`matEdge` gate by `liveFilter`, and `live` is *least*),
so the comparison lifts **directly by `length_filter_mono`**, exactly like `pathSinkDist_le`. This monotone /
non-monotone split between the two passes is itself a finding (`LCM.md §10`).

The comparison is against any placement that keeps the same maximal sinking but a valid (faint-aware)
liveness `live'` — i.e. any correct dead-code-elimination choice. The transform, using the *least* `live`,
executes `a` **at most as often** as every such placement, on every path. -/

/-- The **per-path execution count** of `a` at node entries: path nodes where the transform materializes it. -/
def pathExecCount {P : Program} (S : PdceSpec P) (a : Asgn) (path : List Node) : Nat :=
  (path.filter (fun n => decide (a ∈ matNode P S n))).length

/-- **O3, node form — per-path minimal executions.** Along *every* path, the transform executes `a` at node
    entries no more often than the placement using any valid liveness `live'` (over the same maximal sinking)
    — `matNode_dead_optimal` lifted by filter-monotonicity. The dual of `pathSinkDist_le`, and the per-path
    analogue (monotone case) of LCM's `transform_evalCount_le_safe`. -/
theorem pathExecCount_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (a : Asgn) (path : List Node) :
    pathExecCount S a path
      ≤ (path.filter (fun n =>
          decide (a ∈ liveFilter (Assignments.inter (S.η n) (blockedSet P n)) (S'.π n)))).length :=
  length_filter_mono
    (fun _ hn => decide_eq_true (matNode_dead_optimal hS S' (of_decide_eq_true hn))) path

/-- The **per-path execution count** of `a` on split edges: path edges where the transform materializes it. -/
def pathExecEdgeCount {P : Program} (S : PdceSpec P) (a : Asgn) (edges : List (Node × Node)) : Nat :=
  (edges.filter (fun e => decide (a ∈ matEdge P S e.1 e.2))).length

/-- **O3, edge form.** Along *every* path, the transform executes `a` on split edges no more often than any
    valid-liveness placement over the same delayed set — `matEdge_dead_optimal` lifted. -/
theorem pathExecEdgeCount_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (a : Asgn) (edges : List (Node × Node)) :
    pathExecEdgeCount S a edges
      ≤ (edges.filter (fun e =>
          decide (a ∈ liveFilter (Assignments.sdiff (delayedExit P S e.1) (S.η e.2)) (S'.π e.2)))).length :=
  length_filter_mono
    (fun _ he => decide_eq_true (matEdge_dead_optimal hS S' (of_decide_eq_true he))) edges

/-! ## Operational necessity — every kept assignment is live (no threading needed, unlike LCM)

PDCE's operational "no-waste" is **structural**, not threaded: `matNode`/`matEdge` gate materialization by
`liveFilter`, so every kept assignment's `lhs` is live (used downstream before redefinition). LCM needed a
*threaded* `avail ∩ postp = ∅` because non-redundancy is a joint property of two greatest forward ghosts;
PDCE's second ghost (`live`, backward-least) gates materialization directly — the dual is simpler. -/

/-- Every assignment the transform keeps at a node entry is **live** (necessary — used downstream). -/
theorem matNode_necessary {P : Program} {S : PdceSpec P} {n : Node} {a : Asgn}
    (ha : a ∈ matNode P S n) : a.lhs ∈ S.π n := (mem_matNode.mp ha).2.2

/-- Every assignment the transform keeps on a split edge is **live** (necessary — used downstream). -/
theorem matEdge_necessary {P : Program} {S : PdceSpec P} {p s : Node} {a : Asgn}
    (ha : a ∈ matEdge P S p s) : a.lhs ∈ S.π s := (mem_matEdge.mp ha).2.2

end BaseLanguage.Analyses.PDCE
