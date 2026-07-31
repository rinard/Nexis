-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.EvalCount
import BaseLanguage.LCM.NoReinsert

/-!
# Eval-count optimality (`srcContrib_S ≤ srcContrib_Place` for every safe placement)

`EvalCount.transform_evalCount` proves the transform's whole-run eval count of `e` equals the **source-side**
contribution sum `srcContrib P S e ⟨entry,σ⟩ ks`. This file bounds that sum below the contribution of *every
safe placement* — the literal KRS computational-optimality count.

It builds the **node-list view** of `srcContrib` (companion to `evalCount_eq_filter_runNodes`): the
source-side sum is a `map`/`sum` over the source run's node-path `runNodes`. Working over the explicit node
list (rather than the fuel recursion) is what makes the interval-counting comparison tractable.

`runNodes`/`srcContrib`/`blockContribution` are all projections of `step1` (`IR/Cost`) + `S` (placements).
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-- Edge-walk kept-ctrl count: `[ctrl at c.node computes e]` summed along the run's *steps* (matching the
    edge-indexed `srcContrib`, which likewise counts only at stepping nodes). -/
def keptCount (P : Program) (S : LcmSpec P) (e : Expr) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      match step1 P c with
      | .next c' => (if computesExpr (transform P S)
                        (blockOff P S c.node + (insertBefore P S c.node).toList.length) e then 1 else 0)
                      + keptCount P S e c' fuel
      | _        => 0

/-- Per-step recursion for `keptCount`. -/
theorem keptCount_next {P : Program} {S : LcmSpec P} {e : Expr} {c c' : Config} {fuel : Nat}
    (h : step1 P c = .next c') :
    keptCount P S e c (fuel + 1)
      = (if computesExpr (transform P S)
            (blockOff P S c.node + (insertBefore P S c.node).toList.length) e then 1 else 0)
        + keptCount P S e c' fuel := by
  show (match step1 P c with
        | .next c'' => (if computesExpr (transform P S)
                          (blockOff P S c.node + (insertBefore P S c.node).toList.length) e then 1 else 0)
                        + keptCount P S e c'' fuel
        | _ => 0) = _
  rw [h]

/-- `keptCount ≤` the (over-counting) `runNodes.filter computes` count (the edge-walk drops the terminal
    node, which the node-filter keeps). -/
theorem keptCount_le {P : Program} (S : LcmSpec P) (e : Expr) (c : Config) (ks : Nat) :
    keptCount P S e c ks
      ≤ ((runNodes P c ks).filter
          (fun n => computesExpr (transform P S)
            (blockOff P S n + (insertBefore P S n).toList.length) e)).length := by
  induction ks generalizing c with
  | zero => simp [keptCount, runNodes]
  | succ m ih =>
      cases hs : step1 P c with
      | next c' =>
          rw [keptCount_next hs, show runNodes P c (m + 1) = c.node :: runNodes P c' m from by simp [runNodes, hs],
              List.filter_cons]
          by_cases hc : computesExpr (transform P S)
              (blockOff P S c.node + (insertBefore P S c.node).toList.length) e
          · simp only [hc, if_pos, List.length_cons]; have := ih c'; omega
          · simp only [hc, Bool.false_eq_true, if_neg, not_false_iff]; have := ih c'; omega
      | halt => simp [keptCount, runNodes, hs]
      | fault => simp [keptCount, runNodes, hs]
      | stuck => simp [keptCount, runNodes, hs]

/-! ## The abstract interval-counting core (pure `List`, no operational deps)

The comparison `countS ≤ countP` does **not** lift pointwise (the transform may compute `e` at a node where a
rival placement does not, and vice versa — the placement frontier is non-monotone in the deferral). The KRS
argument is an **interval** count: split the path into segments delimited by kills of `e`; in each segment the
transform computes `e` **at most once** (no double-materialize) and **only if πᵤ** (laziness), while any
safe placement computes `e` **at least once** whenever the segment has a use (coverage). So per segment
`countS ≤ countP`, and since the segments partition the path, the global count follows.

These lemmas are the reduction skeleton: `filter` distributes over a segment partition, and a per-segment
`≤` sums to a global `≤`. The operational/spec content (per-segment-`≤1`, per-segment coverage) feeds
the per-segment hypothesis. Pure list algebra — no `step1`, no `S`. -/

/-- `filter`-length distributes over a `flatten` (segment partition): the count over the whole list is the
    sum of the per-segment counts. -/
theorem length_filter_flatten {α} (p : α → Bool) (segs : List (List α)) :
    ((segs.flatten).filter p).length = (segs.map (fun s => (s.filter p).length)).sum := by
  induction segs with
  | nil => rfl
  | cons s rest ih =>
      rw [List.flatten_cons, List.filter_append, List.length_append, ih, List.map_cons, List.sum_cons]

/-- **Per-segment `≤` sums to global `≤`.** If two counts compare per segment, they compare over the whole
    partitioned path. The interval-count reduction: prove `countS ≤ countP` segment by segment. -/
theorem length_filter_le_of_segments {α} {cS cP : α → Bool} (segs : List (List α))
    (h : ∀ s ∈ segs, (s.filter cS).length ≤ (s.filter cP).length) :
    ((segs.flatten).filter cS).length ≤ ((segs.flatten).filter cP).length := by
  rw [length_filter_flatten, length_filter_flatten]
  induction segs with
  | nil => exact Nat.le_refl 0
  | cons s rest ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add (h s (List.mem_cons_self ..)) (ih (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')))

/-- **The per-segment combiner** (per-segment `≤1` + coverage ⇒ segment `≤`). If the transform computes `e` at most once in
    a segment (`≤ 1`) and computes there only when a safe placement also does (`countS > 0 → countP > 0`),
    then `countS ≤ countP` in that segment: it is `0 ≤ countP`, or `1 ≤ countP` via coverage. -/
theorem seg_count_le {α} {cS cP : α → Bool} (s : List α)
    (h1 : (s.filter cS).length ≤ 1)
    (hcov : 0 < (s.filter cS).length → 0 < (s.filter cP).length) :
    (s.filter cS).length ≤ (s.filter cP).length := by
  rcases Nat.eq_zero_or_pos (s.filter cS).length with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have : (s.filter cS).length = 1 := Nat.le_antisymm h1 hpos
    rw [this]; exact hcov hpos

/-! ## Segment decomposition of the path (split at fresh-need boundaries)

The counting partitions the path into **fresh-need segments**, breaking *before* every boundary node (where
`b` holds — for LCM, `e ∉ πₐ(n)`, an anticipation gap: a kill, or a join where `e` is not anticipated-in). `segmentize` realizes the split;
`segmentize_flatten` recovers the path (so `length_filter_le_of_segments` applies); `segmentize_tail_not_b`
is the structural invariant the per-segment `≤1` consumes — within a segment, only the head may be a boundary,
every later node has `b = false` (so the within-segment discharge engine applies there). -/

/-- Prepend `x` to the first segment (or start a fresh one if there are none). -/
def consFirst {α} (x : α) : List (List α) → List (List α)
  | [] => [[x]]
  | s :: ss => (x :: s) :: ss

theorem consFirst_flatten {α} (x : α) (l : List (List α)) :
    (consFirst x l).flatten = x :: l.flatten := by
  cases l with
  | nil => rfl
  | cons s ss => rw [consFirst, List.flatten_cons, List.cons_append, List.flatten_cons]

theorem consFirst_ne_nil {α} (x : α) (l : List (List α)) (hl : ∀ s ∈ l, s ≠ []) :
    ∀ s ∈ consFirst x l, s ≠ [] := by
  cases l with
  | nil => intro s hs; simp [consFirst] at hs; subst hs; simp
  | cons t ss =>
      intro s hs; rw [consFirst] at hs
      rcases List.mem_cons.mp hs with h | h
      · subst h; simp
      · exact hl s (List.mem_cons_of_mem _ h)

/-- Split `l` into contiguous segments, breaking **before** every element where `b` is true (each segment
    after the first starts at a boundary `b y`). Non-head elements of a segment are all non-boundary. -/
def segmentize {α} (b : α → Bool) : List α → List (List α)
  | [] => []
  | [x] => [[x]]
  | x :: y :: xs =>
      if b y then [x] :: segmentize b (y :: xs)
      else consFirst x (segmentize b (y :: xs))

/-- Every segment produced by `segmentize` is non-empty. -/
theorem segmentize_ne_nil {α} (b : α → Bool) (l : List α) :
    ∀ s ∈ segmentize b l, s ≠ [] := by
  induction l using segmentize.induct b with
  | case1 => intro s hs; simp [segmentize] at hs
  | case2 x => intro s hs; simp [segmentize] at hs; subst hs; simp
  | case3 x y xs hby ih =>
      intro s hs
      rw [segmentize, if_pos hby] at hs
      rcases List.mem_cons.mp hs with h | h
      · subst h; simp
      · exact ih s h
  | case4 x y xs hby ih => rw [segmentize, if_neg hby]; exact consFirst_ne_nil x _ ih

/-- **The segments partition the path** — `flatten` recovers `l`, so the per-segment count lemmas apply. -/
theorem segmentize_flatten {α} (b : α → Bool) (l : List α) : (segmentize b l).flatten = l := by
  induction l using segmentize.induct b with
  | case1 => rfl
  | case2 x => rfl
  | case3 x y xs hby ih => rw [segmentize, if_pos hby, List.flatten_cons, ih, List.singleton_append]
  | case4 x y xs hby ih => rw [segmentize, if_neg hby, consFirst_flatten, ih]

/-- The first segment of `segmentize b (a :: rest)` starts at `a` (the segmentation preserves order). -/
theorem segmentize_head_head {α} (b : α → Bool) (a : α) (rest : List α) :
    ∀ s ss, segmentize b (a :: rest) = s :: ss → s.head? = some a := by
  intro s ss hseg
  have hfl := segmentize_flatten b (a :: rest)
  rw [hseg, List.flatten_cons] at hfl
  have hsne : s ≠ [] := segmentize_ne_nil b (a :: rest) s (hseg ▸ List.mem_cons_self ..)
  cases s with
  | nil => exact absurd rfl hsne
  | cons w s' => rw [List.cons_append] at hfl; injection hfl with hw _; rw [List.head?_cons, hw]

/-- **Structural invariant: within a segment, every non-head node is non-boundary** (`b z = false`). The
    head of each segment is where the fresh need starts; every later node continues the segment, so the
    within-segment discharge engine (`insertBefore_no_reinsert_single`, multi-succ via `insertBefore_multisucc_in_ue`) applies there. -/
theorem segmentize_tail_not_b {α} (b : α → Bool) (l : List α) :
    ∀ s ∈ segmentize b l, ∀ z ∈ s.tail, b z = false := by
  induction l using segmentize.induct b with
  | case1 => intro s hs; simp [segmentize] at hs
  | case2 x => intro s hs z hz; simp [segmentize] at hs; subst hs; simp at hz
  | case3 x y xs hby ih =>
      intro s hs z hz
      rw [segmentize, if_pos hby] at hs
      rcases List.mem_cons.mp hs with h | h
      · subst h; simp at hz
      · exact ih s h z hz
  | case4 x y xs hby ih =>
      rw [segmentize, if_neg hby]
      intro s hs z hz
      cases hseg : segmentize b (y :: xs) with
      | nil => rw [hseg, consFirst] at hs; simp at hs; subst hs; simp at hz
      | cons t ss =>
          rw [hseg, consFirst] at hs
          rcases List.mem_cons.mp hs with h | h
          · subst h
            simp only [List.tail_cons] at hz
            have htne : t ≠ [] := segmentize_ne_nil b (y :: xs) t (hseg ▸ List.mem_cons_self ..)
            have hth : t.head? = some y := segmentize_head_head b y xs t ss hseg
            cases t with
            | nil => exact absurd rfl htne
            | cons w t' =>
                rw [List.head?_cons, Option.some.injEq] at hth; subst hth
                rcases List.mem_cons.mp hz with hzy | hzt'
                · subst hzy; simpa using hby
                · exact ih (w :: t') (hseg ▸ List.mem_cons_self ..) z (by simpa using hzt')
          · exact ih s (hseg ▸ List.mem_cons_of_mem _ h) z hz

/-! ## The inserted-side `0/1` partition and within-segment `ηₚ`-maintenance

The per-block contribution is `[e∈insertBefore n] + [kept-ctrl n] + [e∈insertAfter n]`. The two *inserted* terms
are mutually exclusive (`insertBefore ⊥ insertAfter` via the `latestOut` partition), so they fold to a single
`0/1` indicator `cS n := decide (e ∈ insertBefore n ∨ e ∈ insertAfter n)` — the filterable form `seg_count_le`
needs. The maintenance lemma is the within-segment engine: once `e` has left `ηₚ` (after an insert), a
transparent + anticipated (`¬b`) step keeps it out — so it is never re-inserted before the next boundary. -/

/-- **The inserted sides are disjoint** (`insertBefore n ⊥ insertAfter n`). `insertBefore = (latestNode ∖ latestOut) ∩
    τᵤ` explicitly removes `latestOut`, and `insertAfter ⊆ latestOut` (both are `latestEdge` at `assign`/
    `noop`, `∅` otherwise) — so the two inserted indicators never both fire, making the inserted contribution
    `0/1` per node. -/
theorem insertBefore_disjoint_insertAfter {P : Program} {S : LcmSpec P} {n : Node} {e : Expr}
    (he : e ∈ insertBefore P S n) : e ∉ insertAfter P S n := by
  intro hin
  unfold insertBefore at he
  rw [Assignments.mem_inter, Assignments.mem_sdiff] at he
  apply he.1.2
  unfold latestOut
  unfold insertAfter at hin
  cases hf : P.fetch n with
  | none => rw [hf] at hin; exact absurd hin Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign x e0 nx => rw [hf] at hin; exact (Assignments.mem_inter.mp hin).1
      | noop nx => rw [hf] at hin; exact (Assignments.mem_inter.mp hin).1
      | ifz x z nz => rw [hf] at hin; exact absurd hin Std.HashSet.not_mem_empty
      | halt => rw [hf] at hin; exact absurd hin Std.HashSet.not_mem_empty

/-- **Within-segment `postp`-maintenance (uniform single/multi-successor).** If `e` has already left
    `ηₚ` at `c` and the step `c → c'` is *non-boundary* (`e ∈ πₐ(c)`, `c ≠ entry`), then
    `e ∉ ηₚ(c')`. From `Postponable.update`: `ηₚ(c') ⊆ earliest(c,c') ∪ (ηₚ(c) ∖ ue(c))`; the
    `earliest` disjunct is killed by `earliest_excludes_transferable` (transparent + anticipated-transferable),
    the other by the hypothesis `e ∉ ηₚ(c)`. This is the engine that prevents a second insert in a
    segment — it needs *no* successor-count split (the `Inv_step_multi` obstruction is only for the *first*,
    `e ∈ ηₚ`, materialization). -/
theorem notPostp_maintain {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hstep : Step P c c') (hne : c.node ≠ P.entry)
    (hpi : e ∈ S.πₐ c.node)
    (hnp : e ∉ S.ηₚ c.node) : e ∉ S.ηₚ c'.node := by
  intro hp
  have hup := S.isPostp.update c c' hstep e hp
  rw [Assignments.mem_union] at hup
  rcases hup with hearl | hdiff
  · exact earliest_excludes_transferable hne hpi hearl
  · exact hnp (Assignments.mem_sdiff.mp hdiff).1

/-- **The establish step (insert ⇒ `e` leaves `postp` at the successor).** At a *non-boundary* step
    (`e ∈ πₐ(c)`, `c ≠ entry`), if `e` is inserted at `c` (entry or exit) then `e ∉
    ηₚ(c')` — so it cannot be re-inserted downstream until the next boundary (combined with
    `notPostp_maintain`). The three insert shapes close from the engine: `insertAfter` via
    `insertAfter_postp_disjoint`; entry `insertBefore` at a single-successor (`noop`/`assign`) via
    `insertBefore_transp_notPostp_succ`; entry `insertBefore` at a branch (`ifz`) via `insertBefore_multisucc_in_ue`
    (the carry is a genuine `ue`, so the `ηₚ ∖ ue` branch of `update` is killed) + `earliest_excludes_
    transferable`. -/
theorem insert_notPostp_succ {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config} {e : Expr}
    (hstep : Step P c c') (hne : c.node ≠ P.entry)
    (hpi : e ∈ S.πₐ c.node)
    (hins : e ∈ insertBefore P S c.node ∨ e ∈ insertAfter P S c.node) :
    e ∉ S.ηₚ c'.node := by
  cases hstep with
  | @noop nd σ next hf =>
      rcases hins with hia | hie
      · exact insertBefore_transp_notPostp_succ S hS (Step.noop hf) rfl (Or.inl hf) hne
          (Assignments.mem_toList.2 hia) hpi
      · exact insertAfter_postp_disjoint S hie (Or.inr hf)
  | @assign nd σ x e0 next v hf hv =>
      rcases hins with hia | hie
      · exact insertBefore_transp_notPostp_succ S hS (Step.assign hf hv) rfl (Or.inr ⟨x, e0, hf⟩) hne
          (Assignments.mem_toList.2 hia) hpi
      · exact insertAfter_postp_disjoint S hie (Or.inl ⟨x, e0, hf⟩)
  | @ifzT nd σ x z nz hf hc =>
      have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
      have hia : e ∈ insertBefore P S nd := by
        refine hins.resolve_right (fun hie => ?_)
        unfold insertAfter at hie; rw [hf] at hie; exact Std.HashSet.not_mem_empty hie
      have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
      intro hp
      have hup := S.isPostp.update ⟨nd, σ⟩ ⟨z, σ⟩ (Step.ifzT hf hc) e hp
      rw [Assignments.mem_union] at hup
      rcases hup with hearl | hdiff
      · exact earliest_excludes_transferable hne hpi hearl
      · exact (Assignments.mem_sdiff.mp hdiff).2 hue
  | @ifzF nd σ x z nz hf hc =>
      have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
      have hia : e ∈ insertBefore P S nd := by
        refine hins.resolve_right (fun hie => ?_)
        unfold insertAfter at hie; rw [hf] at hie; exact Std.HashSet.not_mem_empty hie
      have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
      intro hp
      have hup := S.isPostp.update ⟨nd, σ⟩ ⟨nz, σ⟩ (Step.ifzF hf hc) e hp
      rw [Assignments.mem_union] at hup
      rcases hup with hearl | hdiff
      · exact earliest_excludes_transferable hne hpi hearl
      · exact (Assignments.mem_sdiff.mp hdiff).2 hue

/-- **At a non-boundary node, any insert implies `e ∈ postp`.** Entry inserts are `⊆ latestNode ⊆ postp`
    directly; an exit insert lands in `latestEdge`, whose `earliest` part is excluded by
    `earliest_excludes_transferable` (transparent + anticipated), leaving the `ηₚ ∖ ue` part. This is the
    fact that lets the boundary-counting induction charge a non-boundary insert against the `ηₚ` potential. -/
theorem cS_imp_postp {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr} (hstep : Step P c c')
    (hne : c.node ≠ P.entry) (hpi : e ∈ S.πₐ c.node)
    (hcs : e ∈ insertBefore P S c.node ∨ e ∈ insertAfter P S c.node) : e ∈ S.ηₚ c.node := by
  rcases hcs with hia | hie
  · exact latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))
  · cases hstep with
    | @noop nd σ next hf =>
        have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd next := by
          unfold insertAfter at hie; rw [hf] at hie; exact (Assignments.mem_inter.mp hie).1
        unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
        rcases hedge.1 with hearl | hdif
        · exact absurd hearl (earliest_excludes_transferable hne hpi)
        · exact (Assignments.mem_sdiff.mp hdif).1
    | @assign nd σ x e0 next v hf hv =>
        have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ nd next := by
          unfold insertAfter at hie; rw [hf] at hie; exact (Assignments.mem_inter.mp hie).1
        unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
        rcases hedge.1 with hearl | hdif
        · exact absurd hearl (earliest_excludes_transferable hne hpi)
        · exact (Assignments.mem_sdiff.mp hdif).1
    | @ifzT nd σ x z nz hf hc =>
        unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty
    | @ifzF nd σ x z nz hf hc =>
        unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty

/-- An exit insert forces `e ∉ postp` at the (unique) successor — `insertAfter ⊆ latestEdge` excludes
    `ηₚ(next)`. The boundary-step "establish" that needs no `pass`/`πₐ` hypothesis (so it works even
    where the source is a boundary). -/
theorem insertAfter_imp_notPostp_succ {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hstep : Step P c c') (hie : e ∈ insertAfter P S c.node) : e ∉ S.ηₚ c'.node := by
  cases hstep with
  | @noop nd σ next hf => exact insertAfter_postp_disjoint S hie (Or.inr hf)
  | @assign nd σ x e0 next v hf hv => exact insertAfter_postp_disjoint S hie (Or.inl ⟨x, e0, hf⟩)
  | @ifzT nd σ x z nz hf hc => unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty
  | @ifzF nd σ x z nz hf hc => unfold insertAfter at hie; rw [hf] at hie; exact absurd hie Std.HashSet.not_mem_empty

/-! ## Edge-indexed inserted counting (edge placement)

Under edge placement the per-step inserted indicator is `insertBefore c.node ∨ insertEdge(c.node, c'.node)`
(the taken edge, not the node-local `insertAfter`), counted by the edge-walk `cSCount`. The three semantic
helpers below are the edge versions of `insertBefore_disjoint_insertAfter` / `cS_imp_postp` /
`insertAfter_imp_notPostp_succ` / `insert_notPostp_succ`, and they *generalise* cleanly — `insertEdge(c,c') ⊆
latestEdge(c,c')` uniformly, so no per-`fetch` `ifz`-vacuity casing is needed. -/

/-- Edge disjointness: `insertBefore c.node ⊥ insertEdge(c.node, c'.node)` (the entry frontier subtracts
    `latestOut ⊇ latestEdge(c,c')`). -/
theorem insertBefore_disjoint_insertEdge {P : Program} {S : LcmSpec P} {c c' : Config} {e : Expr}
    (hstep : Step P c c') (he : e ∈ insertBefore P S c.node) : e ∉ insertEdge P S c.node c'.node := by
  intro hin
  unfold insertBefore at he
  rw [Assignments.mem_inter, Assignments.mem_sdiff] at he
  apply he.1.2
  have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node :=
    (Assignments.mem_inter.mp hin).1
  cases hstep with
  | @assign nd σ x e0 next v hf hv => simp only [latestOut, hf]; exact hedge
  | @noop nd σ next hf => simp only [latestOut, hf]; exact hedge
  | @ifzT nd σ x z nz hf hc => simp only [latestOut, hf]; exact Assignments.mem_union.mpr (Or.inl hedge)
  | @ifzF nd σ x z nz hf hc => simp only [latestOut, hf]; exact Assignments.mem_union.mpr (Or.inr hedge)

/-- Edge version of `cS_imp_postp`. -/
theorem cS_imp_postp_edge {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr} (hstep : Step P c c')
    (hne : c.node ≠ P.entry) (hpi : e ∈ S.πₐ c.node)
    (hcs : e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c'.node) : e ∈ S.ηₚ c.node := by
  rcases hcs with hia | hie
  · exact latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia))
  · have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node :=
      (Assignments.mem_inter.mp hie).1
    unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
    rcases hedge.1 with hearl | hdif
    · exact absurd hearl (earliest_excludes_transferable hne hpi)
    · exact (Assignments.mem_sdiff.mp hdif).1

/-- Edge version of `insertAfter_imp_notPostp_succ`: an edge insert forces `e ∉ postp c'`
    (`insertEdge ⊆ latestEdge(c,c') = _ ∖ ηₚ c'`). -/
theorem insertEdge_imp_notPostp_succ {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hie : e ∈ insertEdge P S c.node c'.node) : e ∉ S.ηₚ c'.node := by
  have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node :=
    (Assignments.mem_inter.mp hie).1
  unfold latestEdge at hedge; exact (Assignments.mem_sdiff.mp hedge).2

/-- Edge version of `insert_notPostp_succ`. -/
theorem insert_notPostp_succ_edge {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config} {e : Expr}
    (hstep : Step P c c') (hne : c.node ≠ P.entry)
    (hpi : e ∈ S.πₐ c.node)
    (hins : e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c'.node) :
    e ∉ S.ηₚ c'.node := by
  rcases hins with hia | hie
  · cases hstep with
    | @noop nd σ next hf =>
        exact insertBefore_transp_notPostp_succ S hS (Step.noop hf) rfl (Or.inl hf) hne
          (Assignments.mem_toList.2 hia) hpi
    | @assign nd σ x e0 next v hf hv =>
        exact insertBefore_transp_notPostp_succ S hS (Step.assign hf hv) rfl (Or.inr ⟨x, e0, hf⟩) hne
          (Assignments.mem_toList.2 hia) hpi
    | @ifzT nd σ x z nz hf hc =>
        have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
        have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
        intro hp
        have hup := S.isPostp.update ⟨nd, σ⟩ ⟨z, σ⟩ (Step.ifzT hf hc) e hp
        rw [Assignments.mem_union] at hup
        rcases hup with hearl | hdiff
        · exact earliest_excludes_transferable hne hpi hearl
        · exact (Assignments.mem_sdiff.mp hdiff).2 hue
    | @ifzF nd σ x z nz hf hc =>
        have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
        have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
        intro hp
        have hup := S.isPostp.update ⟨nd, σ⟩ ⟨nz, σ⟩ (Step.ifzF hf hc) e hp
        rw [Assignments.mem_union] at hup
        rcases hup with hearl | hdiff
        · exact earliest_excludes_transferable hne hpi hearl
        · exact (Assignments.mem_sdiff.mp hdiff).2 hue
  · exact insertEdge_imp_notPostp_succ S hie

/-- Edge-walk inserted count: `[insertBefore c.node ∨ insertEdge(c.node,c'.node)]` summed along the run. -/
def cSCount (P : Program) (S : LcmSpec P) (e : Expr) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      match step1 P c with
      | .next c' => (if e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c'.node then 1 else 0)
                      + cSCount P S e c' fuel
      | _        => 0

/-- Per-step recursion for `cSCount`. -/
theorem cSCount_next {P : Program} {S : LcmSpec P} {e : Expr} {c c' : Config} {fuel : Nat}
    (h : step1 P c = .next c') :
    cSCount P S e c (fuel + 1)
      = (if e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c'.node then 1 else 0)
        + cSCount P S e c' fuel := by
  show (match step1 P c with
        | .next c'' => (if e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c''.node then 1 else 0)
                        + cSCount P S e c'' fuel
        | _ => 0) = _
  rw [h]

/-! ## The S-side global bound — inserts ≤ boundaries (+ the initial held-potential)

`cS n := [e ∈ insertBefore n ∨ e ∈ insertAfter n]` (the `0/1` inserted indicator) and `bnd n := [n = entry ∨
e ∉ πₐ n]` (a fresh-need boundary: entry, a kill, or an anticipation gap). Along any
halting run the transform materializes `e` **at most once per boundary-delimited interval** — formally,
the number of inserts is at most the number of boundaries plus the initial held-potential `[e ∈ ηₚ]`.

This is the operational core of computational optimality (the "no double-materialize per interval" count),
proved by a single run-induction. Each insert is charged either to a boundary it follows or to the
`ηₚ`-potential it consumes: a non-boundary insert needs `e ∈ ηₚ` (`cS_imp_postp`) and discharges it
(`insert_notPostp_succ`), while `notPostp_maintain` keeps `e ∉ ηₚ` until the next boundary; an exit
insert at a boundary discharges the *next* interval's potential directly (`insertAfter_imp_notPostp_succ`),
which is what lets the count stay tight across kills. -/

/-- Number of inserted-`e` slots vs. boundary nodes along the run, the per-interval `≤ 1` count in
    aggregate form: `#inserts ≤ #boundaries + [e ∈ ηₚ(start)]`. -/
theorem cS_count_le_bnd {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) (e : Expr) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f →
    ∀ ks, run P c ks = (c_f, .next c_f) →
      cSCount P S e c ks
        ≤ ((runNodes P c ks).filter
            (fun n => decide (n = P.entry ∨ e ∉ S.πₐ n))).length
          + (if e ∈ S.ηₚ c.node then 1 else 0) := by
  intro c c_f hrun
  induction hrun with
  | @refl c0 =>
      intro hfin ks hks
      cases ks with
      | zero => simp [cSCount, runNodes]
      | succ k =>
          exfalso
          have hh : step1 P c0 = .halt := by
            unfold step1; rw [show P.fetch c0.node = some .halt from hfin]
          rw [show run P c0 (k + 1) = (c0, .halt) from by simp [run, hh]] at hks; simp at hks
  | @head c c1 cf hstep htail ih =>
      intro hfin ks hks
      have hstepf : step1 P c = .next c1 := step1_next_iff.mpr hstep
      cases ks with
      | zero =>
          exfalso
          rw [show run P c 0 = (c, .next c) from rfl] at hks
          have hcf : c = cf := ((Prod.mk.injEq _ _ _ _).mp hks).1
          subst hcf; simp only [Final] at hfin; cases hstep <;> simp_all
      | succ k =>
          have hk : run P c1 k = (cf, .next cf) := by
            rw [show run P c (k + 1) = run P c1 k from by simp [run, hstepf]] at hks; exact hks
          have ihk := ih hfin k hk
          have hrn : runNodes P c (k + 1) = c.node :: runNodes P c1 k := by simp [runNodes, hstepf]
          rw [cSCount_next hstepf, hrn]
          have hfc_bnd : (List.filter (fun n => decide (n = P.entry ∨ e ∉ S.πₐ n))
                (c.node :: runNodes P c1 k)).length
              = (if (c.node = P.entry ∨ e ∉ S.πₐ c.node) then 1 else 0)
                + (List.filter (fun n => decide (n = P.entry ∨ e ∉ S.πₐ n))
                    (runNodes P c1 k)).length := by
            rw [List.filter_cons]
            by_cases h : (c.node = P.entry ∨ e ∉ S.πₐ c.node) <;>
              simp [h, Nat.add_comm]
          rw [hfc_bnd]
          have hp1 : (if e ∈ S.ηₚ c1.node then 1 else 0) ≤ 1 := by split <;> omega
          have hp0 : (if e ∈ S.ηₚ c.node then 1 else 0) ≤ 1 := by split <;> omega
          by_cases hbnd : (c.node = P.entry ∨ e ∉ S.πₐ c.node)
          · -- BOUNDARY step: charge an edge insert to the next interval, an entry insert to `postp(c)`
            rw [if_pos hbnd]
            by_cases hcs : (e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c1.node)
            · rw [if_pos hcs]
              rcases hcs with hia | hie
              · rw [if_pos (latestNode_sub_postp S c.node e (insertBefore_sub_latestNode (Assignments.mem_toList.2 hia)))]
                omega
              · rw [if_neg (insertEdge_imp_notPostp_succ S hie)] at ihk; omega
            · rw [if_neg hcs]; omega
          · -- NON-BOUNDARY step: `c ≠ entry ∧ e ∈ πₐ(c)`; the no-reinsert engine applies
            rw [if_neg hbnd]
            have hne : c.node ≠ P.entry := fun h => hbnd (Or.inl h)
            have hpi : e ∈ S.πₐ c.node := by
              by_cases ht : e ∈ S.πₐ c.node
              · exact ht
              · exact absurd (Or.inr ht) hbnd
            by_cases hcs : (e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c1.node)
            · rw [if_pos hcs, if_pos (cS_imp_postp_edge S hstep hne hpi hcs)]
              rw [if_neg (insert_notPostp_succ_edge S hS wn hstep hne hpi hcs)] at ihk
              omega
            · rw [if_neg hcs]
              by_cases hpc : e ∈ S.ηₚ c.node
              · rw [if_pos hpc]; omega
              · rw [if_neg hpc]
                rw [if_neg (notPostp_maintain S hstep hne hpi hpc)] at ihk
                omega

/-! ## Decomposing `srcContrib` into the inserted (`0/1`, filterable) part + the shared kept-ctrl part

`blockContribution n = [e∈insertBefore n] + [ctrl computes e] + [e∈insertAfter n]`. The two inserted terms fold
to the single `0/1` indicator `cS n` (partition), and the middle term is the kept original computation `kept
n` — shared by every safe placement. So the `srcContrib` sum splits as
`(runNodes.filter cS).length + (runNodes.filter kept).length`. The first summand is exactly what
`cS_count_le_bnd` bounds; the second cancels against any safe placement (both keep the same un-hoistable
originals). -/

/-- The two edge-indexed inserted indicators fold to one (mutual exclusion via the `latestOut` partition). -/
theorem ins_indic_eq_edge {P : Program} {S : LcmSpec P} {c c' : Config} {e : Expr} (hstep : Step P c c') :
    (if e ∈ insertBefore P S c.node then 1 else 0) + (if e ∈ insertEdge P S c.node c'.node then 1 else 0)
      = (if (e ∈ insertBefore P S c.node ∨ e ∈ insertEdge P S c.node c'.node) then 1 else 0) := by
  by_cases hia : e ∈ insertBefore P S c.node
  · rw [if_pos hia, if_neg (insertBefore_disjoint_insertEdge hstep hia), if_pos (Or.inl hia)]
  · by_cases hie : e ∈ insertEdge P S c.node c'.node
    · rw [if_neg hia, if_pos hie, if_pos (Or.inr hie)]
    · rw [if_neg hia, if_neg hie, if_neg (by rintro (h | h); exact hia h; exact hie h)]

/-- **The `srcContrib` split.** The source-side contribution sum decomposes into the edge-walk
    inserted count `cSCount` (which `cS_count_le_bnd` bounds) plus the kept-ctrl count `keptCount` (the shared
    original computations). Per step, `blockContribution(c,c') = [cS(c,c')] + [ctrl computes]`. -/
theorem srcContrib_eq_inserted_kept {P : Program} (S : LcmSpec P) (e : Expr) (c : Config) (ks : Nat) :
    srcContrib P S e c ks = cSCount P S e c ks + keptCount P S e c ks := by
  induction ks generalizing c with
  | zero => rfl
  | succ m ih =>
      cases hs : step1 P c with
      | next c' =>
          have hstep : Step P c c' := step1_next_iff.mp hs
          rw [srcContrib_next hs, cSCount_next hs, keptCount_next hs, ih c']
          unfold blockContribution
          rw [← ins_indic_eq_edge hstep]; omega
      | halt => simp [srcContrib, cSCount, keptCount, hs]
      | fault => simp [srcContrib, cSCount, keptCount, hs]
      | stuck => simp [srcContrib, cSCount, keptCount, hs]

/-- **S-side capstone.** Along any halting source run, the source-side contribution sum is bounded
    by the number of fresh-need boundaries (`bnd`) plus the initial held-potential plus the shared kept-ctrl
    count. Combines `srcContrib_eq_inserted_kept` (the inserted/kept split) with `cS_count_le_bnd` (inserts
    `≤` boundaries) and `keptCount_le`. -/
theorem srcContrib_le {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) (e : Expr)
    {c c_f : Config} (hsteps : StepsH P c c_f) (hfin : Final P c_f)
    (ks : Nat) (hks : run P c ks = (c_f, .next c_f)) :
    srcContrib P S e c ks
      ≤ ((runNodes P c ks).filter
            (fun n => decide (n = P.entry ∨ e ∉ S.πₐ n))).length
        + (if e ∈ S.ηₚ c.node then 1 else 0)
        + ((runNodes P c ks).filter
            (fun n => computesExpr (transform P S)
              (blockOff P S n + (insertBefore P S n).toList.length) e)).length := by
  rw [srcContrib_eq_inserted_kept]
  have hcs := cS_count_le_bnd S hS wn e hsteps hfin ks hks
  have hkept := keptCount_le S e c ks
  omega

end BaseLanguage.Analyses.LCM
