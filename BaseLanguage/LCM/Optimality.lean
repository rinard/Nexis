-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness

/-!
# `LCM.Optimality` — optimality of the (1-extend) two-valued LCM transform

The placement realized by `Transform` (now the two-valued `Latestin`/`Latestout`, lifetime-optimal variant)
is **optimal** in two layered senses, both consumed from the *extremality* of the analysis bundle
(`isPostp.2`/`isUsedOut`), the same shape as PDCE `§5`, stated over `WellNormalized P`.

* **Lifetime optimality** (the headline — the *lazy* refinement that distinguishes LCM from busy code
  motion): among all computationally-optimal placements, temps live for the **shortest** interval (minimal
  register pressure). Mechanized here as `liveRegion_minimal`: the
  transform defers via `ηₚ` — the **greatest** valid deferral (`isPostp.2`) — so its live region (the
  abstract live range `πₐ ∖ deferral`) is contained in that of *every* competing computationally-optimal
  placement (any valid `Postponable` deferral). This is `isPostp.2` made precise; the placement realizes the
  full edge deferral because the transform materializes each edge insert directly on its branch edge
  (`insertEdge` / `ifz` edge chains), with no critical-edge splitting required.

* **Computational optimality** (every inserted computation is necessary): along any run from the entry, an
  expression the transform materializes is **anticipated** (`insertBefore`/`insertAfter` `⊆ πₐ` — no
  speculation, `insertBefore_down_safe`/`insertAfter_down_safe`), **not already available** (`ηₐ ∩ ηₚ = ∅`,
  threaded along the run from `ηₐ(entry)=∅` — no redundant recomputation, `insertBefore_nonredundant`), and
  **πᵤ downstream** (`∈ τᵤ` — no dead temp, `placement_nonisolated`). Capstone:
  `computation_necessary`. Since every computation is anticipated-and-non-available-and-demanded, *any*
  correct placement must compute it too, so the per-path eval count is minimal.

**Scope.** `liveRegion_minimal` proves the lifetime *domination* at the abstract live-range level
(`πₐ ∖ deferral` — the standard KRS abstract live range); `computation_necessary` proves every inserted
computation is necessary. The **measured layer** below closes the lifetime side literally: `pathLiveLen_le`
lifts `liveRegion_minimal` to a per-path live-range length that is `≤` that of *every* competing placement,
along *every* path (the KRS quantified form). The per-path *eval-count* `≤ every safe placement` (the
placement count is the non-monotone boundary of the deferral, so not a direct filter-lift — it needs the
placement-coverage argument) is proved operationally in `EvalCountHeadline`; the operational
register-liveness tie-in is outside this file. (The `ηₐ ∩ ηₚ = ∅` disjointness is a *joint* property of two
greatest ghosts — not a global fact, but it threads along realized runs exactly like `ηₚ ⊆ πₐ`.)
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## Lifetime optimality (the headline) -/

/-- The **live region** of a temp under a placement with deferral `d`: the nodes where `e` is materialized
    (no longer deferred, `e ∉ d n`) and still anticipated (`e ∈ πₐ n`). The abstract live range. -/
def liveRegion {P : Program} (S : LcmSpec P) (d : Node → Assignments) (n : Node) : Assignments :=
  Assignments.sdiff (S.πₐ n) (d n)

/-- **LIFETIME-OPTIMALITY (core).** The transform defers via `postp` (the greatest valid deferral), so its
    live region is contained in that of **every** computationally-optimal placement `g` (any valid
    `Postponable` deferral). Each temp lives for the shortest interval — minimal register pressure. -/
theorem liveRegion_minimal {P : Program} (S : LcmSpec P) (hS : Extremal S) (g : Node → Assignments)
    (hg : Postponable P S.πₐ S.ηₐ g) (n : Node) :
    Assignments.Subset (liveRegion S S.ηₚ n) (liveRegion S g n) := by
  intro e he
  rw [liveRegion, Assignments.mem_sdiff] at he ⊢
  exact ⟨he.1, fun hgn => he.2 (hS.ηₚ g hg n e hgn)⟩

/-- No valid computationally-optimal placement defers past `postp`: the transform's deferral cannot be
    beaten, so its live region is *minimal*, not merely ⊆. -/
theorem no_deferral_beats_postp {P : Program} (S : LcmSpec P) (hS : Extremal S) (g : Node → Assignments)
    (hg : Postponable P S.πₐ S.ηₐ g) {n : Node} {e : Expr}
    (hlive : e ∈ liveRegion S S.ηₚ n) : e ∉ g n := fun hgn =>
  (Assignments.mem_sdiff.mp hlive).2 (hS.ηₚ g hg n e hgn)

/-- The transform's entry placement sits **inside `postp`** (`insertBefore ⊆ latestNode ⊆ postp`): it materializes
    each temp at the `ηₚ` boundary, confirming the transform's deferral is indeed `ηₚ`. -/
theorem placement_within_postp {P : Program} (S : LcmSpec P) {n : Node} {e : Expr}
    (he : e ∈ (insertBefore P S n).toList) : e ∈ S.ηₚ n :=
  latestNode_sub_postp S n e (insertBefore_sub_latestNode he)

/-! ## Computational optimality (fragment: no dead/isolated temps) -/

/-- Every **entry**-materialized temp is used downstream (`∈ usedOut`) — no dead computation. -/
theorem insertBefore_nonisolated {P : Program} {S : LcmSpec P} {n : Node} {e : Expr}
    (he : e ∈ (insertBefore P S n).toList) : e ∈ S.τᵤ n :=
  (mem_insertBefore.mp he).2

/-- Every **exit**-materialized temp is used downstream (`∈ usedOut`) — no dead computation. -/
theorem insertAfter_nonisolated {P : Program} {S : LcmSpec P} {i : Node} {e : Expr}
    (he : e ∈ insertAfter P S i) : e ∈ S.τᵤ i := by
  unfold insertAfter at he
  cases hf : P.fetch i with
  | none => rw [hf] at he; exact absurd he Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign x e0 next => rw [hf, Assignments.mem_inter] at he; exact he.2
      | noop next => rw [hf, Assignments.mem_inter] at he; exact he.2
      | ifz x z nz => rw [hf] at he; exact absurd he Std.HashSet.not_mem_empty
      | halt => rw [hf] at he; exact absurd he Std.HashSet.not_mem_empty

/-- **Computational optimality (fragment): no isolated/dead temps.** Every materialized temp — at a node
    entry *or* exit — is πᵤ downstream (`∈ τᵤ`); the transform computes nothing that is never read. -/
theorem placement_nonisolated {P : Program} (S : LcmSpec P) {i : Node} {e : Expr} :
    (e ∈ (insertBefore P S i).toList → e ∈ S.τᵤ i) ∧ (e ∈ insertAfter P S i → e ∈ S.τᵤ i) :=
  ⟨insertBefore_nonisolated, insertAfter_nonisolated⟩

/-! ## Computational optimality (fragment: no speculation — every placement is down-safe)

Along any run that maintains the threaded `ηₚ ⊆ πₐ` invariant (`hpa`, established by the simulation),
every inserted computation is **anticipated** where placed — it is πᵤ on every continuation, so it is never
speculative/wasted. Entry: `insertBefore ⊆ latestNode ⊆ ηₚ ⊆[hpa] πₐ`. Exit: `edgeIns_sub_anti` (the `earliest`
part by `earliest_sub_anti`, the transparent carry by `hpa` + `isAnti.predict`). -/

/-- Every **entry**-inserted computation is anticipated (down-safe — no speculation). -/
theorem insertBefore_down_safe {P : Program} (S : LcmSpec P) {n : Node} {e : Expr}
    (hpa : Assignments.Subset (S.ηₚ n) (S.πₐ n)) (he : e ∈ (insertBefore P S n).toList) : e ∈ S.πₐ n :=
  hpa e (latestNode_sub_postp S n e (insertBefore_sub_latestNode he))

/-- Every **exit**-inserted computation is anticipated at the successor (down-safe — no speculation). -/
theorem insertAfter_down_safe {P : Program} (S : LcmSpec P) {c c' : Config} (hstep : Step P c c')
    (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node)) {e : Expr}
    (he : e ∈ insertAfter P S c.node) : e ∈ S.πₐ c'.node := by
  have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node := by
    cases hstep with
    | @assign nd σ x e0 next v hf hv => unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he; exact he.1
    | @noop nd σ next hf => unfold insertAfter at he; rw [hf, Assignments.mem_inter] at he; exact he.1
    | @ifzT nd σ x z nz hf hz => unfold insertAfter at he; rw [hf] at he; exact absurd he Std.HashSet.not_mem_empty
    | @ifzF nd σ x z nz hf hz => unfold insertAfter at he; rw [hf] at he; exact absurd he Std.HashSet.not_mem_empty
  exact edgeIns_sub_anti S hstep hpa hedge

/-- **Computational optimality (no wasted computation).** Combining the two fragments: along any run, every
    computation the transform inserts is **anticipated** (down-safe — πᵤ on every continuation, no
    speculation) AND **non-isolated** (πᵤ downstream, no dead temp). So the transform introduces no wasted
    evaluation. *(The full per-path eval-count *minimality* additionally needs non-redundancy — `ηₚ` is
    disjoint from `ηₐ`, a joint greatest-solution fact over two ghosts not expressible in the current
    abstract bundle — plus a CFG-path eval-count measure; those are the remaining "last mile", the same
    shape as the operational live-range tie-in for `liveRegion_minimal`.)* -/
theorem placement_no_waste {P : Program} (S : LcmSpec P) {c c' : Config} (hstep : Step P c c')
    (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node)) {e : Expr} :
    (e ∈ (insertBefore P S c.node).toList → e ∈ S.πₐ c.node ∧ e ∈ S.τᵤ c.node) ∧
    (e ∈ insertAfter P S c.node → e ∈ S.πₐ c'.node ∧ e ∈ S.τᵤ c.node) :=
  ⟨fun he => ⟨insertBefore_down_safe S hpa he, insertBefore_nonisolated he⟩,
   fun he => ⟨insertAfter_down_safe S hstep hpa he, insertAfter_nonisolated he⟩⟩

/-! ## Computational optimality (non-redundancy — no recomputation of an available expression)

`ηₐ` and `ηₚ` are **disjoint** (an available value is not being postponed) — so the transform never
re-materializes an expression that is already available, *along any run*. This was the missing third
fragment: with **down-safety** (no speculation), **non-isolation** (no dead temp), and **non-redundancy**
(no recompute), *every* computation the transform inserts is genuinely necessary, hence the per-path
eval-count is minimal. The disjointness is a *joint* property of two greatest ghosts, so it is not a global
fact, but it **threads along a realized run from the entry** (where `ηₐ(entry) = ∅`), exactly like the
`ηₚ ⊆ πₐ` invariant `hpa`. The step preservation closes in four cases purely from validity
(`de ⊆ availableOut`, `earliest ⊥ availableOut`, `de ⊆ ue`) except the carried case, which is the threaded hypothesis. -/

/-- One-step preservation of `avail ∩ postp = ∅`. -/
theorem avail_postp_disjoint_step {P : Program} (S : LcmSpec P) {c c' : Config} (hstep : Step P c c')
    (hd : ∀ e, e ∈ S.ηₐ c.node → e ∉ S.ηₚ c.node) :
    ∀ e, e ∈ S.ηₐ c'.node → e ∉ S.ηₚ c'.node := by
  intro e hav hp
  have hav' := S.isAvail.update c c' hstep e hav
  have hp' := S.isPostp.update c c' hstep e hp
  rw [Assignments.mem_union] at hav' hp'
  have earliest_not_avail : e ∈ earliest P S.πₐ S.ηₐ c.node c'.node →
      e ∈ availableOut P S.ηₐ c.node → False := by
    intro hearl hao
    unfold earliest at hearl; rw [Assignments.mem_inter, Assignments.mem_inter] at hearl
    have hnav := hearl.1.2; unfold compl at hnav
    exact (Assignments.mem_sdiff.mp hnav).2 hao
  rcases hav' with hde | hat
  · rcases hp' with hearl | hpu
    · exact earliest_not_avail hearl (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde)
    · exact (Assignments.mem_sdiff.mp hpu).2 (Assignments.mem_inter.mp hde).1
  · rcases hp' with hearl | hpu
    · exact earliest_not_avail hearl (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inr hat)
    · exact hd e (Assignments.mem_inter.mp hat).1 (Assignments.mem_sdiff.mp hpu).1

/-- Base: `avail ∩ postp = ∅` at the entry (`avail(entry) ⊆ ∅`). -/
theorem avail_postp_disjoint_entry {P : Program} (S : LcmSpec P) (e : Expr)
    (hav : e ∈ S.ηₐ P.entry) : e ∉ S.ηₚ P.entry := by
  have h := S.isAvail.seed e hav
  simp only [entrySeed, Assignments.empty] at h
  exact absurd h Std.HashSet.not_mem_empty

/-- Threading `avail ∩ postp = ∅` forward along a run. -/
theorem avail_postp_disjoint_thread {P : Program} (S : LcmSpec P) : ∀ {a c : Config}, StepsH P a c →
    (∀ e, e ∈ S.ηₐ a.node → e ∉ S.ηₚ a.node) → (∀ e, e ∈ S.ηₐ c.node → e ∉ S.ηₚ c.node) := by
  intro a c h
  induction h with
  | refl => intro hda; exact hda
  | head hstep _ ih => intro hda; exact ih (avail_postp_disjoint_step S hstep hda)

/-- **Non-redundancy (operational).** On any run from the entry, the transform does **not** materialize an
    already-available expression — `e ∈ ηₐ(c.node) ⇒ e ∉ insertBefore(c.node)` (since `insertBefore ⊆ latestNode ⊆
    ηₚ`, and `ηₐ ∩ ηₚ = ∅` along the run). No redundant recomputation. -/
theorem insertBefore_nonredundant {P : Program} (S : LcmSpec P) {σ : Store} {c : Config}
    (hrun : StepsH P ⟨P.entry, σ⟩ c) {e : Expr} (hav : e ∈ S.ηₐ c.node)
    (he : e ∈ (insertBefore P S c.node).toList) : False :=
  avail_postp_disjoint_thread S hrun (avail_postp_disjoint_entry S) e hav
    (latestNode_sub_postp S c.node e (insertBefore_sub_latestNode he))

/-- **COMPUTATIONAL OPTIMALITY (every inserted computation is necessary).** On any run from the entry, an
    expression the transform materializes at a node entry is **anticipated** (πᵤ on every continuation — no
    speculation), **not already available** (no redundant recomputation), and **πᵤ downstream** (no dead
    temp). So the transform computes nothing unnecessary; its per-path evaluation count is the minimum, since
    any correct placement must likewise compute every such anticipated, non-available, demanded expression.
    (The remaining gap to a literal "≤ every `P'`" statement is a CFG-path eval-count *measure* + the
    alternative-placement comparison — bookkeeping over this necessity core, the analogue of the operational
    live-range tie-in for `liveRegion_minimal`.) -/
theorem computation_necessary {P : Program} (S : LcmSpec P) {σ : Store} {c : Config}
    (hrun : StepsH P ⟨P.entry, σ⟩ c) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    {e : Expr} (he : e ∈ (insertBefore P S c.node).toList) :
    e ∈ S.πₐ c.node ∧ e ∉ S.ηₐ c.node ∧ e ∈ S.τᵤ c.node :=
  ⟨insertBefore_down_safe S hpa he,
   fun hav => insertBefore_nonredundant S hrun hav he,
   insertBefore_nonisolated he⟩

/-! ## The measured layer — per-path live-range, and the literal "≤ every P'" theorem

`Steps`/`StepsH` are `Prop` (no large elimination), so we measure over the **path as data**: a `List Node`
— the node-sequence of *any* execution. The per-path **live-range length** of a temp `h_e` under a placement
with deferral `d` is the number of path nodes where `h_e` is live (`e ∈ liveRegion S d n = πₐ n ∖ d n`).
Lifting the pointwise `liveRegion_minimal` by filter-monotonicity gives the literal KRS lifetime statement:
*along every path, the transform's live-range length for `h_e` is `≤` that under every computationally-optimal
placement.* (Holds for an arbitrary `List Node`, so it subsumes every real run.) -/

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

/-- The **per-path live-range length** of `h_e` under deferral `d`: path nodes where `h_e` is live. -/
def pathLiveLen {P : Program} (S : LcmSpec P) (d : Node → Assignments) (e : Expr) (path : List Node) : Nat :=
  (path.filter (fun n => decide (e ∈ liveRegion S d n))).length

/-- **LIFETIME OPTIMALITY (literal, per-path).** Along *every* path, the transform's live-range length for
    `h_e` is `≤` that under *every* computationally-optimal placement `g` (any valid `Postponable` deferral).
    Minimal live ranges — the lazy/lifetime-optimal property, in the KRS quantified form. -/
theorem pathLiveLen_le {P : Program} (S : LcmSpec P) (hS : Extremal S) (g : Node → Assignments)
    (hg : Postponable P S.πₐ S.ηₐ g) (e : Expr) (path : List Node) :
    pathLiveLen S S.ηₚ e path ≤ pathLiveLen S g e path :=
  length_filter_mono
    (fun _n hn => decide_eq_true (liveRegion_minimal S hS g hg _n e (of_decide_eq_true hn))) path

/-! ## Per-path eval-count — the bound that lifts here, and why the quantitative headline is operational

The per-path **eval count** of `e` is the number of path nodes where the transform materializes it
(`h_e := e`, i.e. `e ∈ insertBefore n`). What lifts cleanly (`pathEvalCount_le_demand`): the transform evaluates
`e` **only at demanded nodes** (`insertBefore ⊆ τᵤ`) — no evaluation at an undemanded point.

What does **not** lift by `length_filter_mono`, and exactly why (this is why the `≤ every P'` headline is
proved operationally in `EvalCountHeadline`, not by a `filter`-count lift here):
* **The placement frontier is non-monotone in the deferral.** A placement under deferral `d` computes `e` at
  `latestNode_d = d ∩ (ue ∪ ¬⋂_succ d)`. The transform uses `d = ηₚ` (greatest). But `latestNode_postp ⊄ latestNode_g`
  for a smaller admissible `g` (the `¬⋂_succ d` factor *flips* as `d` shrinks), so the `≤ every P'` count is
  **not** a `filter`-monotone lift the way `pathLiveLen_le`/`pathSinkDist_le` are.
* **Computational optimality is run-dependent.** Its content — *every evaluation is necessary* (anticipated ∧
  not-already-available ∧ demanded) — is `computation_necessary`, but the non-redundancy (`ηₐ ∩ ηₚ = ∅`)
  **threads along an actual run** and turns on *this-path* availability, which the `must`-`ηₐ` ghost does
  not capture. So unlike the *pointwise/unconditional* `liveRegion_minimal`, it cannot be packaged over a
  path-as-`List Node`; counting run-dependent evaluations needs a **`Type`-level instrumented trace** (`Steps`
  is `Prop` — no large elimination), plus a placement-coverage model for `P'`.

The *content* is proven pointwise here (`computation_necessary`: nothing wasted). The literal quantitative
`≤ every safe placement` is proved operationally in `EvalCountHeadline.lean`
(`transform_evalCount_le_safe`, axiom-clean, in the default build) via the `earliest`-crossing engine: the
cost-instrumented `Type`-level trace + placement-coverage (`PlCovers`) model, which admits the eager
placements the `bndN`-segmentation route excludes. This file only records why it is *not* a
`length_filter_mono` lift the way `pathLiveLen_le`/`pathSinkDist_le` are. -/

/-- The **per-path eval count** of `e`: path nodes where the transform materializes it. -/
def pathEvalCount {P : Program} (S : LcmSpec P) (e : Expr) (path : List Node) : Nat :=
  (path.filter (fun n => decide (e ∈ (insertBefore P S n).toList))).length

/-- **Eval count is confined to demand.** Along *every* path, the transform evaluates `e` at most as many
    times as there are nodes where `e` is demanded (`τᵤ`) — no evaluation at an undemanded point. -/
theorem pathEvalCount_le_demand {P : Program} (S : LcmSpec P) (e : Expr) (path : List Node) :
    pathEvalCount S e path ≤ (path.filter (fun n => decide (e ∈ S.τᵤ n))).length :=
  length_filter_mono
    (fun _n hn => decide_eq_true (insertBefore_nonisolated (of_decide_eq_true hn))) path

end BaseLanguage.Analyses.LCM
