-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.EvalCountOpt
import BaseLanguage.LCM.LayoutEval

/-!
# `EvalCountPlace` — the lazy-aligned `IntervalCov` fragment of computational optimality

The Place lower bound `evalCount(transform) ≤ evalCount(P')` against the **lazy-aligned** class of safe
placements. `EvalCount.transform_evalCount` gives `evalCount(transform P S) e = srcContrib P S e`; this file
compares that count, along the source run, to any placement `pl` satisfying the per-interval coverage
`IntervalCov`.

The eval indicator is the *total* per-node indicator `cE n := (e ∈ insertBefore n ∨ e ∈ insertAfter n) ∨
keptCtrl n` (including the kept originals, not inserts-only); `cEb` is its per-edge form. The engine's
`ηₚ`-discharge applies uniformly to the kept control (a kept use has `e ∈ ηₚ` and discharges it at the
successor, exactly like an insert), giving `#cE ≤ 1` per fresh-need interval.

## What is proven here (axiom-clean, in the default build)

* `blockContribution_eq_cEb` — `blockContribution = #cEb` (the slot kinds are pairwise disjoint).
* `cE_le_pl` (**Theorem A**) — for any placement `pl` satisfying the per-interval coverage `IntervalCov`,
  `#cE ≤ #pl` along a halting source run, via the two-sided 2-bit interval potential. This is the
  genuinely run-dependent core of computational optimality (the count `≤ every covering placement`).

`IntervalCov P S e pl c ks sIns plF` is the **comparison condition**: along the run, every fresh-need (`bndN`)
interval in which the transform evaluates `e` also contains a `pl`-eval. `intervalCov_self` shows S itself
satisfies it (bound attained).

`IntervalCov` (whose boundaries `bndN` include **πₐ-gaps** `e∉πₐ`) is **strictly stronger** than
"`#cE ≤ #pl`", because the two-sided potential resets at every boundary (discarding pl-ahead credit). An
**eager** down-safe use-covering placement that computes `e` in an earlier `bndN`-interval than lazy S (across
an πₐ-gap) violates `IntervalCov` while computing the same total, so `cE_le_pl` here compares only against the
**lazy-aligned** class, not "every safe placement".

The full "≤ every safe placement" headline is `EvalCountHeadline.transform_evalCount_le_safe`
(axiom-clean, in the default build). It counts `earliest`-crossings directly (`cE_count_le_cross` +
`crossCount_le_pl`), which admits the eager placements the `bndN` route excludes; the results below are the
lazy-aligned fragment.

`cE`/`keptCtrl`/`pl` are projections of `computesExpr`/`S`/`step1`; the interval state carried in the count
induction is operational proof-bookkeeping (like `Cov`/`M`), not a new analysis.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-! ## `blockContribution = [cE]` (the three slot kinds are pairwise disjoint) -/

/-- A member of `allExprs` is a numbered (non-atom) expression. -/
theorem allExprs_isNumbered {P : Program} {e : Expr} (he : e ∈ allExprs P) : isNumbered e = true := by
  obtain ⟨n, _, hue⟩ := mem_allExprs_range.mp he
  obtain ⟨_, _, _, hn⟩ := mem_ue hue
  exact hn

/-- A realizable step has a valid fetch at its source. -/
theorem step_fetch {P : Program} {c c' : Config} (h : Step P c c') :
    ∃ instr, P.fetch c.node = some instr := by
  cases h with
  | noop hf => exact ⟨_, hf⟩
  | assign hf hv => exact ⟨_, hf⟩
  | ifzT hf hc => exact ⟨_, hf⟩
  | ifzF hf hc => exact ⟨_, hf⟩

/-- A numbered expression is not a bare variable atom — `tempFor`'s reads are copies, never computes. -/
theorem isNumbered_ne_atom {e : Expr} (he : isNumbered e = true) (v : Var) :
    (Expr.atom (.var v) == e) = false := by
  cases e with
  | atom a => simp [isNumbered] at he
  | una _ _ => rfl
  | bin _ _ _ => rfl

/-- **kept-ctrl ⇒ `e ∈ ue ∧ e ∉ recoverable`** (for numbered `e`). The floated control evaluates a numbered
    `e` only when the original `assign x e _` was **not** rewritten (so it is a genuine kept computation),
    which means the gate did not fire: `e ∉ recoverable`. (A rewritten control reads the fresh temp atom,
    which is not numbered, so it never matches a numbered `e`.) -/
theorem keptCtrl_imp {P : Program} {S : LcmSpec P} {n : Node} (hi : n < P.size) {e : Expr}
    (hnum : isNumbered e = true)
    (hk : computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e = true) :
    e ∈ ue P n ∧ e ∉ recoverable P S n := by
  rw [computesExpr_ctrl hi] at hk
  cases hf : P.fetch n with
  | none => simp only [hf] at hk; simp at hk
  | some instr =>
      cases instr with
      | assign x e0 next =>
          simp only [hf] at hk
          by_cases hg : (isNumbered e0 && (recoverable P S n).contains e0) = true
          · rw [if_pos hg] at hk; rw [isNumbered_ne_atom hnum] at hk; simp at hk
          · rw [if_neg hg] at hk
            have he : e0 = e := eq_of_beq hk
            subst he
            have hnum0 : isNumbered e0 = true := hnum
            have hue : e0 ∈ ue P n := by
              unfold ue; rw [hf]; simp only [hnum0, if_true]; exact Assignments.mem_singleton.2 rfl
            refine ⟨hue, ?_⟩
            intro hrec
            have hc : (recoverable P S n).contains e0 = true := Std.HashSet.contains_iff_mem.mpr hrec
            simp [hnum0, hc] at hg
      | ifz x z nz => simp only [hf] at hk; simp at hk
      | noop next => simp only [hf] at hk; simp at hk
      | halt => simp only [hf] at hk; simp at hk

/-- **`insertBefore ⊥ keptCtrl`.** A node whose floated control recomputes `e` is not also an `insertBefore` site:
    `e ∈ insertBefore ⇒ e ∈ recoverable`, but a kept (un-rewritten) control needs `e ∉ recoverable`. -/
theorem insertBefore_disjoint_keptCtrl {P : Program} {S : LcmSpec P} {n : Node} (hi : n < P.size) {e : Expr}
    (he : e ∈ insertBefore P S n) :
    computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e = false := by
  rcases Bool.eq_false_or_eq_true
      (computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e) with h | h
  · have hnum : isNumbered e = true := allExprs_isNumbered (insertBefore_mem_allExprs (Assignments.mem_toList.2 he))
    exact absurd (mem_recoverable.2 (Or.inr he)) (keptCtrl_imp hi hnum h).2
  · exact h

/-- **`insertEdge ⊥ keptCtrl`** (edge version, uniform — `insertEdge(n,j) ⊆ latestEdge(n,j)`, no `ifz`-vacuity
    casing). A kept control computes `e ∈ ue`, transparent ⇒ `e ∈ de ⊆ availableOut` ⇒ `e ∉ earliest`, and the
    carry part contradicts `e ∈ ue`. -/
theorem insertEdge_disjoint_keptCtrl {P : Program} {S : LcmSpec P} (wn : WellNormalized P)
    {n j : Node} (hi : n < P.size) {e : Expr} (he : e ∈ insertEdge P S n j) :
    computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e = false := by
  rcases Bool.eq_false_or_eq_true
      (computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e) with h | h
  case inr => exact h
  exfalso
  have hnum : isNumbered e = true := allExprs_isNumbered (insertEdge_mem_allExprs (Assignments.mem_toList.2 he))
  obtain ⟨hue, _⟩ := keptCtrl_imp hi hnum h
  have htransp : e ∈ pass P n := ue_sub_transp wn hue
  have hde : e ∈ de P n := Assignments.mem_inter.mpr ⟨hue, htransp⟩
  have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ n j := (Assignments.mem_inter.mp he).1
  unfold latestEdge at hedge; rw [Assignments.mem_sdiff, Assignments.mem_union] at hedge
  rcases hedge.1 with hear | hcarry
  · unfold earliest at hear; rw [Assignments.mem_inter, Assignments.mem_inter] at hear
    have hnav : e ∉ availableOut P S.ηₐ n := (Assignments.mem_sdiff.mp hear.1.2).2
    exact hnav (by unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde)
  · exact (Assignments.mem_sdiff.mp hcarry).2 hue

/-- **The per-node eval indicator** (node-local: `insertBefore ∨ insertAfter ∨ kept-ctrl`), for the
    `bndN`/`IntervalCov` path; the headline uses the edge indicator `cEb` below. -/
def cE (P : Program) (S : LcmSpec P) (n : Node) (e : Expr) : Bool :=
  decide (e ∈ insertBefore P S n ∨ e ∈ insertAfter P S n)
    || computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e

/-- **The per-edge total eval indicator.** `e` is evaluated on the step `n → next` iff it is materialized at
    `n`'s entry (`insertBefore`), on the taken edge (`insertEdge n next`), or recomputed by a kept control. -/
def cEb (P : Program) (S : LcmSpec P) (n next : Node) (e : Expr) : Bool :=
  decide (e ∈ insertBefore P S n ∨ e ∈ insertEdge P S n next)
    || computesExpr (transform P S) (blockOff P S n + (insertBefore P S n).toList.length) e

/-- **`blockContribution(n,next) = [cEb n next]`.** The three slot kinds (`insertBefore`,
    kept control, `insertEdge`) are pairwise disjoint, so the per-block contribution is the `0/1` indicator `cEb`. -/
theorem blockContribution_eq_cEb {P : Program} (S : LcmSpec P) (wn : WellNormalized P) {c c' : Config}
    (hstep : Step P c c') (hi : c.node < P.size) (e : Expr) :
    blockContribution P S c.node c'.node e = if cEb P S c.node c'.node e then 1 else 0 := by
  unfold blockContribution cEb
  by_cases ha : e ∈ insertBefore P S c.node
  · rw [insertBefore_disjoint_keptCtrl hi ha]
    have hb : e ∉ insertEdge P S c.node c'.node := insertBefore_disjoint_insertEdge hstep ha
    simp [ha, hb]
  · by_cases hb : e ∈ insertEdge P S c.node c'.node
    · rw [insertEdge_disjoint_keptCtrl wn hi hb]
      simp [ha, hb]
    · by_cases hk : computesExpr (transform P S) (blockOff P S c.node + (insertBefore P S c.node).toList.length) e = true
      · rw [hk]; simp [ha, hb]
      · rw [Bool.not_eq_true] at hk; rw [hk]; simp [ha, hb]

/-- **A use-node discharges `postp` at the successor**. `e ∈ ue ∧ pass ⇒
    e ∈ de ⊆ availableOut ⇒ e ∉ earliest`, and `e ∈ ue` kills the `ηₚ ∖ ue` branch of `Postponable.update`. -/
theorem ue_transp_notPostp_succ {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hstep : Step P c c') (hue : e ∈ ue P c.node) (htr : e ∈ pass P c.node) :
    e ∉ S.ηₚ c'.node := by
  intro hp
  have hde : e ∈ de P c.node := Assignments.mem_inter.mpr ⟨hue, htr⟩
  have hav : e ∈ availableOut P S.ηₐ c.node := Assignments.mem_union.mpr (Or.inl hde)
  have hnearl : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node := by
    intro he
    obtain ⟨h1, _⟩ := Assignments.mem_inter.mp he
    obtain ⟨_, hc⟩ := Assignments.mem_inter.mp h1
    exact (Assignments.mem_sdiff.mp hc).2 hav
  have hup := S.isPostp.update c c' hstep e hp
  rw [Assignments.mem_union] at hup
  rcases hup with hearl | hdiff
  · exact hnearl hearl
  · exact (Assignments.mem_sdiff.mp hdiff).2 hue

/-- `e ∈ insertBefore ⇒ n ≠ entry` (`postp(entry) = ∅`, so `latestNode(entry) = ∅`). -/
theorem insertBefore_ne_entry {P : Program} (S : LcmSpec P) {n : Node} {e : Expr}
    (he : e ∈ insertBefore P S n) : n ≠ P.entry := by
  intro hne
  have hp : e ∈ S.ηₚ n := latestNode_sub_postp S n e (insertBefore_sub_latestNode (Assignments.mem_toList.2 he))
  rw [hne] at hp
  have := S.isPostp.seed e hp
  simp only [entrySeed, Assignments.empty] at this
  exact Std.HashSet.not_mem_empty this

/-- **The uniform `cE`-establish** — a `cE`-node discharges `postp` at the successor, at *any* step (boundary
    or not). `insertAfter` via `insertAfter_imp_notPostp_succ`; entry-`insertBefore` via `insertBefore_transp_notPostp_succ`
    (transparent, non-entry, single-succ — branches have no `insertBefore` by `insertBefore_multisucc_in_ue`); kept-ctrl
    via `ue_transp_notPostp_succ`. This is what bounds `#cE ≤ 1` per fresh-need interval. -/
theorem cE_imp_notPostp_succ {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) {c c' : Config} {e : Expr}
    (hnum : isNumbered e = true) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hstep : Step P c c') (hce : cE P S c.node e = true) : e ∉ S.ηₚ c'.node := by
  have hi : c.node < P.size := fetch_lt (step_fetch hstep).choose_spec
  unfold cE at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · rcases hins with hia | hie
    · -- entry insert: e ∈ πₐ(c) (via ηₚ ⊆ πₐ), ≠ entry; dispatch on the step shape
      have hpi : e ∈ S.πₐ c.node := insertBefore_sub_anti S hpa hia
      have hne : c.node ≠ P.entry := insertBefore_ne_entry S hia
      cases hstep with
      | @noop nd σ next hf =>
          exact insertBefore_transp_notPostp_succ S hS (Step.noop hf) rfl (Or.inl hf) hne
            (Assignments.mem_toList.2 hia) hpi
      | @assign nd σ x e0 next v hf hv =>
          exact insertBefore_transp_notPostp_succ S hS (Step.assign hf hv) rfl (Or.inr ⟨x, e0, hf⟩) hne
            (Assignments.mem_toList.2 hia) hpi
      | @ifzT nd σ x z nz hf hc =>
          exfalso
          have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
          have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
          unfold ue at hue; rw [hf] at hue; exact Std.HashSet.not_mem_empty hue
      | @ifzF nd σ x z nz hf hc =>
          exfalso
          have hmulti : 2 ≤ (succList P nd).length := by rw [succList_eq hf]; simp [Cmd.succs]
          have hue : e ∈ ue P nd := insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia)
          unfold ue at hue; rw [hf] at hue; exact Std.HashSet.not_mem_empty hue
    · exact insertAfter_imp_notPostp_succ S hstep hie
  · obtain ⟨hue, _⟩ := keptCtrl_imp hi hnum hk
    exact ue_transp_notPostp_succ S hstep hue (ue_sub_transp wn hue)

/-- **`cE ⇒ e ∈ postp` at a non-boundary node** (the precondition lever). An insert is `⊆ postp` directly
    (`cS_imp_postp`); a kept use has `e ∈ ue ∖ πᵤ ⊆ latestNode ⊆ ηₚ` (`Used.check` — `e ∉ recoverable ⊇ πᵤ`). -/
theorem cE_imp_postp {P : Program} (S : LcmSpec P) {c c' : Config} {e : Expr}
    (hi : c.node < P.size) (hnum : isNumbered e = true) (hstep : Step P c c')
    (hne : c.node ≠ P.entry) (hpi : e ∈ S.πₐ c.node)
    (hce : cE P S c.node e = true) : e ∈ S.ηₚ c.node := by
  unfold cE at hce
  rw [Bool.or_eq_true, decide_eq_true_eq] at hce
  rcases hce with hins | hk
  · exact cS_imp_postp S hstep hne hpi hins
  · obtain ⟨hue, hnr⟩ := keptCtrl_imp hi hnum hk
    have hnused : e ∉ S.πᵤ c.node := fun h => hnr (mem_recoverable.2 (Or.inl h))
    have hlat : e ∈ latestNode P S.ηₚ S.τₚ c.node := by
      by_cases hl : e ∈ latestNode P S.ηₚ S.τₚ c.node
      · exact hl
      · exact absurd (S.isUsed.check c.node e (Assignments.mem_sdiff.mpr ⟨hue, hl⟩)) hnused
    exact latestNode_sub_postp S c.node e hlat

/-! ## Theorem A: `#cE ≤ #pl` for any per-interval-covering placement (2-bit run-induction)

The count carries a 2-bit interval state `(sIns, plF)` (has S / has the placement evaluated `e` since the
last fresh-need boundary) and proves the *two-sided* invariant `#cE + [sIns∧¬plF] ≤ #pl + [plF∧¬sIns]`. The
per-step telescopes (`place_step_telescope_2bit` interior, `place_step_telescope_bnd` boundary) are pure
Bool/Nat; the operational content is the debt invariant `sIns → e ∉ ηₚ` (maintained by the `cE`-engine)
which discharges the interior precondition `cE → ¬sIns`. The coverage `sIns → plF` at each boundary is
supplied by `IntervalCov`. -/

/-- The interior per-step amortized inequality (★4), 2-bit two-sided, under the no-2nd-insert precondition
    `cs → ¬sIns`. -/
theorem place_per_step_2bit (sIns plF cs pl : Bool) (hprec : cs = true → sIns = false) :
    (if cs then 1 else 0) + (if (sIns && !plF) then 1 else 0)
        + (if ((plF || pl) && !(sIns || cs)) then 1 else 0)
      ≤ (if pl then 1 else 0) + (if (plF && !sIns) then 1 else 0)
        + (if ((sIns || cs) && !(plF || pl)) then 1 else 0) := by
  revert hprec; cases sIns <;> cases plF <;> cases cs <;> cases pl <;> decide

/-- Interior telescope: (★4) + IH ⇒ the head-case goal. -/
theorem place_step_telescope_2bit (sIns plF cs pl : Bool) (Acs Apl : Nat)
    (hprec : cs = true → sIns = false)
    (hih : Acs + (if ((sIns || cs) && !(plF || pl)) then 1 else 0)
            ≤ Apl + (if ((plF || pl) && !(sIns || cs)) then 1 else 0)) :
    (if cs then 1 else 0) + Acs + (if (sIns && !plF) then 1 else 0)
      ≤ (if pl then 1 else 0) + Apl + (if (plF && !sIns) then 1 else 0) := by
  have := place_per_step_2bit sIns plF cs pl hprec
  omega

/-- Boundary telescope: at a `bnd` step the interval state RESETS to `(cE, pl)`; the just-closed interval's
    S-ahead is settled by coverage (`sIns → plF`). -/
theorem place_step_telescope_bnd (sIns plF cE pl : Bool) (Acs Apl : Nat)
    (hcov : sIns = true → plF = true)
    (hih : Acs + (if (cE && !pl) then 1 else 0) ≤ Apl + (if (pl && !cE) then 1 else 0)) :
    (if cE then 1 else 0) + Acs + (if (sIns && !plF) then 1 else 0)
      ≤ (if pl then 1 else 0) + Apl + (if (plF && !sIns) then 1 else 0) := by
  revert hcov hih
  cases sIns <;> cases plF <;> cases cE <;> cases pl <;> simp_all <;> omega

/-! ### Faithfulness lemmas -/

/-- **Fresh-need boundary** of `e` at node `n`: the entry, or an anticipation gap `e ∉ πₐ(n)` (a kill or a
    join where `e` is not anticipated-in). Between boundaries the transform materializes `e` at most once. -/
def bndN (P : Program) (S : LcmSpec P) (e : Expr) (n : Node) : Bool :=
  decide (n = P.entry ∨ e ∉ S.πₐ n)

/-- **Operational per-interval coverage.** Along the run from `c` (with incoming interval state `(sIns, plF)`),
    every maximal fresh-need interval in which the transform evaluates `e` (`sIns`) also contains a `pl`-eval
    (`plF`). The induction in `cE_le_pl` consumes the `sIns → plF` clause at each boundary. -/
def IntervalCov (P : Program) (S : LcmSpec P) (e : Expr) (pl : Node → Bool) :
    Config → Nat → Bool → Bool → Prop
  | _, 0, sIns, plF => sIns = true → plF = true
  | c, k+1, sIns, plF =>
      match step1 P c with
      | .next c' =>
          if bndN P S e c.node then
            (sIns = true → plF = true) ∧ IntervalCov P S e pl c' k (cE P S c.node e) (pl c.node)
          else
            IntervalCov P S e pl c' k (sIns || cE P S c.node e) (plF || pl c.node)
      | _ => sIns = true → plF = true

/-- **Theorem A — the Place lower bound (count).** Along any halting source run, the transform's `cE`-count
    of `e` is bounded by the `pl`-count of any per-interval-covering placement, via the two-sided 2-bit
    interval potential. Carried: the debt invariant `sIns → e ∉ ηₚ` (engine-maintained) and the threaded
    `ηₚ ⊆ πₐ`; consumed: `IntervalCov` (boundary coverage). -/
theorem cE_le_pl {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) {e : Expr}
    (hnum : isNumbered e = true) (pl : Node → Bool) :
    ∀ {c c_f : Config}, StepsH P c c_f → Final P c_f →
    ∀ ks, run P c ks = (c_f, .next c_f) →
    ∀ sIns plF, (sIns = true → e ∉ S.ηₚ c.node) →
      Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node) →
      IntervalCov P S e pl c ks sIns plF →
      ((runNodes P c ks).filter (fun n => cE P S n e)).length + (if sIns && !plF then 1 else 0)
        ≤ ((runNodes P c ks).filter pl).length + (if plF && !sIns then 1 else 0) := by
  intro c c_f hrun
  induction hrun with
  | @refl c0 =>
      intro hfin ks hks sIns plF hdebt hpa hcov
      cases ks with
      | zero =>
          simp only [runNodes, List.filter_nil, List.length_nil, Nat.zero_add]
          have : sIns = true → plF = true := hcov
          revert this; cases sIns <;> cases plF <;> simp_all
      | succ k =>
          exfalso
          have hh : step1 P c0 = .halt := by
            unfold step1; rw [show P.fetch c0.node = some .halt from hfin]
          rw [show run P c0 (k + 1) = (c0, .halt) from by simp [run, hh]] at hks; simp at hks
  | @head c c1 cf hstep htail ih =>
      intro hfin ks hks sIns plF hdebt hpa hcov
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
          have hi : c.node < P.size := fetch_lt (step_fetch hstep).choose_spec
          have hpa1 : Assignments.Subset (S.ηₚ c1.node) (S.πₐ c1.node) := postpSubAnti_step S hstep hpa
          have hrn : runNodes P c (k + 1) = c.node :: runNodes P c1 k := by simp [runNodes, hstepf]
          -- split each cons-filter length into a head indicator + the tail count
          have hfa : (List.filter (fun n => cE P S n e) (runNodes P c (k + 1))).length
              = (if cE P S c.node e then 1 else 0)
                + (List.filter (fun n => cE P S n e) (runNodes P c1 k)).length := by
            rw [hrn, List.filter_cons]; by_cases h : cE P S c.node e <;> simp [h, Nat.add_comm]
          have hfp : (List.filter pl (runNodes P c (k + 1))).length
              = (if pl c.node then 1 else 0) + (List.filter pl (runNodes P c1 k)).length := by
            rw [hrn, List.filter_cons]; by_cases h : pl c.node <;> simp [h, Nat.add_comm]
          rw [hfa, hfp]
          -- unfold IntervalCov at the head step
          rw [IntervalCov] at hcov
          simp only [hstepf] at hcov
          by_cases hbnd : bndN P S e c.node
          · -- BOUNDARY step: reset, consume coverage `sIns → plF`
            rw [if_pos hbnd] at hcov
            obtain ⟨hcovb, hcovrec⟩ := hcov
            have hdebt1 : cE P S c.node e = true → e ∉ S.ηₚ c1.node :=
              fun hce => cE_imp_notPostp_succ S hS wn hnum hpa hstep hce
            have ihk := ih hfin k hk (cE P S c.node e) (pl c.node) hdebt1 hpa1 hcovrec
            have hres := place_step_telescope_bnd sIns plF (cE P S c.node e) (pl c.node)
                ((runNodes P c1 k).filter (fun n => cE P S n e)).length
                ((runNodes P c1 k).filter pl).length hcovb ihk
            omega
          · -- NON-BOUNDARY step: accumulate, use the engine for the precondition + debt maintenance
            rw [if_neg hbnd] at hcov
            have hb3 : ¬(c.node = P.entry ∨ e ∉ S.πₐ c.node) := by
              have h := hbnd; unfold bndN at h
              exact fun hor => h (by rw [decide_eq_true_eq]; exact hor)
            have hne : c.node ≠ P.entry := fun h => hb3 (Or.inl h)
            have hpi : e ∈ S.πₐ c.node := by
              by_cases h : e ∈ S.πₐ c.node
              · exact h
              · exact absurd (Or.inr h) hb3
            have hprec : cE P S c.node e = true → sIns = false := by
              intro hce
              cases hsi : sIns with
              | false => rfl
              | true => exact absurd (cE_imp_postp S hi hnum hstep hne hpi hce) (hdebt hsi)
            have hdebt1 : (sIns || cE P S c.node e) = true → e ∉ S.ηₚ c1.node := by
              intro h
              rw [Bool.or_eq_true] at h
              rcases h with hsi | hce
              · exact notPostp_maintain S hstep hne hpi (hdebt hsi)
              · exact cE_imp_notPostp_succ S hS wn hnum hpa hstep hce
            have ihk := ih hfin k hk (sIns || cE P S c.node e) (plF || pl c.node) hdebt1 hpa1 hcov
            have hres := place_step_telescope_2bit sIns plF (cE P S c.node e) (pl c.node)
                ((runNodes P c1 k).filter (fun n => cE P S n e)).length
                ((runNodes P c1 k).filter pl).length hprec ihk
            omega

/-! ## Non-vacuity: the transform's own placement covers itself

The comparison class is non-empty: `pl = cE` satisfies `IntervalCov` trivially (S covers every interval it
evaluates in, by itself), so `cE_le_pl` instantiates to `#cE ≤ #cE`. Hence the lower bound is real, not
vacuous. -/

/-- `pl = cE` satisfies `IntervalCov` on the diagonal (`sIns = plF` is preserved, so `sIns → plF` always). -/
theorem intervalCov_self {P : Program} (S : LcmSpec P) (e : Expr) (c : Config) (ks : Nat) (b : Bool) :
    IntervalCov P S e (fun n => cE P S n e) c ks b b := by
  induction ks generalizing c b with
  | zero => exact fun h => h
  | succ k ih =>
      rw [IntervalCov]
      cases hs : step1 P c with
      | next c' =>
          simp only [hs]
          by_cases hbnd : bndN P S e c.node
          · rw [if_pos hbnd]; exact ⟨fun h => h, ih c' (cE P S c.node e)⟩
          · rw [if_neg hbnd]; exact ih c' (b || cE P S c.node e)
      | halt => simp only [hs]; exact fun h => h
      | fault => simp only [hs]; exact fun h => h
      | stuck => simp only [hs]; exact fun h => h

/-! ## Assembly (in `EvalCountHeadline`)

The run-level headline `evalCount(transform P S) e ≤ #pl` for every safe placement is
`EvalCountHeadline.transform_evalCount_le_safe` (the `earliest`-crossing, edge-indexed engine). `#pl` is the
placement's per-path eval count of `e` over the *source* node-path — the literal KRS computational-optimality
comparison. The per-node `cE`/`cE_le_pl`/`IntervalCov` machinery above is the abstract interval-count core,
under its class restriction. -/

end BaseLanguage.Analyses.LCM
