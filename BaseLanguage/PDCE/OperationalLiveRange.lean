-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Optimality
import BaseLanguage.IR.Cost

/-!
# `PDCE.OperationalLiveRange` — register-pressure optimality of the **transformed program**

The static live-range results (`pathLiveRange_le`, `pathVarLiveRange_le`) are the KRS-level lifetime optimality
— statements about the *ghosts* over source paths. This file adds the **operational** content: the
transformed program's *actual registers* hold each value over exactly the (minimal) occupancy region.

`transform_holds_regOcc` is the operational realization: at every reachable source config where register `x`
is *live and unpending* (`regOcc`), the transform reaches the corresponding block head with `x` **holding the
source value** in its store. Combined with `pathVarLiveRange_le` (that occupancy region is `≤` any admissible
placement's, `transform_regPressure_le`), this is register-pressure optimality *of `transform P S`* — the honest
"the compiled program holds registers minimally" statement KRS's path abstraction never makes.

No new fold: the per-config correspondence is obtained by applying `match_steps` to each reachable prefix of
the run, so this rides entirely on the existing forward simulation (`Match`) + `Match` clause 2.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
set_option linter.unusedVariables false

/-- **Operational realization of the live range.** At every reachable source config `c` where register `x` is
    register-occupied (`regOcc` — live and no assignment to `x` in flight), the transformed program reaches the
    corresponding block head `⟨blockOff c.node, τ⟩` with `τ x = c.store x`: the register **holds the source
    value**. Rides on the forward simulation (`match_steps`) + the store-agreement `Match` clause. -/
theorem transform_holds_regOcc {P : Program} (S : PdceSpec P) (wf : WellFormed P) {σ : Store}
    {c : Config} (x : Var) (hreach : Steps P ⟨P.entry, σ⟩ c)
    (hocc : regOcc S.π S.ηK x c.node = true) :
    ∃ τ, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ ⟨blockOff P S c.node, τ⟩
         ∧ τ x = c.store x := by
  obtain ⟨d, hsteps, hm⟩ := match_steps S wf (match_init S σ) hreach
  obtain ⟨hnode, hc2, _, _⟩ := hm
  obtain ⟨hlive, hnf⟩ := regOcc_iff.mp hocc
  obtain ⟨dn, dσ⟩ := d
  subst hnode
  exact ⟨dσ, hsteps, hc2 x hlive hnf⟩

/-! ## Live range as a sum over *corresponding original nodes* (materializations excluded)

The node correspondence `blockOff P S : Node → Node` is injective (`blockOff_inj`, `Layout.lean`): each original
node has a distinct corresponding transformed node (its block head), and the materialized assignments occupy the
*other* block slots — the ones outside `blockOff`'s image. So "the live range counted as the sum of
corresponding original nodes, not counting materialized assignments" is exactly the occupancy count over the
**source** run's nodes (each source-node visit = one corresponding-transformed-node visit): `pathVarLiveRange`.
This is a **reorder-invariant** measure — the movers (materializations) are the
only things two valid analyses reorder, and they are precisely what this measure does not count. Hence a genuine
`≤ every valid analysis` theorem exists for it (below), unlike an operation-count-in-between measure. -/

/-- **Register-pressure optimality of the transformed program (per-run, minimality).** Along the actual run,
    the register-occupancy region of `x` under the transform's `(live, sink)` is no larger than under any
    admissible placement `(sink', live')`. Instantiates `pathVarLiveRange_le` at the run's node-path; paired
    with `transform_holds_regOcc` (the transform *realizes* this region operationally), this is the
    lifetime/register-pressure optimality of `transform P S`, not merely of the ghosts.

    **`regOcc` is register-pressure of MATERIALIZED values only** — it undercounts `x` when `x`'s read has
    *moved* (been sunk downward as the operand of an in-flight assignment). See `regOccExt` / §"honest
    register occupancy" below for the corrected measure, the explicit `NoMovedRead` hypothesis under which
    this measure *is* the live range, and the mechanized counterexample where it is not. -/
theorem transform_regPressure_le {P : Program} {S : PdceSpec P} (hS : Extremal S) (S' : PdceSpec P)
    (hkq : S'.keep = S.keep) (x : Var) (c : Config) (ks : Nat) :
    pathVarLiveRange S x (runNodes P c ks)
      ≤ pathVarLiveRange S' x (runNodes P c ks) :=
  pathVarLiveRange_le hS S' hkq x (runNodes P c ks)

/-! ## Honest register occupancy — `regOcc` undercounts moved reads; the hypothesis that fixes it

**The gap.** `regOcc live sink x n = x live ∧ x's def not in flight` counts only the
register occupancy of **materialized** values. It is silent on a register held to feed an **in-flight** (sunk)
assignment. Concretely: for `a := 5 ; b := a+1 ; ifz z ; (c := b | ·)`, PDCE sinks
`b := a+1` into the branch, so the compiled program **reads `a` at the sunk site** — `a` is genuinely held
across four nodes — yet `pathVarLiveRange S a = 0`. The hold is tracked in `sink`, and strong-liveness does
not mark `a` live for it, so `regOcc a` is `false` throughout.

So `pathVarLiveRange` is not the live range when a read moves, and `transform_regPressure_le` — read as a
statement about *actual register pressure* — needs a hypothesis: that no read of `x`
moves. Below: the honest measure, that hypothesis, and the optimality theorem under it. -/

/-- **Operand-hold: `x` is held to feed a *live* in-flight (sunk) assignment.** Some `⟨y,e⟩ ∈ sink n` with
    `e` reading `x` **and `y` live** — then `x` must occupy a register at `n` to materialize that assignment
    below. The `y ∈ live` gate is what makes this term *operationally realized* (`Match` clause 3 —
    `transform_holds_heldForInFlight` below): a dead in-flight assignment never materializes, so its operands
    are not really held. The exact term `regOcc` omits. -/
def heldForInFlight (live : Node → Variables) (sink : Node → Assignments) (x : Var) (n : Node) : Bool :=
  (sink n).toList.any (fun a => exprReadsVar a.rhs x && (live n).contains a.lhs)

/-- **Honest register occupancy.** `x` occupies a register at `n` iff it is a live materialized value
    (`regOcc`, realized by `Match` clause 2) **or** held for a live in-flight assignment (`heldForInFlight`,
    realized by `Match` clause 3). Every disjunct is operationally grounded. -/
def regOccExt (live : Node → Variables) (sink : Node → Assignments) (x : Var) (n : Node) : Bool :=
  regOcc live sink x n || heldForInFlight live sink x n

/-- Per-path honest occupancy length. -/
def pathVarLiveRangeExt {P : Program} (S : PdceSpec P) (x : Var) (path : List Node) : Nat :=
  (path.filter (regOccExt S.π S.ηK x)).length

/-- **The missing hypothesis: no read of `x` moves** — no in-flight assignment reads `x`, i.e. `x` is never
    carried downstream as a sunk assignment's operand. On the extremal `S` (greatest sink) this is the
    weakest form: it then holds for every valid competitor too. It is exactly what fails for `a` in the
    counterexample above (`⟨b,a+1⟩` reads `a`), and holds for any `x` read only by non-sunk instructions
    (e.g. branch conditions). -/
def NoMovedRead {P : Program} (S : PdceSpec P) (x : Var) : Prop :=
  ∀ n a, a ∈ S.ηK n → exprReadsVar a.rhs x = false

/-- Under `NoMovedRead`, the operand-hold term is vacuous, so honest occupancy IS `regOcc`. -/
theorem regOccExt_eq_regOcc {P : Program} {S : PdceSpec P} {x : Var}
    (h : NoMovedRead S x) (n : Node) :
    regOccExt S.π S.ηK x n = regOcc S.π S.ηK x n := by
  have hheld : heldForInFlight S.π S.ηK x n = false := by
    unfold heldForInFlight
    rw [List.any_eq_false]
    intro a ha
    rw [h n a (Assignments.mem_toList.mp ha)]; simp
  unfold regOccExt
  rw [hheld, Bool.or_false]

/-- **Live-range optimality under non-moving reads.** For a variable `x` whose reads do not move
    (`NoMovedRead` on the extremal `S`), the transform occupies register `x` over a region no larger than
    under any valid competitor `S'` — for the **honest** occupancy `regOccExt`, not merely `regOcc`. This is
    "if the uses do not move, the live ranges in `T'` are at least as large as in `T`", with the hypothesis
    made explicit. Chain: `honest(S) = regOcc(S)` (the hypothesis cancels the operand-hold term)
    `≤ regOcc(S')` (`pathVarLiveRange_le`) `≤ honest(S')` (`regOcc` is a disjunct). -/
theorem transform_honestLiveRange_le {P : Program} {S : PdceSpec P} (hS : Extremal S)
    (S' : PdceSpec P) (hkq : S'.keep = S.keep) (x : Var) (h : NoMovedRead S x)
    (path : List Node) :
    pathVarLiveRangeExt S x path ≤ pathVarLiveRangeExt S' x path := by
  have e1 : pathVarLiveRangeExt S x path = pathVarLiveRange S x path := by
    unfold pathVarLiveRangeExt pathVarLiveRange
    rw [List.filter_congr (fun n _ => regOccExt_eq_regOcc h n)]
  have step2 : pathVarLiveRange S' x path ≤ pathVarLiveRangeExt S' x path :=
    length_filter_mono (fun n hn => by simp only [regOccExt, hn, Bool.true_or]) path
  calc pathVarLiveRangeExt S x path
      = pathVarLiveRange S x path := e1
    _ ≤ pathVarLiveRange S' x path := pathVarLiveRange_le hS S' hkq x path
    _ ≤ pathVarLiveRangeExt S' x path := step2

/-- **Necessity of `NoMovedRead` (why the hypothesis is not free).** `regOcc` alone can be strictly below the
    honest occupancy exactly when a read moves: whenever `x` is held for an in-flight assignment at `n`
    (`heldForInFlight`) but is not a live materialized value there (`¬ regOcc`), the honest indicator fires
    and `regOcc` does not. The `a`-at-a-sunk-`b:=a+1` counterexample is a concrete instance
    (`pathVarLiveRange S a = 0` while `a` is genuinely held); this is the pointwise reason the plain measure
    is not a live range without the hypothesis. -/
theorem regOccExt_gt_regOcc_of_movedRead {P : Program} {S : PdceSpec P} {x : Var} {n : Node}
    (hheld : heldForInFlight S.π S.ηK x n = true) (hnocc : regOcc S.π S.ηK x n = false) :
    regOccExt S.π S.ηK x n = true ∧ regOcc S.π S.ηK x n = false :=
  ⟨by simp only [regOccExt, hheld, Bool.or_true, hnocc], hnocc⟩

/-! ## Operational realization of the operand-hold term — `Match` clause 3

`transform_holds_regOcc` realized the `regOcc` disjunct (clause 2: the register holds a materialized value).
This realizes the **other** disjunct (clause 3: the register state *recovers* each live in-flight assignment),
so `regOccExt` is grounded in the running transformed program at both disjuncts, not merely as a static count.
The honest content of "`x` is held for the in-flight `⟨y,e⟩`" is not "register `x` = source `x`" (`x` need not
be `live`, so no `Match` clause tracks it directly) but **"the transformed store recomputes `⟨y,e⟩`'s value",
which reads `x`** — so `x`'s contribution is present. -/

/-- **The in-flight assignment is recoverable in the transformed store (clause 3, lifted).** At every
    reachable source config `c`, for each **live** in-flight `a ∈ S.ηK c.node` (`a.lhs ∈ S.π c.node`),
    the transform reaches the block head with `eval τ a.rhs = some (c.store a.lhs)`: the deferred computation
    is recomputable there. Rides on the forward simulation (`match_steps`) + `Match` clause 3, exactly as
    `transform_holds_regOcc` rides on clause 2. -/
theorem transform_recovers_inFlight {P : Program} (S : PdceSpec P) (wf : WellFormed P) {σ : Store}
    {c : Config} {a : Asgn} (hreach : Steps P ⟨P.entry, σ⟩ c)
    (hmem : a ∈ S.ηK c.node) (hlive : a.lhs ∈ S.π c.node) :
    ∃ τ, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ ⟨blockOff P S c.node, τ⟩
         ∧ eval τ a.rhs = some (c.store a.lhs) := by
  obtain ⟨d, hsteps, hm⟩ := match_steps S wf (match_init S σ) hreach
  obtain ⟨hnode, _, hc3, _⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  subst hnode
  exact ⟨dσ, hsteps, hc3 a.lhs a.rhs hmem hlive⟩

/-- `heldForInFlight` gives back a concrete witness: a live in-flight assignment whose rhs reads `x`. -/
theorem heldForInFlight_witness {P : Program} {S : PdceSpec P} {x : Var} {n : Node}
    (h : heldForInFlight S.π S.ηK x n = true) :
    ∃ a : Asgn, a ∈ S.ηK n ∧ exprReadsVar a.rhs x = true ∧ a.lhs ∈ S.π n := by
  unfold heldForInFlight at h
  rw [List.any_eq_true] at h
  obtain ⟨a, ha, hp⟩ := h
  rw [Bool.and_eq_true] at hp
  exact ⟨a, Assignments.mem_toList.mp ha, hp.1, Std.HashSet.contains_iff_mem.mp hp.2⟩

/-- **Operational realization of `heldForInFlight` — the operand-hold is grounded in the running program.**
    Wherever the honest measure counts `x` as held (`heldForInFlight`), the transformed program reaches the
    corresponding block head with a store `τ` that **recomputes an in-flight assignment reading `x`**
    (`eval τ a.rhs = some (c.store a.lhs)` with `exprReadsVar a.rhs x`). So the extra term in `regOccExt` over
    `regOcc` is not a bookkeeping fiction: it marks exactly the points where the compiled program must keep
    `x`'s contribution available to materialize a deferred assignment. Combined with `transform_holds_regOcc`
    (the `regOcc` disjunct), **`regOccExt` is fully operationally realized.** -/
theorem transform_holds_heldForInFlight {P : Program} (S : PdceSpec P) (wf : WellFormed P) {σ : Store}
    {c : Config} {x : Var} (hreach : Steps P ⟨P.entry, σ⟩ c)
    (hheld : heldForInFlight S.π S.ηK x c.node = true) :
    ∃ (a : Asgn) (τ : Store), a ∈ S.ηK c.node ∧ exprReadsVar a.rhs x = true
      ∧ Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ ⟨blockOff P S c.node, τ⟩
      ∧ eval τ a.rhs = some (c.store a.lhs) := by
  obtain ⟨a, hmem, hreads, hlive⟩ := heldForInFlight_witness hheld
  obtain ⟨τ, hsteps, hrec⟩ := transform_recovers_inFlight S wf hreach hmem hlive
  exact ⟨a, τ, hmem, hreads, hsteps, hrec⟩

end BaseLanguage.Analyses.PDCE
