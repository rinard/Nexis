-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.Behavior.Outcomes

/-!
# `LCM.Divergence` — a divergence-preserving mode for Lazy Code Motion

`Correctness.lean` proves observable preservation on **halting** runs. Divergence was left open, and not
by oversight: LCM *hoists*, so it can place an evaluation in front of a loop the source never leaves, and
if that evaluation faults a divergent source run becomes a faulting target run. That is a real defect of
the classical (KRS) transform, not an artifact of the proof.

The reason it is a defect is visible in the correctness proof itself. The only thing the simulation needs
about an inserted expression is that it **evaluates** (`match_step_core`'s `hnfB`/`hnfE`). The halting
proof discharges that from the *halting continuation*: an inserted expression is anticipated at its node,
and `antiNoFault` turns "anticipated + this run reaches `halt`" into "the source evaluates it too, so it
cannot fault". A divergent run offers no such continuation, so the certificate is simply unavailable.

Down-safety does not rescue it. `πₐ` is a **greatest** solution of the backward `must` constraints, and
its `check`/`predict` clauses are satisfiable all the way around a cycle whose body never computes `e`.
So "anticipated" here means *anticipated on every path that halts* — vacuously true along a divergent
path. This is precisely the anticipability subtlety CompCert's LCM validator checks for.

## The mode

This file supplies the **other** certificate: fault-freedom read off the expression syntactically
(`Expr.faultFree`, `IR/TAC.lean`). In this IR the only fault is `div`/`mod` by a zero divisor, so an
expression whose top-level operator is total evaluates in *every* store — no continuation needed. Gate the
inserted expressions on that (`SafeInserts`) and the same simulation runs on a divergent source run,
giving `transform_preserves_diverges`.

Both modes are the **same transform and the same simulation** (`match_step_core`); they differ only in
which no-fault certificate they supply. Nothing here weakens the classical mode — `transform_preserves_halt`
is untouched and still holds for every extremal bundle, with or without `SafeInserts`.

The trade is the honest one, and it is **per expression**: the divergence-preserving mode declines to hoist
a `div`/`mod` — exactly the class that can turn divergence into a fault — and hoists everything else
exactly as the classical mode does. `LCM/Mode.lean` makes the choice a compiler option (`--lcm=`).
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## The side condition -/

/-- **Fault-free insertion.** Along every step the machine can actually take, the expressions the
    transform inserts at the node entry and on the taken edge are `Expr.faultFree`, hence evaluate in
    every store. Purely a property of the *placement sets* — it says nothing about the ghosts.

    Indexing by `Step` rather than quantifying over all of `Node` matters twice over: it is exactly what
    the simulation consumes (only reachable nodes and real edges are ever executed), and it keeps the
    condition to in-range nodes and their real successors. In the divergence-preserving mode it is
    discharged outright by `safeInserts_faultFree`; it is stated separately so that the divergence proof
    never depends on *how* fault-freedom was obtained. -/
def SafeInserts (P : Program) (S : LcmSpec P) : Prop :=
  ∀ {c c' : Config}, Step P c c' →
    (∀ e ∈ (insertBefore P S c.node).toList, e.faultFree = true)
  ∧ (∀ e ∈ (insertEdge P S c.node c'.node).toList, e.faultFree = true)

/-! ## The step case, with the syntactic certificate -/

/-- **`match_step_div`** — `match_step_core` with the no-fault obligations discharged from
    `SafeInserts` instead of from a halting continuation. No `StepsH`/`Final` hypothesis appears, which
    is the whole point: this step case is available on a run that never terminates. -/
theorem match_step_div {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P)
    (hsafe : SafeInserts P S) {c c' d : Config} {M : Assignments}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hcov : Cov S c.node M) (hstep : Step P c c') :
    ∃ d', StepsPlus (transform P S) d d' ∧ Match P S c' d' (Mstep_edge S c.node c'.node M)
        ∧ Cov S c'.node (Mstep_edge S c.node c'.node M) :=
  match_step_core S hg wn hm hpa hcov hstep
    (fun e he => eval_ne_none_of_faultFree ((hsafe hstep).1 e he))
    (fun e he => eval_ne_none_of_faultFree ((hsafe hstep).2 e he))

/-! ## The simulation relation and the divergence engine -/

/-- The config relation fed to `diverges_of_stepsimG`: `Match` at some frontier `M`, together with the
    two invariants the step case needs — coverage of `M` and `ηₚ ⊆ πₐ` at the current node. Both are
    re-established across a step (`Cov_step_edge`, `postpSubAnti_step`), so the relation is preserved. -/
def DivRel (P : Program) (S : LcmSpec P) (c d : Config) : Prop :=
  ∃ M, Match P S c d M ∧ Cov S c.node M ∧ Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node)

/-- **The non-stuttering step simulation.** Each source step is matched by ≥ 1 target steps — the block
    always executes its floated control instruction — which is what keeps an infinite source run from
    collapsing to a finite target run. -/
theorem stepSimG_div {P : Program} (S : LcmSpec P) (hg : GateSound P S) (wn : WellNormalized P)
    (hsafe : SafeInserts P S) : StepSimG P (transform P S) (DivRel P S) := by
  rintro c c' d _hlt ⟨M, hm, hcov, hpa⟩ hstep
  obtain ⟨d', ⟨mid, hlead, htail⟩, hm', hcov'⟩ := match_step_div S hg wn hsafe hm hpa hcov hstep
  exact ⟨mid, d', hlead, htail, ⟨_, hm', hcov', postpSubAnti_step S hstep hpa⟩⟩

/-- **LCM preserves divergence, in the fault-free-insertion mode.** If `P` from its entry runs forever,
    so does `transform P S`. Fills the cell `transform_preserves_halt` leaves open, under the one extra
    hypothesis `SafeInserts` — which is exactly the hypothesis the classical mode cannot supply.

    Same transform, same bundle requirements (validity, `WellNormalized`) as the halting theorem; the
    only addition is `hsafe`. -/
theorem transform_preserves_diverges {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    (wn : WellNormalized P) (wf : WellFormed P) (hsafe : SafeInserts P S)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P S) ⟨blockOff P S P.entry, σ⟩ := by
  exact diverges_of_stepsimG (Rel := DivRel P S) (stepSimG_div S hg wn hsafe) wf wf.entry_lt
    ⟨Assignments.empty, match_init S σ, Cov_entry S hg, postpSubAnti_entry S⟩ hdiv

/-- **Divergence preservation under the materialization gate — from validity alone.** The third outcome
    cell, on the same footing as `transform_preserves_halt_mat` and `transform_preserves_faulting_mat`. -/
theorem transform_preserves_diverges_mat {P : Program} (S : LcmSpec P) (hm : S.gate = .materialized)
    (wn : WellNormalized P) (wf : WellFormed P) (hsafe : SafeInserts P S)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P S) ⟨blockOff P S P.entry, σ⟩ :=
  transform_preserves_diverges S (gateSound_materialized S hm) wn wf hsafe hdiv

/-- **Divergence preservation under the classical demand gate** — needs `Extremal S` and the
    `prependEntry` `noop` entry, exactly as its halt and fault counterparts do. -/
theorem transform_preserves_diverges_demand {P : Program} (S : LcmSpec P) (hd : S.gate = .demand)
    (hS : Extremal S) (wn : WellNormalized P) (wf : WellFormed P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne)) (hsafe : SafeInserts P S)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P S) ⟨blockOff P S P.entry, σ⟩ :=
  transform_preserves_diverges S (gateSound_demand S hd hS wn hen) wn wf hsafe hdiv

/-- The same statement phrased at the transformed program's own entry label. -/
theorem transform_preserves_diverges' {P : Program} (S : LcmSpec P) (hg : GateSound P S)
    (wn : WellNormalized P) (wf : WellFormed P) (hsafe : SafeInserts P S)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P S) ⟨(transform P S).entry, σ⟩ := by
  rw [transform_entry]
  exact transform_preserves_diverges S hg wn wf hsafe hdiv

/-! ## Discharging the side condition: per-expression, by construction

`SafeInserts` needs no decision procedure and no whole-program fallback. Every insert set is gated by
`τᵤK = τᵤ ∩ keep` (`LcmAdapter`), so aiming `keep` at `Expr.faultFree` makes *every* insertion fault-free
by construction — for **all** programs, including those that also contain `div`/`mod`. Such an expression
is simply left where the source computes it (and, because `recoverable` is filtered by the same predicate,
it is not rewritten to read a temp either), while every other expression is hoisted exactly as before. -/

/-- **The divergence-preserving mode satisfies its own side condition, unconditionally.** Immediate from
    the gate: an inserted expression lies in `τᵤK`, whose filter *is* `Expr.faultFree` here. -/
theorem safeInserts_faultFree {P : Program} (S : LcmSpec P) :
    SafeInserts P (S.withKeep Expr.faultFree) := by
  intro c c' _
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · exact (mem_τᵤK.mp (mem_insertBefore.mp he).2).2
  · rw [Assignments.mem_toList, insertEdge, Assignments.mem_inter] at he
    exact (mem_τᵤK.mp he.2).2

/-- **LCM preserves divergence in the fault-free-hoisting mode — with no side condition at all.**
    The `SafeInserts` hypothesis of `transform_preserves_diverges` is discharged by `safeInserts_faultFree`,
    so this holds for every program and every valid, extremal bundle. -/
theorem transform_preserves_diverges_faultFree {P : Program} (S : LcmSpec P)
    (hg : GateSound P (S.withKeep Expr.faultFree))
    (wn : WellNormalized P) (wf : WellFormed P)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P (S.withKeep Expr.faultFree))
      ⟨blockOff P (S.withKeep Expr.faultFree) P.entry, σ⟩ :=
  transform_preserves_diverges (S.withKeep Expr.faultFree) hg wn wf
    (safeInserts_faultFree S) hdiv

/-- …under the materialization gate, from validity alone. `keep` and `gate` are independent fields, so
    re-aiming the filter leaves the gate — and hence `gateSound_materialized` — untouched. -/
theorem transform_preserves_diverges_faultFree_mat {P : Program} (S : LcmSpec P)
    (hm : S.gate = .materialized) (wn : WellNormalized P) (wf : WellFormed P)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P (S.withKeep Expr.faultFree))
      ⟨blockOff P (S.withKeep Expr.faultFree) P.entry, σ⟩ :=
  transform_preserves_diverges_faultFree S
    (gateSound_materialized (S.withKeep Expr.faultFree) hm) wn wf hdiv

/-- …and under the classical demand gate, from extremality. -/
theorem transform_preserves_diverges_faultFree_demand {P : Program} (S : LcmSpec P)
    (hd : S.gate = .demand) (hS : Extremal S) (wn : WellNormalized P) (wf : WellFormed P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P (S.withKeep Expr.faultFree))
      ⟨blockOff P (S.withKeep Expr.faultFree) P.entry, σ⟩ :=
  transform_preserves_diverges_faultFree S
    (gateSound_demand (S.withKeep Expr.faultFree) hd (hS.withKeep _) wn hen) wn wf hdiv

end BaseLanguage.Analyses.LCM
