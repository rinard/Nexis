-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.Frontend.Ast

/-!
# `Behavior/Outcomes.lean` — outcome predicates + a fuel-monotonicity toolkit

Foundations for the **full-behavioral-preservation** proof of the optimizer-free compiler skeleton
(`codegen ∘ normalize ∘ lower`). Everything here is *new* and only *uses* the audited operational
semantics (`IR.TAC`, `Frontend.Ast`); nothing in `Semantics`/`Normalize`/`TAC.lean` is modified.

Two independent pieces:

* **IR outcomes** (`Semantics` namespace): `Halts`/`Faults`/`Diverges` on top of the *functional*
  interpreter `Semantics.run` (`TAC.lean`), mirroring `Asm`'s fuel-based defs, plus the IR
  **trichotomy** (exhaustive + mutually exclusive) proved from `run`/`step1` and `no_stuck_reachable`.
  These are the IR-side classifiers the plus-simulation proofs pin outcomes onto.

* **Source monotonicity** (`Ast` namespace): `evalS` fuel-monotonicity — more fuel never turns an
  `.ok`/`.fault` verdict into anything else (only `.timeout` is fuel-sensitive). This is what makes the
  source outcomes `Faults := ∃ fuel, .fault` and `Diverges := ∀ fuel, .timeout` well-defined.
-/

namespace BaseLanguage

/-! ## Source-side: `evalS` fuel-monotonicity -/

namespace Ast
open Tac Semantics

/-- **One loop iteration.** When the guard is true and the body runs to `σ'` with fuel `n`, one extra
    unit of fuel steps the loop to a re-entry at `σ'`. Stated as a fixed lemma so the `while`-headed
    loop-back call is over a *variable* fuel `n` — `simp` cannot re-unfold it, sidestepping the
    over-reduction that afflicts `simp [evalS]` when the loop-back sits at a successor fuel. -/
theorem evalS_while_iter {n : Nat} {c : Expr} {bd : Stmt} {σ σ' : Store} {bv : Val}
    (hc : evalE σ c = some bv) (hnz : ¬ (bv == 0) = true) (hb : evalS n bd σ = .ok σ') :
    evalS (n + 1) (.while c bd) σ = evalS n (.while c bd) σ' := by
  simp [evalS, hc, hnz, hb]

/-- **One-step fuel monotonicity.** If `evalS fuel s σ` is a *decided* verdict (not `.timeout`), one
    extra unit of loop-fuel leaves it unchanged. Only `.timeout` — "ran out of loop fuel" — is
    fuel-sensitive. Proved by `evalS.induct` (structural on `s`, fuel-decreasing on `while`). -/
theorem evalS_succ {fuel : Nat} {s : Stmt} {σ : Store} :
    evalS fuel s σ ≠ .timeout → evalS (fuel + 1) s σ = evalS fuel s σ := by
  induction fuel, s, σ using evalS.induct with
  | case1 fuel σ => intro _; simp only [evalS]                     -- skip
  | case2 fuel xv e σ bv heq => intro _; simp [evalS, heq]         -- assign, ok
  | case3 fuel xv e σ heq => intro _; simp [evalS, heq]            -- assign, fault
  | case4 fuel s1 s2 σ σmid hmid ih1 ih2 =>                        -- seq, first ok
      intro hne
      simp only [evalS, hmid] at hne ⊢
      have e1 := ih1 (by rw [hmid]; simp)
      rw [e1, hmid]
      exact ih2 hne
  | case5 fuel s1 s2 σ hfail ih1 =>                                -- seq, first not ok
      intro hne
      simp only [evalS] at hne ⊢
      cases hm : evalS fuel s1 σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault => rw [ih1 (by rw [hm]; simp), hm]
      | timeout => rw [hm] at hne; exact absurd rfl hne
  | case6 fuel c t e σ bv heq hz ihe =>                            -- ite, cond = 0 (else)
      intro hne; simp only [evalS, heq, hz] at hne ⊢; exact ihe hne
  | case7 fuel c t e σ bv heq hnz iht =>                           -- ite, cond ≠ 0 (then)
      intro hne; simp only [evalS, heq, hnz] at hne ⊢; exact iht hne
  | case8 fuel c t e σ heq => intro _; simp [evalS, heq]           -- ite, cond faults
  | case9 c bd σ =>                                                -- while, fuel 0 (timeout)
      intro hne; exact absurd (show evalS 0 (Stmt.while c bd) σ = Outcome.timeout by simp [evalS]) hne
  | case10 fuel c bd σ bv heq hz => intro _; simp [evalS, heq, hz] -- while, cond = 0 (exit)
  | case11 fuel c bd σ bv heq hnz σmid hbody ihb ihw =>            -- while, iterate
      intro hne
      have hb1 : evalS (fuel + 1) bd σ = .ok σmid := (ihb (by rw [hbody]; simp)).trans hbody
      have hR := evalS_while_iter heq hnz hbody          -- evalS (fuel+1) while σ = evalS fuel while σmid
      have hL := evalS_while_iter heq hnz hb1            -- evalS (fuel+2) while σ = evalS (fuel+1) while σmid
      rw [hL, hR]
      exact ihw (by rw [← hR]; exact hne)
  | case12 fuel c bd σ bv heq hnz hfail ihb =>                     -- while, body not ok
      intro hne
      simp only [evalS, heq, hnz] at hne ⊢
      cases hm : evalS fuel bd σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault => rw [ihb (by rw [hm]; simp), hm]
      | timeout => rw [hm] at hne; exact absurd rfl hne
  | case13 fuel c bd σ heq => intro _; simp [evalS, heq]           -- while, cond faults

/-- **Fuel monotonicity.** A decided verdict is stable under *any* fuel increase. -/
theorem evalS_mono {fuel fuel' : Nat} {s : Stmt} {σ : Store}
    (hle : fuel ≤ fuel') (hne : evalS fuel s σ ≠ .timeout) :
    evalS fuel' s σ = evalS fuel s σ := by
  obtain ⟨k, rfl⟩ := Nat.le.dest hle
  clear hle
  induction k with
  | zero => rfl
  | succ k ih =>
      have hik : evalS (fuel + k) s σ ≠ Outcome.timeout := by rw [ih]; exact hne
      rw [show fuel + (k + 1) = (fuel + k) + 1 by omega, evalS_succ hik, ih]

/-- If `s` halts at some fuel, it halts to the same store at any larger fuel. -/
theorem evalS_ok_mono {fuel fuel' : Nat} {s : Stmt} {σ σ' : Store}
    (h : evalS fuel s σ = .ok σ') (hle : fuel ≤ fuel') : evalS fuel' s σ = .ok σ' := by
  rw [evalS_mono hle (by rw [h]; exact Outcome.noConfusion), h]

/-- If `s` faults at some fuel, it faults at any larger fuel. -/
theorem evalS_fault_mono {fuel fuel' : Nat} {s : Stmt} {σ : Store}
    (h : evalS fuel s σ = .fault) (hle : fuel ≤ fuel') : evalS fuel' s σ = .fault := by
  rw [evalS_mono hle (by rw [h]; exact Outcome.noConfusion), h]

end Ast

/-! ## IR-side: outcome predicates on the functional interpreter `run` -/

namespace Semantics
open Tac

/-- The program run from `c` **halts** at configuration `cf` (a node sitting on `halt`). Carries the
    reached config because the halting store is the observable-bearing endpoint. Mirrors `Asm.Halts`. -/
def Halts (P : Program) (c cf : Config) : Prop := ∃ fuel, run P c fuel = (cf, .halt)

/-- The program run from `c` **faults** (`div`/`mod` by zero). Outcome-only — no observable. -/
def Faults (P : Program) (c : Config) : Prop := ∃ fuel cf, run P c fuel = (cf, .fault)

/-- The program run from `c` **diverges**: still running at every fuel. Mirrors `Asm.Diverges`. -/
def Diverges (P : Program) (c : Config) : Prop := ∀ fuel, ∃ cf, (run P c fuel).2 = .next cf

/-! ### Stability: terminals are preserved by extra fuel (mirrors `Asm.run_*_succ`) -/

theorem run_halt_succ {P : Program} {cf : Config} :
    ∀ (f : Nat) (c : Config), run P c f = (cf, .halt) → run P c (f + 1) = (cf, .halt) := by
  intro f
  induction f with
  | zero => intro c h; simp [run] at h
  | succ k ih =>
    intro c h
    simp only [run] at h ⊢
    cases hstep : step1 P c with
    | next c' => simp only [hstep] at h ⊢; exact ih c' h
    | halt => simp only [hstep] at h ⊢; exact h
    | fault => simp only [hstep] at h; exact absurd h (by simp)
    | stuck => simp only [hstep] at h; exact absurd h (by simp)

theorem run_fault_succ {P : Program} :
    ∀ (f : Nat) (c : Config), (∃ cf, run P c f = (cf, .fault)) →
      ∃ cf, run P c (f + 1) = (cf, .fault) := by
  intro f
  induction f with
  | zero => intro c ⟨cf, h⟩; simp [run] at h
  | succ k ih =>
    intro c ⟨cf, h⟩
    simp only [run] at h ⊢
    cases hstep : step1 P c with
    | next c' => simp only [hstep] at h ⊢; exact ih c' ⟨cf, h⟩
    | halt => simp only [hstep] at h; exact absurd h (by simp)
    | fault => exact ⟨c, rfl⟩
    | stuck => simp only [hstep] at h; exact absurd h (by simp)

theorem run_halt_mono {P : Program} {cf : Config} {f : Nat} {c : Config}
    (h : run P c f = (cf, .halt)) : ∀ k, run P c (f + k) = (cf, .halt) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact run_halt_succ (f + k) c ih

theorem run_fault_mono {P : Program} {f : Nat} {c cf : Config}
    (h : run P c f = (cf, .fault)) : ∀ k, ∃ cf', run P c (f + k) = (cf', .fault) := by
  intro k
  induction k with
  | zero => exact ⟨cf, h⟩
  | succ k ih => exact run_fault_succ (f + k) c ih

/-! ### `run` ↔ `Steps` bridges

The functional interpreter `run` (fuel = exact step count) and the relational `Steps` (unbounded
reflexive–transitive closure) are two views of the same execution. These lemmas convert between them:
`steps_to_run` turns a relational path into an exact-count non-terminating run, and `run_add` splits a
run at an interior still-running point. Together they let the lowering's straight-line prefixes (proved
as `Steps` in `AstToTacCorrect`) be spliced onto fuel-indexed loop/divergence arguments. -/

-- `run_add` (additivity of `run` at a still-running split point) is a shared reference-semantics lemma
-- hoisted to `IR.TAC` (`namespace Semantics`).

/-- One more step, appended at the *end* of a still-running run. -/
theorem run_succ_back {P : Program} {k : Nat} {c c' c'' : Config}
    (h : run P c k = (c', .next c')) (hstep : step1 P c' = .next c'') :
    run P c (k + 1) = (c'', .next c'') := by
  rw [run_add h]; simp only [run, hstep]

/-- **A relational path is a still-running run of its length.** Any `Steps` chain is realized by the
    functional `run` at some fuel, ending `.next` at the same config (no terminal in between). -/
theorem steps_to_run {P : Program} {c c' : Config} (h : Steps P c c') :
    ∃ k, run P c k = (c', .next c') := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k + 1, run_succ_back hk (step1_next_iff.mpr hstep)⟩

/-! ### From `Steps` + terminal classification to `Halts`/`Faults` -/

theorem step1_halt_of_final {P : Program} {c : Config} (h : Final P c) : step1 P c = .halt := by
  simp only [step1, Final] at *; rw [h]

theorem step1_fault_of_faulting {P : Program} {c : Config} (h : Faulting P c) :
    step1 P c = .fault := by
  obtain ⟨x, e, next, hf, hev⟩ := h
  simp only [step1, hf, hev]

/-- A relational run to a `Final` config is an IR `Halts`. -/
theorem halts_of_steps_final {P : Program} {c cf : Config}
    (hs : Steps P c cf) (hfin : Final P cf) : Halts P c cf := by
  obtain ⟨k, hk⟩ := steps_to_run hs
  exact ⟨k + 1, by rw [run_add hk]; simp only [run, step1_halt_of_final hfin]⟩

/-- A relational run to a `Faulting` config is an IR `Faults`. -/
theorem faults_of_steps_faulting {P : Program} {c cf : Config}
    (hs : Steps P c cf) (hflt : Faulting P cf) : Faults P c := by
  obtain ⟨k, hk⟩ := steps_to_run hs
  exact ⟨k + 1, cf, by rw [run_add hk]; simp only [run, step1_fault_of_faulting hflt]⟩

/-! ### Still-running-for-`n`-steps predicate + downward closure (for divergence) -/

/-- When `run` reports `.next`, the returned config *is* the `.next` payload (they are set together
    at the fuel-exhaustion base case, and the recursion preserves it). -/
theorem run_next_config {P : Program} {n : Nat} {c a b : Config}
    (h : run P c n = (a, .next b)) : a = b := by
  induction n generalizing c with
  | zero =>
      simp only [run, Prod.mk.injEq, Status.next.injEq] at h
      rw [← h.1, h.2]
  | succ k ih =>
      simp only [run] at h
      cases hstep : step1 P c with
      | next d => simp only [hstep] at h; exact ih h
      | halt => simp only [hstep] at h; exact absurd h (by simp)
      | fault => simp only [hstep] at h; exact absurd h (by simp)
      | stuck => simp only [hstep] at h; exact absurd h (by simp)

/-- The run from `c` is **still going after `n` steps**. -/
def RunsFor (P : Program) (c : Config) (n : Nat) : Prop := ∃ c', run P c n = (c', .next c')

/-- Terminals are stable: a non-`.next` result at fuel `m` persists at `m + 1`. -/
theorem run_not_next_succ {P : Program} {e : Config} {st : Status} (hst : ∀ c', st ≠ .next c') :
    ∀ (m : Nat) (c : Config), run P c m = (e, st) → run P c (m + 1) = (e, st) := by
  intro m
  induction m with
  | zero =>
      intro c h; simp only [run, Prod.mk.injEq] at h
      obtain ⟨_, h2⟩ := h; exact absurd h2.symm (hst c)
  | succ k ih =>
      intro c h
      simp only [run] at h ⊢
      cases hstep : step1 P c with
      | next c' => simp only [hstep] at h ⊢; exact ih c' h
      | halt => simp only [hstep] at h ⊢; exact h
      | fault => simp only [hstep] at h ⊢; exact h
      | stuck => simp only [hstep] at h ⊢; exact h

theorem run_not_next_mono {P : Program} {e : Config} {st : Status} (hst : ∀ c', st ≠ .next c')
    {m : Nat} {c : Config} (h : run P c m = (e, st)) : ∀ k, run P c (m + k) = (e, st) := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact run_not_next_succ hst (m + k) c ih

/-- **Downward closure.** Still running after `n` steps ⇒ still running after any `m ≤ n`. -/
theorem RunsFor.le {P : Program} {c : Config} {m n : Nat}
    (hle : m ≤ n) (h : RunsFor P c n) : RunsFor P c m := by
  obtain ⟨d, hn⟩ := h
  rcases hstat : run P c m with ⟨e, st⟩
  cases st with
  | next e' => rw [run_next_config hstat] at hstat; exact ⟨e', hstat⟩
  | halt =>
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      rw [run_not_next_mono (by simp) hstat k] at hn; exact absurd hn (by simp)
  | fault =>
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      rw [run_not_next_mono (by simp) hstat k] at hn; exact absurd hn (by simp)
  | stuck =>
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      rw [run_not_next_mono (by simp) hstat k] at hn; exact absurd hn (by simp)

/-- Running forever (for every step count) is exactly `Diverges`. -/
theorem diverges_of_runsFor {P : Program} {c : Config} (h : ∀ n, RunsFor P c n) : Diverges P c := by
  intro fuel; obtain ⟨c', hc'⟩ := h fuel; exact ⟨c', by rw [hc']⟩

/-- **Prepend a finite path to a still-running run.** A `Steps`-path into a config that itself runs for
    `n` steps yields a run of at least `n` steps from the start. The workhorse for splicing the
    lowering's straight-line prefixes onto the loop/divergence step-count arguments. -/
theorem runsFor_of_steps {P : Program} {c c' : Config} {n : Nat}
    (hs : Steps P c c') (hr : RunsFor P c' n) : RunsFor P c n := by
  obtain ⟨k, hk⟩ := steps_to_run hs
  obtain ⟨d, hd⟩ := hr
  exact RunsFor.le (Nat.le_add_left n k) ⟨d, by rw [run_add hk]; exact hd⟩

/-- **Prepend a single step**, gaining one on the count: this is where a loop back-edge turns "survives
    `n` more iterations" into "still running after `n + 1` steps" — the ≥ 1-step-per-iteration content
    of the plus-simulation. -/
theorem runsFor_step {P : Program} {c c' : Config} {n : Nat}
    (h : step1 P c = .next c') (hr : RunsFor P c' n) : RunsFor P c (n + 1) := by
  obtain ⟨d, hd⟩ := hr
  exact ⟨d, by simp only [run, h]; exact hd⟩

/-! ### Transitivity + `Diverges` peel/graft -/

-- `steps_trans` is a shared reference-semantics lemma hoisted to `IR.TAC` (`namespace Semantics`).

/-- Peel the first step off a divergent run: it steps, and the successor still diverges. -/
theorem diverges_step {P : Program} {c : Config} (h : Diverges P c) :
    ∃ c', Step P c c' ∧ Diverges P c' := by
  obtain ⟨cf, hcf⟩ := h 1
  cases hstep : step1 P c with
  | next d =>
      refine ⟨d, step1_next_iff.mp hstep, fun fuel => ?_⟩
      obtain ⟨cg, hcg⟩ := h (fuel + 1)
      exact ⟨cg, by rw [show run P c (fuel + 1) = run P d fuel by simp only [run, hstep]] at hcg; exact hcg⟩
  | halt => rw [show (run P c 1).2 = Status.halt by simp only [run, hstep]] at hcf; exact absurd hcf (by simp)
  | fault => rw [show (run P c 1).2 = Status.fault by simp only [run, hstep]] at hcf; exact absurd hcf (by simp)
  | stuck => rw [show (run P c 1).2 = Status.stuck by simp only [run, hstep]] at hcf; exact absurd hcf (by simp)

/-- Graft a step onto the front of a divergent run. -/
theorem diverges_step_back {P : Program} {c c' : Config}
    (h : step1 P c = .next c') (hd : Diverges P c') : Diverges P c := by
  intro fuel
  cases fuel with
  | zero => exact ⟨c, rfl⟩
  | succ k => obtain ⟨cg, hcg⟩ := hd k; exact ⟨cg, by simp only [run, h]; exact hcg⟩

/-! ### Generic step-simulation ⇒ fault/divergence preservation (IR → IR)

A *step simulation* `StepSim P P' R`: every source `Step` (from an in-range node, under a store relation
`R`) is matched by **≥ 1** target steps to the same successor node, re-establishing `R`. The node is
preserved (all three normalize passes keep old node indices; inserted nodes get fresh labels). From this
alone, both fault- and divergence-preservation follow uniformly — the reusable engine the per-pass
`NormalizeBehavior` obligations plug into. -/

/-- One source step matched by ≥ 1 target steps (a leading `Step` then a `Steps` tail), same successor
    node, `R` restored. -/
def StepSim (P P' : Program) (R : Store → Store → Prop) : Prop :=
  ∀ {c d : Config} {σT : Store}, c.node < P.size → R σT c.store → Step P c d →
    ∃ mid σT', Step P' ⟨c.node, σT⟩ mid ∧ Steps P' mid ⟨d.node, σT'⟩ ∧ R σT' d.store

/-- Lift a whole source run into the target, threading `R`. -/
theorem steps_lift_R {P P' : Program} {R : Store → Store → Prop} (hsim : StepSim P P' R)
    (hwf : WellFormed P) {c₀ cf : Config} {σ0 : Store}
    (hc0 : c₀.node < P.size) (hR0 : R σ0 c₀.store) (h : Steps P c₀ cf) :
    ∃ σTf, Steps P' ⟨c₀.node, σ0⟩ ⟨cf.node, σTf⟩ ∧ R σTf cf.store := by
  induction h with
  | refl => exact ⟨σ0, Steps.refl, hR0⟩
  | tail hs hstep ih =>
      obtain ⟨σT', hlift, hR'⟩ := ih
      obtain ⟨mid, σTf, hstepP, hstepsP, hRf⟩ :=
        hsim (reachable_in_range hwf hc0 hs) hR' hstep
      exact ⟨σTf, steps_trans hlift (steps_trans (Steps.tail Steps.refl hstepP) hstepsP), hRf⟩

/-- **Fault preservation** from a step simulation, in composable `Steps`-into-`Faulting` form (so it
    threads across a chain of passes): a source run into a `Faulting` config yields a target run into a
    `Faulting` config, given the fault reflects (`hfsim`). -/
theorem faultSteps_of_stepsim {P P' : Program} {R : Store → Store → Prop} (hsim : StepSim P P' R)
    (hwf : WellFormed P)
    (hfsim : ∀ {cf : Config} {σT : Store}, cf.node < P.size → R σT cf.store → Faulting P cf →
        ∃ cf', Steps P' ⟨cf.node, σT⟩ cf' ∧ Faulting P' cf')
    {c₀ cf : Config} {σ0 : Store} (hc0 : c₀.node < P.size) (hR0 : R σ0 c₀.store)
    (hs : Steps P c₀ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps P' ⟨c₀.node, σ0⟩ cf' ∧ Faulting P' cf' := by
  obtain ⟨σTf, hlift, hRf⟩ := steps_lift_R hsim hwf hc0 hR0 hs
  obtain ⟨cf', hcf', hflt'⟩ := hfsim (reachable_in_range hwf hc0 hs) hRf hflt
  exact ⟨cf', steps_trans hlift hcf', hflt'⟩

/-- **Divergence preservation** from a step simulation: each source step forces ≥ 1 target steps, so a
    source run surviving `m` steps forces a target run still live after `m` steps — for every `m`. -/
theorem diverges_of_stepsim {P P' : Program} {R : Store → Store → Prop} (hsim : StepSim P P' R)
    (hwf : WellFormed P) {c₀ : Config} {σ0 : Store}
    (hc0 : c₀.node < P.size) (hR0 : R σ0 c₀.store) (hdiv : Diverges P c₀) :
    Diverges P' ⟨c₀.node, σ0⟩ := by
  apply diverges_of_runsFor
  intro m
  induction m generalizing c₀ σ0 with
  | zero => exact ⟨_, rfl⟩
  | succ k ih =>
      obtain ⟨c₁, hstep, hdiv1⟩ := diverges_step hdiv
      obtain ⟨mid, σT', hstepP, hstepsP, hR1⟩ := hsim hc0 hR0 hstep
      exact runsFor_step (step1_next_iff.mpr hstepP)
        (runsFor_of_steps hstepsP (ih (step_in_range hwf hstep) hR1 hdiv1))

/-! ### Config-relation generalization: divergence preservation under node-remapping

`StepSim`/`diverges_of_stepsim` fix the target node **equal to** the source node (`⟨d.node, σT'⟩`) —
right for the normalize passes, which keep node indices. A block-expanding transform (PDCE maps each
source node `i` to a whole block at some offset) breaks that, so the simulation is restated over an
arbitrary config relation `Rel : Config → Config → Prop`, with each source step matched by a **leading
target `Step` then a `Steps` tail** — i.e. ≥ 1 target step, the non-stuttering condition divergence
preservation requires (a 0-step match would let an infinite source run collapse to a finite target
run). Everything downstream (`runsFor_step`/`runsFor_of_steps`/`diverges_step`) is reused verbatim. -/

/-- One source step matched by ≥ 1 target steps, threading a general config relation `Rel` (the target
    endpoint node is arbitrary — not tied to the source node). -/
def StepSimG (P Q : Program) (Rel : Config → Config → Prop) : Prop :=
  ∀ {c c' d : Config}, c.node < P.size → Rel c d → Step P c c' →
    ∃ mid d', Step Q d mid ∧ Steps Q mid d' ∧ Rel c' d'

/-- **Divergence preservation from a config-relation step simulation.** Same counting argument as
    `diverges_of_stepsim`, but over `Rel` with the target start `d₀` free: each source step forces a
    leading target step (`runsFor_step`, +1) followed by its tail (`runsFor_of_steps`), so a source run
    surviving `m` steps forces a target run still live after `m` steps — for every `m`. -/
theorem diverges_of_stepsimG {P Q : Program} {Rel : Config → Config → Prop}
    (hsim : StepSimG P Q Rel) (hwf : WellFormed P) {c₀ d₀ : Config}
    (hc0 : c₀.node < P.size) (hR0 : Rel c₀ d₀) (hdiv : Diverges P c₀) :
    Diverges Q d₀ := by
  apply diverges_of_runsFor
  intro m
  induction m generalizing c₀ d₀ with
  | zero => exact ⟨_, rfl⟩
  | succ k ih =>
      obtain ⟨c₁, hstep, hdiv1⟩ := diverges_step hdiv
      obtain ⟨mid, d', hstepQ, hstepsQ, hR1⟩ := hsim hc0 hR0 hstep
      exact runsFor_step (step1_next_iff.mpr hstepQ)
        (runsFor_of_steps hstepsQ (ih (step_in_range hwf hstep) hR1 hdiv1))

/-! ### No reachable `.stuck` under well-formedness -/

/-- An in-range node never classifies as `.stuck` (that arm needs `fetch = none`). -/
theorem step1_ne_stuck_of_lt {P : Program} {c : Config} (h : c.node < P.size) :
    step1 P c ≠ .stuck := by
  obtain ⟨instr, hf⟩ := fetch_some_of_lt h
  cases instr with
  | assign x e next => simp only [step1, hf]; cases eval c.store e <;> exact Status.noConfusion
  | ifz x z nz => simp only [step1, hf]; exact Status.noConfusion
  | noop next => simp only [step1, hf]; exact Status.noConfusion
  | halt => simp only [step1, hf]; exact Status.noConfusion

/-- **`run` never reports `.stuck`** from an in-range start of a well-formed program — every
    intermediate config stays in range (`step_in_range`), so the `.stuck` arm is unreachable. -/
theorem run_ne_stuck {P : Program} (wf : WellFormed P) :
    ∀ (fuel : Nat) (c : Config), c.node < P.size → (run P c fuel).2 ≠ .stuck := by
  intro fuel
  induction fuel with
  | zero => intro c _ h; simp [run] at h
  | succ k ih =>
    intro c hc
    simp only [run]
    cases hstep : step1 P c with
    | next c' => exact ih c' (step_in_range wf (step1_next_iff.mp hstep))
    | halt => simp
    | fault => simp
    | stuck => exact absurd hstep (step1_ne_stuck_of_lt hc)

/-! ### The IR trichotomy: exhaustive + mutually exclusive -/

/-- **Every well-formed IR program is halting, diverging, or faulting** (no fourth "stuck" outcome),
    from any in-range start. The proof of the missing `Diverges` disjunct reuses the other two to
    contradict, exactly as `Arm64Trichotomy.outcome_exhaustive` does. -/
theorem outcome_exhaustive {P : Program} (wf : WellFormed P) {c : Config} (hc : c.node < P.size) :
    (∃ cf, Halts P c cf) ∨ Diverges P c ∨ Faults P c := by
  apply Classical.byContradiction
  intro hcon
  apply hcon
  refine Or.inr (Or.inl ?_)
  intro fuel
  cases hr : run P c fuel with
  | mk cf st =>
    cases st with
    | next cf' => exact ⟨cf', rfl⟩
    | halt => exact absurd (Or.inl ⟨cf, fuel, hr⟩) hcon
    | fault => exact absurd (Or.inr (Or.inr ⟨fuel, cf, hr⟩)) hcon
    | stuck => exact absurd (show (run P c fuel).2 = Status.stuck by rw [hr]) (run_ne_stuck wf fuel c hc)

theorem halts_not_diverges {P : Program} {c cf : Config}
    (hh : Halts P c cf) (hd : Diverges P c) : False := by
  obtain ⟨f, hf⟩ := hh
  obtain ⟨cf', hr⟩ := hd f
  rw [hf] at hr; exact Status.noConfusion hr

theorem faults_not_diverges {P : Program} {c : Config}
    (hf : Faults P c) (hd : Diverges P c) : False := by
  obtain ⟨f, cf, hff⟩ := hf
  obtain ⟨cf', hr⟩ := hd f
  rw [hff] at hr; exact Status.noConfusion hr

theorem halts_not_faults {P : Program} {c cf : Config}
    (hh : Halts P c cf) (hf : Faults P c) : False := by
  obtain ⟨f₁, h₁⟩ := hh
  obtain ⟨f₂, cf₂, h₂⟩ := hf
  have e₁ := run_halt_mono h₁ f₂
  obtain ⟨cf', e₂⟩ := run_fault_mono h₂ f₁
  rw [Nat.add_comm] at e₂
  rw [e₁] at e₂; simp only [Prod.mk.injEq] at e₂; exact Status.noConfusion e₂.2

theorem halts_unique {P : Program} {c cf₁ cf₂ : Config}
    (h₁ : Halts P c cf₁) (h₂ : Halts P c cf₂) : cf₁ = cf₂ := by
  obtain ⟨f₁, e₁⟩ := h₁
  obtain ⟨f₂, e₂⟩ := h₂
  have a₁ := run_halt_mono e₁ f₂
  have a₂ := run_halt_mono e₂ f₁
  rw [Nat.add_comm] at a₂
  rw [a₁] at a₂; exact (Prod.mk.injEq _ _ _ _ ▸ a₂).1

end Semantics

end BaseLanguage
