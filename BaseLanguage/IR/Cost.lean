-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

/-!
# `IR.Cost` — a measured layer over the EXISTING semantics (no new operational semantics)

The per-path eval-count is an **instrumentation of the existing functional interpreter** `step1`
(proven `step1_next_iff : step1 = .next c' ↔ Step`), not a new semantics. `evalCount` is `run` with a
counter: at each step it increments when the current node computes the tracked expression `e` (read off the
existing `P.fetch`), then recurses via the existing `step1`. PRIME-DIRECTIVE clean — a projection of
`step1`/`fetch`, no new analysis / `Node → Assignments` / fixpoint / source of truth.
-/

namespace BaseLanguage.Tac
open Semantics

/-- Does node `n` of `P` compute expression `e` (its `assign` RHS)? Read off the existing `fetch`. -/
def computesExpr (P : Program) (n : Node) (e : Expr) : Bool :=
  match P.fetch n with
  | some (.assign _ e' _) => e' == e
  | _ => false

/-- **Per-run eval count** of `e`: how many times the program *evaluates* `e` along the (fuel-bounded)
    run from `c`, via the EXISTING interpreter `step1`. Pure instrumentation — `step1` is the only
    semantics, `fetch` the only structure read. -/
def evalCount (P : Program) (e : Expr) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      (if computesExpr P c.node e then 1 else 0) +
        (match step1 P c with
         | .next c' => evalCount P e c' fuel
         | _        => 0)

/-- Sanity: the count never exceeds the fuel (one evaluation per step at most). -/
theorem evalCount_le_fuel (P : Program) (e : Expr) (c : Config) (fuel : Nat) :
    evalCount P e c fuel ≤ fuel := by
  induction fuel generalizing c with
  | zero => simp [evalCount]
  | succ n ih =>
      unfold evalCount
      have hstep : (match step1 P c with | .next c' => evalCount P e c' n | _ => 0) ≤ n := by
        cases step1 P c with
        | next c' => exact ih c'
        | halt => simp
        | fault => simp
        | stuck => simp
      split <;> omega

/-- **Per-step recursion.** On a real step `c → c'`, the count is the contribution of `c` plus the count of
    the continuation — the accounting any optimality argument folds over. -/
theorem evalCount_next {P : Program} {e : Expr} {c c' : Config} {fuel : Nat}
    (h : step1 P c = .next c') :
    evalCount P e c (fuel + 1)
      = (if computesExpr P c.node e then 1 else 0) + evalCount P e c' fuel := by
  show (if computesExpr P c.node e then 1 else 0)
      + (match step1 P c with | .next c'' => evalCount P e c'' fuel | _ => 0) = _
  rw [h]

/-- A non-stepping configuration (`halt`/`fault`/`stuck`) contributes only its own evaluation and stops. -/
theorem evalCount_stop {P : Program} {e : Expr} {c : Config} {m : Nat}
    (hs : ∀ c', step1 P c ≠ .next c') :
    evalCount P e c (m + 1) = (if computesExpr P c.node e then 1 else 0) := by
  show (if computesExpr P c.node e then 1 else 0)
      + (match step1 P c with | .next c'' => evalCount P e c'' m | _ => 0) = _
  cases hstep : step1 P c with
  | next c' => exact absurd hstep (hs c')
  | halt => simp
  | fault => simp
  | stuck => simp

/-- **A terminal configuration evaluates nothing** (`halt` computes no expression), so the run from a
    `Final` config has eval-count `0` at any fuel — the base of the run accounting. -/
theorem evalCount_final {P : Program} {e : Expr} {c : Config} (hf : Final P c) :
    ∀ fuel, evalCount P e c fuel = 0 := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ m =>
      unfold evalCount
      have h1 : step1 P c = .halt := by unfold step1; rw [show P.fetch c.node = some .halt from hf]
      have h2 : computesExpr P c.node e = false := by
        unfold computesExpr; rw [show P.fetch c.node = some .halt from hf]
      rw [h1, h2]; simp

/-- **Monotone in fuel** (more fuel only runs further, never fewer evaluations). Lets the eval-count of a
    *terminating* run be taken at any sufficient fuel. -/
theorem evalCount_mono {P : Program} {e : Expr} {c : Config} {m n : Nat} (hmn : m ≤ n) :
    evalCount P e c m ≤ evalCount P e c n := by
  induction m generalizing c n with
  | zero => simp [evalCount]
  | succ k ih =>
      obtain ⟨j, rfl⟩ := Nat.le.dest hmn
      cases hs : step1 P c with
      | next c' =>
          rw [evalCount_next hs, show k + 1 + j = (k + j) + 1 from by omega, evalCount_next hs]
          have := ih (c := c') (n := k + j) (by omega); omega
      | halt =>
          have h1 := evalCount_stop (e := e) (m := k) (fun c' => by rw [hs]; simp)
          have h2 := evalCount_stop (e := e) (m := k + j) (fun c' => by rw [hs]; simp)
          rw [show k + 1 + j = (k + j) + 1 from by omega]; omega
      | fault =>
          have h1 := evalCount_stop (e := e) (m := k) (fun c' => by rw [hs]; simp)
          have h2 := evalCount_stop (e := e) (m := k + j) (fun c' => by rw [hs]; simp)
          rw [show k + 1 + j = (k + j) + 1 from by omega]; omega
      | stuck =>
          have h1 := evalCount_stop (e := e) (m := k) (fun c' => by rw [hs]; simp)
          have h2 := evalCount_stop (e := e) (m := k + j) (fun c' => by rw [hs]; simp)
          rw [show k + 1 + j = (k + j) + 1 from by omega]; omega

/-- **The eval-count is well-defined for a terminating run.** Once the run from `c` has halted within `k`
    steps, extra fuel only re-walks the `Final` config (which evaluates nothing), so the count is fixed:
    `evalCount c (k + j) = evalCount c k`. This grounds the `Type`-level measure against termination — it is
    *the* number of evaluations the halting run performs, independent of the fuel chosen. -/
theorem evalCount_stable {P : Program} {e : Expr} {c : Config} {k : Nat}
    (hhalt : (run P c k).2 = .halt) : ∀ j, evalCount P e c (k + j) = evalCount P e c k := by
  induction k generalizing c with
  | zero => simp [run] at hhalt
  | succ m ih =>
      intro j
      cases hs : step1 P c with
      | next c' =>
          have hr : (run P c' m).2 = .halt := by
            have : run P c (m + 1) = run P c' m := by simp [run, hs]
            rwa [this] at hhalt
          rw [show m + 1 + j = (m + j) + 1 from by omega, evalCount_next hs, evalCount_next hs, ih hr j]
      | halt =>
          rw [show m + 1 + j = (m + j) + 1 from by omega,
              evalCount_stop (e := e) (fun c' => by rw [hs]; simp),
              evalCount_stop (e := e) (fun c' => by rw [hs]; simp)]
      | fault => simp [run, hs] at hhalt
      | stuck => simp [run, hs] at hhalt

/-- **Run-segment additivity.** If the first `a` steps from `c` reach `c'` without stopping, the count over
    `a + b` steps splits as the count of the first segment plus the count from `c'`. The backbone of the
    per-block decomposition: a whole-program run is the concatenation of its per-node block sub-runs. -/
theorem evalCount_add {P : Program} {e : Expr} {c c' : Config} {a : Nat}
    (h : run P c a = (c', .next c')) (b : Nat) :
    evalCount P e c (a + b) = evalCount P e c a + evalCount P e c' b := by
  induction a generalizing c with
  | zero =>
      simp only [run, Prod.mk.injEq, Status.next.injEq] at h
      obtain ⟨rfl, _⟩ := h
      show evalCount P e c (0 + b) = 0 + evalCount P e c b
      rw [Nat.zero_add, Nat.zero_add]
  | succ a ih =>
      cases hs : step1 P c with
      | next c1 =>
          have hr : run P c1 a = (c', .next c') := by
            rw [show run P c (a + 1) = run P c1 a from by simp [run, hs]] at h; exact h
          rw [show a + 1 + b = (a + b) + 1 from by omega, evalCount_next hs, evalCount_next hs, ih hr]
          omega
      | halt => rw [show run P c (a + 1) = (c, .halt) from by simp [run, hs]] at h; simp at h
      | fault => rw [show run P c (a + 1) = (c, .fault) from by simp [run, hs]] at h; simp at h
      | stuck => rw [show run P c (a + 1) = (c, .stuck) from by simp [run, hs]] at h; simp at h

/-- The **node-path** a fuel-bounded run walks (the node at each step taken). Companion to `evalCount`. -/
def runNodes (P : Program) : Config → Nat → List Node
  | _, 0      => []
  | c, fuel+1 => c.node :: (match step1 P c with | .next c' => runNodes P c' fuel | _ => [])

/-- **The operational eval-count is a filter-count over the run's node-path.** This unifies `evalCount`
    with the analysis-level path measures (`pathLiveLen`/`pathSinkDist`): the operational quantity is just
    `length ∘ filter computesExpr` over the nodes the run visits — the lingua franca for the optimality
    comparison. -/
theorem evalCount_eq_filter_runNodes (P : Program) (e : Expr) (c : Config) (fuel : Nat) :
    evalCount P e c fuel
      = ((runNodes P c fuel).filter (fun n => computesExpr P n e)).length := by
  induction fuel generalizing c with
  | zero => rfl
  | succ m ih =>
      cases hs : step1 P c with
      | next c' =>
          rw [evalCount_next hs, ih c',
              show runNodes P c (m + 1) = c.node :: runNodes P c' m from by simp [runNodes, hs],
              List.filter_cons]
          by_cases hp : computesExpr P c.node e <;> simp [hp] <;> omega
      | halt =>
          rw [evalCount_stop (e := e) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : computesExpr P c.node e <;> simp [hp]
      | fault =>
          rw [evalCount_stop (e := e) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : computesExpr P c.node e <;> simp [hp]
      | stuck =>
          rw [evalCount_stop (e := e) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : computesExpr P c.node e <;> simp [hp]

end BaseLanguage.Tac
