-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Divergence
import BaseLanguage.Normalize.Sim

/-!
# `LCM.Mode` — selecting between the two verified LCM modes

Both modes run the *same* verified transform over the *same* solver bundle. They differ in one field of
that bundle — `keep`, the hoisting filter — and therefore in which preservation theorems hold:

| mode                  | halting runs | faults    | divergence        | hoists            |
|-----------------------|--------------|-----------|-------------------|-------------------|
| `classic`             | preserved    | preserved | **not** preserved | every expression  |
| `preserveDivergence`  | preserved    | preserved | preserved         | all but `div`/`mod` |

`preserveDivergence` is `classic` with `keep := Expr.faultFree`. The filter is **per expression**: a
`div`/`mod` is left exactly where the source computes it, and every other expression is hoisted exactly as
in `classic`. A program containing a division still gets the full benefit of LCM on all of its other
expressions — there is no whole-program fallback, and no side condition to check, because every insert set
is gated by `τᵤK = τᵤ ∩ keep` and so is fault-free by construction (`safeInserts_faultFree`).

`runLcm_safe_preserves_all` states the `preserveDivergence` row as a single theorem: the base language has
exactly three outcomes (halt, fault, diverge), and that mode preserves all three, halting runs together
with their observable store.

Because `keep` occurs in no validity or extremality clause, `S.withKeep f` is trivially still a valid,
extremal bundle (`Extremal.withKeep`). That is what lets *one* development, *one* solver and *one* set of
correctness theorems — all quantified over an arbitrary valid, extremal bundle — cover both modes.
-/
namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-- Which LCM mode the compiler runs. -/
inductive LcmMode where
  /-- The classical KRS hoist. Divergence is out of scope. -/
  | classic
  /-- Hoist only fault-free expressions, so divergence is preserved. -/
  | preserveDivergence
  deriving DecidableEq, Repr, Inhabited

/-- Parse the CLI spelling of a mode. -/
def LcmMode.ofString? : String → Option LcmMode
  | "classic" | "krs"                  => some .classic
  | "safe" | "preserve-divergence"     => some .preserveDivergence
  | _                                  => none

/-- The CLI spelling of a mode. -/
def LcmMode.name : LcmMode → String
  | .classic            => "classic"
  | .preserveDivergence => "preserve-divergence"

/-- The bundle a mode runs with: the solver's bundle, re-aimed at the mode's hoisting filter. -/
def LcmMode.spec {P : Program} (mode : LcmMode) (S : LcmSpec P) : LcmSpec P :=
  match mode with
  | .classic            => S
  | .preserveDivergence => S.withKeep Expr.faultFree

theorem LcmMode.spec_extremal {P : Program} (mode : LcmMode) {S : LcmSpec P} (hS : Extremal S) :
    Extremal (mode.spec S) := by
  cases mode with
  | classic => exact hS
  | preserveDivergence => exact hS.withKeep _

/-- **The mode-selecting LCM pass.** One transform, one bundle, one field different. -/
def runLcm (mode : LcmMode) (P : Program) (S : LcmSpec P) : Program :=
  transform P (mode.spec S)

@[simp] theorem runLcm_classic {P : Program} (S : LcmSpec P) :
    runLcm .classic P S = transform P S := rfl

theorem runLcm_wellFormed {P : Program} (mode : LcmMode) (S : LcmSpec P) (wf : WellFormed P) :
    WellFormed (runLcm mode P S) := transform_wellFormed (mode.spec S) wf

@[simp] theorem runLcm_obs {P : Program} (mode : LcmMode) (S : LcmSpec P) :
    (runLcm mode P S).obs = P.obs := rfl

/-- **Both modes preserve halting behavior.** One instance of `transform_preserves_halt`, applied to the
    mode's bundle — which is valid whatever the filter is aimed at (`keep` appears in no clause). -/
theorem runLcm_preserves_halt {P : Program} (mode : LcmMode) (S : LcmSpec P)
    (hg : GateSound P (mode.spec S)) (wn : WellNormalized P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (runLcm mode P S) ⟨(runLcm mode P S).entry, σ⟩ d_f
         ∧ Final (runLcm mode P S) d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  show ∃ d_f, Steps (transform P (mode.spec S)) ⟨(transform P (mode.spec S)).entry, σ⟩ d_f ∧ _ ∧ _
  rw [transform_entry]
  exact transform_preserves_halt (mode.spec S) hg wn hobs hrun hfin

/-- **Both modes preserve faults.** `transform_preserves_faulting` holds for any extremal bundle, and the
    mode's bundle is extremal whatever the filter is aimed at, so the fault diagonal is mode-general in
    exactly the way the halting theorem is. Together with `runLcm_preserves_halt` and
    `runLcm_preserves_diverges` this closes the outcome table for `.preserveDivergence`: it preserves
    halting (with the observables), faulting, and divergence. -/
theorem runLcm_preserves_faulting {P : Program} (mode : LcmMode) (S : LcmSpec P)
    (hg : GateSound P (mode.spec S)) (wn : WellNormalized P)
    {σ : Store} {c_n : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_n) (hflt : Faulting P c_n) :
    ∃ df, Steps (runLcm mode P S) ⟨(runLcm mode P S).entry, σ⟩ df
        ∧ Faulting (runLcm mode P S) df := by
  show ∃ df, Steps (transform P (mode.spec S)) ⟨(transform P (mode.spec S)).entry, σ⟩ df ∧ _
  rw [transform_entry]
  exact transform_preserves_faulting (mode.spec S) hg wn hrun hflt

/-- **The divergence-preserving mode preserves divergence — for every program, with no side condition.**
    Its bundle hoists only `Expr.faultFree` expressions, so `SafeInserts` is immediate
    (`safeInserts_faultFree`) rather than checked, and nothing falls back to the unoptimized program. -/
theorem runLcm_preserves_diverges {P : Program} (S : LcmSpec P)
    (hg : GateSound P (S.withKeep Expr.faultFree)) (wn : WellNormalized P) (wf : WellFormed P)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (runLcm .preserveDivergence P S) ⟨(runLcm .preserveDivergence P S).entry, σ⟩ := by
  show Diverges (transform P (S.withKeep Expr.faultFree))
         ⟨(transform P (S.withKeep Expr.faultFree)).entry, σ⟩
  rw [transform_entry]
  exact transform_preserves_diverges_faultFree S hg wn wf hdiv

/-- **Every hypothesis discharged at once, on a real pipeline program.** For any well-formed, fully
    reachable source program, the normalized program the compiler actually feeds to LCM satisfies
    `WellNormalized`, so the divergence-preserving mode preserves divergence on it. This is the form the
    compiler uses, and it is what rules out the hypotheses being jointly unsatisfiable — the theorem
    above is not vacuously true for want of a program that meets its side conditions. -/
theorem runLcm_normalized_preserves_diverges {P : Program}
    (hwf : WellFormed P) (har : AllReachable P)
    (S : LcmSpec (Normalize.normalize P))
    (hg : GateSound (Normalize.normalize P) (S.withKeep Expr.faultFree)) {σ : Store}
    (hdiv : Diverges (Normalize.normalize P) ⟨(Normalize.normalize P).entry, σ⟩) :
    Diverges (runLcm .preserveDivergence (Normalize.normalize P) S)
      ⟨(runLcm .preserveDivergence (Normalize.normalize P) S).entry, σ⟩ := by
  have hwn := Normalize.normalize_wellNormalized P hwf har
  exact runLcm_preserves_diverges S hg hwn hwn.wf hdiv

/-- **The divergence-preserving mode preserves every outcome the semantics can produce.** The base
    language has exactly three (`IR/TAC.lean`: halt, fault, diverge), and `.preserveDivergence` preserves
    all three — halting with the observable store, faulting, and divergence. The classical mode has the
    first two conjuncts but not the third (`examples/lcm-divergence/DivergenceGap.lean` is the witness). -/
theorem runLcm_safe_preserves_all {P : Program} (S : LcmSpec P)
    (hg : GateSound P (S.withKeep Expr.faultFree))
    (wn : WellNormalized P) (wf : WellFormed P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true) {σ : Store} :
    let T := runLcm .preserveDivergence P S
    (∀ c_f, Steps P ⟨P.entry, σ⟩ c_f → Final P c_f →
        ∃ d_f, Steps T ⟨T.entry, σ⟩ d_f ∧ Final T d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v)
  ∧ (∀ c_n, Steps P ⟨P.entry, σ⟩ c_n → Faulting P c_n →
        ∃ df, Steps T ⟨T.entry, σ⟩ df ∧ Faulting T df)
  ∧ (Diverges P ⟨P.entry, σ⟩ → Diverges T ⟨T.entry, σ⟩) :=
  ⟨fun _ hrun hfin => runLcm_preserves_halt .preserveDivergence S hg wn hobs hrun hfin,
   fun _ hrun hflt => runLcm_preserves_faulting .preserveDivergence S hg wn hrun hflt,
   fun hdiv => runLcm_preserves_diverges S hg wn wf hdiv⟩

/-! ### The outcome table, per gate

All three cells at once, once for each `GateMode`. The pair below is the sharpest statement of what the
seventh ghost buys: the *same* three conclusions, about the *same* transform, with the `.materialized`
form needing neither `Extremal S` nor the `prependEntry` `noop` entry. -/

/-- **Every outcome preserved, from validity alone** — the materialization gate. -/
theorem runLcm_safe_preserves_all_mat {P : Program} (S : LcmSpec P) (hm : S.gate = .materialized)
    (wn : WellNormalized P) (wf : WellFormed P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true) {σ : Store} :
    let T := runLcm .preserveDivergence P S
    (∀ c_f, Steps P ⟨P.entry, σ⟩ c_f → Final P c_f →
        ∃ d_f, Steps T ⟨T.entry, σ⟩ d_f ∧ Final T d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v)
  ∧ (∀ c_n, Steps P ⟨P.entry, σ⟩ c_n → Faulting P c_n →
        ∃ df, Steps T ⟨T.entry, σ⟩ df ∧ Faulting T df)
  ∧ (Diverges P ⟨P.entry, σ⟩ → Diverges T ⟨T.entry, σ⟩) :=
  runLcm_safe_preserves_all S (gateSound_materialized (S.withKeep Expr.faultFree) hm) wn wf hobs

/-- **Every outcome preserved, from extremality** — the classical demand gate. Same conclusions, two
    more hypotheses. -/
theorem runLcm_safe_preserves_all_demand {P : Program} (S : LcmSpec P) (hd : S.gate = .demand)
    (hS : Extremal S) (wn : WellNormalized P) (wf : WellFormed P)
    {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true) {σ : Store} :
    let T := runLcm .preserveDivergence P S
    (∀ c_f, Steps P ⟨P.entry, σ⟩ c_f → Final P c_f →
        ∃ d_f, Steps T ⟨T.entry, σ⟩ d_f ∧ Final T d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v)
  ∧ (∀ c_n, Steps P ⟨P.entry, σ⟩ c_n → Faulting P c_n →
        ∃ df, Steps T ⟨T.entry, σ⟩ df ∧ Faulting T df)
  ∧ (Diverges P ⟨P.entry, σ⟩ → Diverges T ⟨T.entry, σ⟩) :=
  runLcm_safe_preserves_all S
    (gateSound_demand (S.withKeep Expr.faultFree) hd (hS.withKeep _) wn hen) wn wf hobs

end BaseLanguage.Analyses.LCM
