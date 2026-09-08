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
    mode's bundle — which is valid and extremal whatever the filter is aimed at. -/
theorem runLcm_preserves_halt {P : Program} (mode : LcmMode) (S : LcmSpec P)
    (hS : Extremal S) (wn : WellNormalized P) {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (runLcm mode P S) ⟨(runLcm mode P S).entry, σ⟩ d_f
         ∧ Final (runLcm mode P S) d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v := by
  show ∃ d_f, Steps (transform P (mode.spec S)) ⟨(transform P (mode.spec S)).entry, σ⟩ d_f ∧ _ ∧ _
  rw [transform_entry]
  exact transform_preserves_halt (mode.spec S) (mode.spec_extremal hS) wn hen hobs hrun hfin

/-- **The divergence-preserving mode preserves divergence — for every program, with no side condition.**
    Its bundle hoists only `Expr.faultFree` expressions, so `SafeInserts` is immediate
    (`safeInserts_faultFree`) rather than checked, and nothing falls back to the unoptimized program. -/
theorem runLcm_preserves_diverges {P : Program} (S : LcmSpec P) (hS : Extremal S)
    (wn : WellNormalized P) (wf : WellFormed P) {ne : Node} (hen : P.fetch P.entry = some (.noop ne))
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (runLcm .preserveDivergence P S) ⟨(runLcm .preserveDivergence P S).entry, σ⟩ := by
  show Diverges (transform P (S.withKeep Expr.faultFree))
         ⟨(transform P (S.withKeep Expr.faultFree)).entry, σ⟩
  rw [transform_entry]
  exact transform_preserves_diverges_faultFree S hS wn wf hen hdiv

/-- **Every hypothesis discharged at once, on a real pipeline program.** For any well-formed, fully
    reachable source program, the normalized program the compiler actually feeds to LCM satisfies
    `WellNormalized` and the `prependEntry` `noop`-entry condition, so the divergence-preserving mode
    preserves divergence on it. This is the form the compiler uses, and it is what rules out the
    hypotheses being jointly unsatisfiable — the theorem above is not vacuously true for want of a
    program that meets its side conditions. -/
theorem runLcm_normalized_preserves_diverges {P : Program}
    (hwf : WellFormed P) (har : AllReachable P)
    (S : LcmSpec (Normalize.normalize P)) (hS : Extremal S) {σ : Store}
    (hdiv : Diverges (Normalize.normalize P) ⟨(Normalize.normalize P).entry, σ⟩) :
    Diverges (runLcm .preserveDivergence (Normalize.normalize P) S)
      ⟨(runLcm .preserveDivergence (Normalize.normalize P) S).entry, σ⟩ := by
  obtain ⟨ne, hen⟩ := Normalize.normalize_entry_noop P
  have hwn := Normalize.normalize_wellNormalized P hwf har
  exact runLcm_preserves_diverges S hS hwn hwn.wf hen hdiv

end BaseLanguage.Analyses.LCM
