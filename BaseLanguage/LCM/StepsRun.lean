-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.IR.Cost

/-!
# The `StepsH` ↔ fuel-`run` bridge

The simulation (`sim`/`match_step`/`transform_preserves_halt`) is **relational** (`Steps`/`StepsH`, `Prop`);
`evalCount`/`runNodes` are **fuel-based** (`step1`). This file bridges the two so evaluations can be counted
along the transform's relational run:

* `stepsH_run` — the functional `run` follows any relational `StepsH` (exact-length).
* `evalCount_stepsH` — hence `evalCount` **decomposes over a `StepsH` segment** (the per-block additivity
  folded with `match_step`'s per-block `Steps`).
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-- **The functional run follows the relational head-run.** After exactly the `StepsH`'s length, `run`
    reaches its end (fuel exhausted there, status `.next`). The missing link between the `Prop` simulation
    and the fuel-based cost measure. -/
theorem stepsH_run {P : Program} {c c' : Config} (h : StepsH P c c') :
    ∃ k, run P c k = (c', .next c') := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | head s _ ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      simp only [run, step1_next_iff.mpr s]
      exact hk

/-- **`evalCount` decomposes over a `StepsH` segment.** For a relational segment `c ⟶* c'` there is a fuel
    `k` with `evalCount c (k+b) = evalCount c k + evalCount c' b`. This sums the transform's run: `match_step`
    hands a per-block `Steps`, this turns it into an additive count contribution. Combined with
    `evalCount_eq_filter_runNodes` + the `LayoutEval` gate, the per-block contribution is
    `[e∈insertBefore]+[e∈insertAfter]+[kept]`. -/
theorem evalCount_stepsH {P : Program} {e : Expr} {c c' : Config} (h : StepsH P c c') (b : Nat) :
    ∃ k, evalCount P e c (k + b) = evalCount P e c k + evalCount P e c' b := by
  obtain ⟨k, hk⟩ := stepsH_run h
  exact ⟨k, evalCount_add hk b⟩

/-- Any transform run obtained from a source halting run (`transform_preserves_halt` gives a
    `Steps (transform P S)`) is followed by `run`, so `evalCount` over it is well-defined and fuel-stable
    (`evalCount_stable`). -/
theorem transform_run_evalCount_defined {P : Program} {S : LcmSpec P} {c d : Config}
    (h : Steps (transform P S) c d) :
    ∃ k, run (transform P S) c k = (d, .next d) := stepsH_run (steps_toH h)

end BaseLanguage.Analyses.LCM
