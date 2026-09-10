-- Copyright (c) 2026 Martin Rinard
import Seam.lcmmat.Adapter
import BaseLanguage.LCM.EvalCountHeadline
import BaseLanguage.Normalize.Sim

/-!
# Computational optimality, with every hypothesis discharged

`LCM.transform_evalCount_le_safe` states computational optimality abstractly: over any bundle that is
`Extremal`, whose replace gate is `GateSound` and `GateComplete`, on a `WellNormalized` program. Stating
it that way is deliberate — the gate is a *field* of the bundle, so taking its two obligations as
hypotheses is what keeps the demand-gate and materialization-gate proofs disjoint, and what makes the
ablation test in `Correctness/Coverage.lean` mean anything.

The cost of that abstraction is that the headline alone does not exhibit a bundle satisfying all four at
once. This file closes that: it instantiates the headline on the **solved seven-ghost bundle over a
normalized program**, so nothing is assumed that is not also proved here.

  Extremal       `lcmMatSolved_extremal`
  ExtremalMat    `lcmMatSolved_extremalMat`      (needed by the gate-completeness discharge)
  GateSound      `gateSound_materialized S rfl`  — the bundle ships `.materialized`, so `rfl`
  GateComplete   `gateComplete_materialized`
  WellNormalized `normalize_wellNormalized`
  noop entry     `normalize_entry_noop`
  keep           `rfl` — the bundle takes the default filter

This is the optimality analogue of `LCM.runLcm_normalized_preserves_diverges`, which exists for the same
reason: to rule out the headline being vacuously true for want of a bundle meeting its side conditions.
The only remaining hypotheses are about the *run* (`hrun`/`hfin`/`hks`) and the *competitor*
(`pl`/`hcov`), which is where they belong — `pl` is never constructed, so the bound really is against
every safe placement.
-/

namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Normalize Std
open BaseLanguage.Analyses.LCM

/-- **Computational optimality of LCM on the compiler's own bundle.** For any well-formed, fully
    reachable source program, the normalized program the compiler feeds to LCM, optimized with the solved
    seven-ghost bundle, evaluates `e` no more often along its complete run than any safe placement `pl`
    does over the source path.

    Every side condition of `transform_evalCount_le_safe` is discharged; what remains is the run and the
    competing placement. -/
theorem normalized_evalCount_le_safe {P : Program} (hwf : WellFormed P) (har : AllReachable P)
    {e : Expr} (hnum : isNumbered e = true) (pl : Node → Bool)
    {σ : Store} {c_f : Config} (ks : Nat)
    (hrun : Steps (normalize P) ⟨(normalize P).entry, σ⟩ c_f)
    (hfin : Final (normalize P) c_f)
    (hks : run (normalize P) ⟨(normalize P).entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCovers (normalize P)
              (lcmMatSolved (normalize P) (normalize_wellNormalized P hwf har).wf)
              e pl ⟨(normalize P).entry, σ⟩ ks false) :
    -- `N` is the program the compiler feeds to LCM; `S` its solved seven-ghost bundle; `T` the optimized
    -- program. Bound here rather than spelled out, so the statement reads as the inequality it is.
    let N := normalize P
    let S := lcmMatSolved N (normalize_wellNormalized P hwf har).wf
    let T := transform N S
    ∃ kt τf,
      run T ⟨blockOff N S N.entry, σ⟩ kt
        = (⟨blockOff N S c_f.node, τf⟩, .next ⟨blockOff N S c_f.node, τf⟩)
      ∧ evalCount T e ⟨blockOff N S N.entry, σ⟩ kt
        ≤ ((runNodes N ⟨N.entry, σ⟩ ks).filter pl).length := by
  intro N S T
  obtain ⟨ne, hen⟩ := normalize_entry_noop P
  have wn : WellNormalized N := normalize_wellNormalized P hwf har
  exact transform_evalCount_le_safe S (lcmMatSolved_extremal N wn.wf)
    (gateSound_materialized S rfl)
    (gateComplete_materialized S rfl (lcmMatSolved_extremal N wn.wf)
      (lcmMatSolved_extremalMat N wn.wf) wn hen)
    wn hnum rfl pl hrun hfin ks hks hcov

#assert_clean_axioms normalized_evalCount_le_safe

end BaseLanguage.Analyses.LcmMat
