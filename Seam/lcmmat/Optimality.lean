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

/-- **The bundle the compiler actually runs**, named so the statements below can mention it without
    respelling `lcmMatSolved (normalize P) (normalize_wellNormalized P hwf har).wf` at every occurrence. -/
def normSolvedMat {P : Program} (hwf : WellFormed P) (har : AllReachable P) :
    LCM.LcmSpec (normalize P) :=
  lcmMatSolved (normalize P) (normalize_wellNormalized P hwf har).wf

/-- **The seven-ghost bundle is extremal in the six classical ghosts** — from the solver, via
    `lcmMatSolved_extremal`. Named for the same reason as its `.demand` counterpart. -/
theorem normSolvedMat_extremal {P : Program} (hwf : WellFormed P) (har : AllReachable P) :
    LCM.Extremal (normSolvedMat hwf har) :=
  lcmMatSolved_extremal (normalize P) (normalize_wellNormalized P hwf har).wf

/-- **…and its seventh ghost is greatest.** Kept apart from `Extremal` because a six-ghost bundle has no
    `ηₘ` to be greatest in; this is what the gate-completeness discharge needs. -/
theorem normSolvedMat_extremalMat {P : Program} (hwf : WellFormed P) (har : AllReachable P) :
    LCM.ExtremalMat (normSolvedMat hwf har) :=
  lcmMatSolved_extremalMat (normalize P) (normalize_wellNormalized P hwf har).wf

/-- **Computational optimality of LCM on the compiler's own bundle.** For any well-formed, fully
    reachable source program, the normalized program the compiler feeds to LCM, optimized with the solved
    seven-ghost bundle, evaluates `e` no more often along its complete run than any safe placement `pl`
    does over the source path.

    Every side condition of `transform_evalCount_le_safe` about the *analysis* is discharged here —
    extremality included (`lcmMatSolved_extremal`, `lcmMatSolved_extremalMat`), which is why no `Extremal`
    appears above. What remains is about the run (`hrun`/`hfin`/`hks`) and the competitor (`pl`/`hcov`),
    and `pl` is never constructed, so the bound really is against every safe placement. -/
theorem normalized_evalCount_le_safe_mat {P : Program} (hwf : WellFormed P) (har : AllReachable P)
    {e : Expr} (hnum : isNumbered e = true) (pl : Node → Bool)
    {σ : Store} {c_f : Config} (ks : Nat)
    (hrun : Steps (normalize P) ⟨(normalize P).entry, σ⟩ c_f)
    (hfin : Final (normalize P) c_f)
    (hks : run (normalize P) ⟨(normalize P).entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCovers (normalize P) (normSolvedMat hwf har) e pl ⟨(normalize P).entry, σ⟩ ks false) :
    let N := normalize P
    let S := normSolvedMat hwf har
    let T := transform N S
    ∃ kt τf,
      run T ⟨blockOff N S N.entry, σ⟩ kt
        = (⟨blockOff N S c_f.node, τf⟩, .next ⟨blockOff N S c_f.node, τf⟩)
      ∧ evalCount T e ⟨blockOff N S N.entry, σ⟩ kt
        ≤ ((runNodes N ⟨N.entry, σ⟩ ks).filter pl).length := by
  intro N S T
  obtain ⟨ne, hen⟩ := normalize_entry_noop P
  have wn : WellNormalized N := normalize_wellNormalized P hwf har
  exact transform_evalCount_le_safe S (normSolvedMat_extremal hwf har)
    (gateSound_materialized S rfl)
    (gateComplete_materialized S rfl (normSolvedMat_extremal hwf har)
      (normSolvedMat_extremalMat hwf har) wn hen)
    wn hnum rfl pl hrun hfin ks hks hcov

#assert_clean_axioms normSolvedMat_extremal
#assert_clean_axioms normSolvedMat_extremalMat
#assert_clean_axioms normalized_evalCount_le_safe_mat

end BaseLanguage.Analyses.LcmMat
