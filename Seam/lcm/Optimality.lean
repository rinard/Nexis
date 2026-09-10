-- Copyright (c) 2026 Martin Rinard
import Seam.lcm.Adapter
import BaseLanguage.LCM.EvalCountHeadline
import BaseLanguage.Normalize.Sim

/-!
# Computational optimality for the **shipped default**, with every side condition discharged

`transform_evalCount_le_safe` states computational optimality abstractly — over any bundle that is
`Extremal`, whose replace gate is `GateSound` and `GateComplete`, on a `WellNormalized` program. That
abstraction is deliberate (it is what keeps the two gates' proofs disjoint), but it leaves the headline
without a witness that some bundle satisfies all four at once.

This file supplies one for the configuration the compiler runs by default: the six-ghost analysis
(`analyses/lcm/Lcm.gsl`) with the classical KRS **demand** gate, on a normalized program.

  Extremal       `lcmSolved_extremal`
  GateSound      `gateSound_demand` — needs `Extremal`, `WellNormalized`, the noop entry
  GateComplete   `gateComplete_demand _ rfl` — trivial: `covSet = demandSet` for this gate
  WellNormalized `normalize_wellNormalized`
  noop entry     `normalize_entry_noop`
  keep           `rfl` — the bundle takes the default filter

Note where extremality sits. It is *discharged* here rather than assumed, but it is genuinely needed:
`gateSound_demand` rests on `πᵤ` being the least solution, and optimality rests on extremality in its own
right, since the bound is against every competing placement. The seventh-ghost counterpart
(`LcmMat.normalized_evalCount_le_safe_mat`) differs only in that its *correctness* obligation is
discharged from validity — its optimality obligation still needs extremality, and always will.

The analogue of `LCM.runLcm_normalized_preserves_diverges` for the eval-count claim: it rules out the
headline holding only for want of a bundle meeting its side conditions.
-/

namespace BaseLanguage.Analyses.LCM
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Normalize Std

/-- **The default bundle the compiler runs**, named so the statement below can mention it without
    respelling `lcmSolved (normalize P) (normalize_wellNormalized P hwf har).wf` at every occurrence. -/
def normSolved {P : Program} (hwf : WellFormed P) (har : AllReachable P) :
    LcmSpec (normalize P) :=
  lcmSolved (normalize P) (normalize_wellNormalized P hwf har).wf

/-- **The default bundle is extremal.** Named, rather than re-derived inline, so "where does extremality
    come from?" is answerable by a reference: it comes from the solver, via the generated per-ghost
    `_greatest`/`_least` theorems that `lcmSolved_extremal` assembles. It is a fact about the worklist's
    output, never a hypothesis the caller supplies. -/
theorem normSolved_extremal {P : Program} (hwf : WellFormed P) (har : AllReachable P) :
    Extremal (normSolved hwf har) :=
  lcmSolved_extremal (normalize P) (normalize_wellNormalized P hwf har).wf

/-- **Computational optimality of LCM on the compiler's default bundle.** For any well-formed, fully
    reachable source program, the normalized program the compiler feeds to LCM, optimized with the solved
    six-ghost bundle under the classical demand gate, evaluates `e` no more often along its complete run
    than any safe placement `pl` does over the source path.

    Every side condition of `transform_evalCount_le_safe` about the *analysis* is discharged here —
    extremality included (`lcmSolved_extremal`), which is why no `Extremal` appears above. What remains is
    about the run (`hrun`/`hfin`/`hks`) and the competitor (`pl`/`hcov`), and `pl` is never constructed,
    so the bound really is against every safe placement. -/
theorem normalized_evalCount_le_safe {P : Program} (hwf : WellFormed P) (har : AllReachable P)
    {e : Expr} (hnum : isNumbered e = true) (pl : Node → Bool)
    {σ : Store} {c_f : Config} (ks : Nat)
    (hrun : Steps (normalize P) ⟨(normalize P).entry, σ⟩ c_f)
    (hfin : Final (normalize P) c_f)
    (hks : run (normalize P) ⟨(normalize P).entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCovers (normalize P) (normSolved hwf har) e pl ⟨(normalize P).entry, σ⟩ ks false) :
    let N := normalize P
    let S := normSolved hwf har
    let T := transform N S
    ∃ kt τf,
      run T ⟨blockOff N S N.entry, σ⟩ kt
        = (⟨blockOff N S c_f.node, τf⟩, .next ⟨blockOff N S c_f.node, τf⟩)
      ∧ evalCount T e ⟨blockOff N S N.entry, σ⟩ kt
        ≤ ((runNodes N ⟨N.entry, σ⟩ ks).filter pl).length := by
  intro N S T
  obtain ⟨ne, hen⟩ := normalize_entry_noop P
  have wn : WellNormalized N := normalize_wellNormalized P hwf har
  exact transform_evalCount_le_safe S (normSolved_extremal hwf har)
    (gateSound_demand S rfl (normSolved_extremal hwf har) wn hen)
    (gateComplete_demand S rfl)
    wn hnum rfl pl hrun hfin ks hks hcov

#assert_clean_axioms normSolved_extremal
#assert_clean_axioms normalized_evalCount_le_safe

end BaseLanguage.Analyses.LCM
