-- Copyright (c) 2026 Martin Rinard
import analyses.lcm.LcmAdapter
import BaseLanguage.Meta.AxiomCheck
/-! # LCM adapter — the generated Solve → the `LcmSpec` bundle interface (hand-written).

`BaseLanguage/LCM/Transform.lean` and the LCM/PRE correctness + optimality developments are generic over
a valid, extremal `LcmSpec P` bundle (six ghosts + witnesses). The generator (`GenGeneral`, from
`Lcm.gsl`) emits the loose per-ghost `<ghost>Sol` + `<ghost>Sol_valid` (validity) and
`<ghost>_greatest`/`_least` (extremality). This file assembles those into the bundle structure, so the
verified transform runs on the generated solver unchanged. Hand-written because the bundle's field names /
`solve` memoization / decoders are compiler-specific — emitting them would couple the general generator to
LCM internals. (Lives in the `generated` lib to avoid an import cycle: it depends on `lcm.ValidExtremal`.) -/
namespace BaseLanguage.Analyses.LCM
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std

/-- The solved LCM bundle, assembled from the new Solve's validity witnesses. The memoizing `solve`
    bundle is bound to a single `let` so every ghost fixpoint array runs **once** (the bundle is a
    structure ⇒ arity-1 ⇒ no eta-expansion / per-node re-solve). Each `decFExpr P sol.x` is zeta-defeq
    to the corresponding `<x>Sol P = decFExpr P (solve P).x`, so the `<x>Sol_valid` witnesses typecheck. -/
def lcmSolved (P : Program) (wf : WellFormed P) : LcmSpec P :=
  let sol := solve P
  { πₐ    := decFExpr P sol.πₐ
    ηₐ   := decFExpr P sol.ηₐ
    ηₚ   := decFExpr P sol.ηₚ
    τₚ    := decFExpr P sol.τₚ
    πᵤ    := decFExpr P sol.πᵤ
    τᵤ := decFExpr P sol.τᵤ
    isAnti    := πₐSol_valid P wf
    isAvail   := ηₐSol_valid P wf
    isPostp   := ηₚSol_valid P wf
    isTauP    := τₚSol_valid P wf
    isUsed    := πᵤSol_valid P wf
    isUsedOut := τᵤSol_valid P wf
    -- `Lcm.gsl` has six ghosts, so there is no solved `ηₘ` here; the empty set is a valid
    -- `Materialized` (every clause is an upper bound, and `∅` satisfies each vacuously). It is *not*
    -- the greatest one, so this bundle satisfies no `ExtremalMat` and would replace nothing under the
    -- `.materialized` gate — which is why it ships `.demand`. The seventh ghost is
    -- `LcmMat.lcmMatSolved`.
    ηₘ        := fun _ => Assignments.empty
    -- no seventh ghost to read, so this bundle ships the classical gate — which it can afford, being
    -- extremal (`lcmSolved_extremal` below)
    gate      := .demand
    isMat     := ⟨fun _ _ _ _ he => absurd he Std.HashSet.not_mem_empty,
                  fun _ he => absurd he Std.HashSet.not_mem_empty,
                  fun _ _ he => absurd he Std.HashSet.not_mem_empty⟩ }

/-- …and it is extremal in the six classical ghosts — the `Extremal` predicate the classical `.demand`
    gate's correctness proof and the optimality development both consume. The seventh ghost's
    greatest-ness (`ExtremalMat`) is a separate predicate precisely so that this bundle, which has no
    seventh ghost, can still be `Extremal`. -/
theorem lcmSolved_extremal (P : Program) (wf : WellFormed P) : Extremal (lcmSolved P wf) where
  πₐ    := πₐ_greatest P wf
  ηₐ   := ηₐ_greatest P wf
  ηₚ   := ηₚ_greatest P wf
  τₚ    := τₚ_greatest P wf
  πᵤ    := πᵤ_least P wf
  τᵤ := τᵤ_least P wf

#assert_clean_axioms lcmSolved
#assert_clean_axioms lcmSolved_extremal
end BaseLanguage.Analyses.LCM
