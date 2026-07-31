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
    isUsedOut := τᵤSol_valid P wf }

/-- …and it is extremal — the `Extremal` predicate the optimality development consumes. -/
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
