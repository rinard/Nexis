-- Copyright (c) 2026 Martin Rinard
import analyses.pdce.PdceAdapter
import BaseLanguage.Meta.AxiomCheck
/-! # PDCE adapter — the generated Solve → the `PdceSpec` bundle interface (hand-written).

`BaseLanguage/PDCE/Transform.lean` and the PDCE correctness developments are generic over a valid,
extremal `PdceSpec P` bundle (`Sink`/`Live` ghosts + witnesses). The generator (`GenGeneral`, from
`Pdce.gsl`) emits the loose per-ghost `ηSol`/`πSol` + `ηSol_valid`/`πSol_valid` (validity) and
`η_greatest`/`π_least` (extremality). This file assembles those into the bundle structure, so the
verified transform runs on the generated solver unchanged. Hand-written because the bundle's field names /
`solve` memoization / decoders are compiler-specific — emitting them would couple the general generator to
PDCE internals. (Lives in the `generated` lib to avoid an import cycle: it depends on `pdce.ValidExtremal`.) -/
namespace BaseLanguage.Analyses.PDCE
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std

/-- The solved PDCE bundle, assembled from the new Solve's validity witnesses. The memoizing `solve`
    bundle is bound once (arity-1 structure ⇒ no per-node re-solve); `decFVar/Asgn P sol.x` is zeta-defeq
    to `<x>Sol P`, so the `<x>Sol_valid` witnesses typecheck. -/
def pdceSolved (P : Program) (wf : WellFormed P) : PdceSpec P :=
  let sol := solve P
  { π   := decFVar P sol.π
    η   := decFAsgn P sol.η
    isLive := πSol_valid P wf
    isSink := ηSol_valid P wf }

/-- …and it is extremal (least `Live`, greatest `Sink`) — the `Extremal` predicate the optimality
    development consumes. -/
theorem pdceSolved_extremal (P : Program) (wf : WellFormed P) : Extremal (pdceSolved P wf) where
  π := π_least P wf
  η := η_greatest P wf

#assert_clean_axioms pdceSolved
#assert_clean_axioms pdceSolved_extremal
end BaseLanguage.Analyses.PDCE
