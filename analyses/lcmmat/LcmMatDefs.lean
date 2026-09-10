-- Copyright (c) 2026 Martin Rinard
import analyses.lcm.LcmDefs

/-!
# `Analyses.LcmMat` — node-locals for the **materialization** ghost

The seventh LCM ghost, `Materialized ηₘ`, is availability of the *temporary* `tₑ` **in the transformed
program**. It exists so the transform's replace gate can read a ghost instead of reconstructing
recoverability from `πᵤ`.

Why that matters. The classical gate is `recoverable = πᵤK ∪ insertBefore`, and keeping it honest — never
replacing an original computation by a read of a temporary that was never written — is exactly what forces
LCM's correctness proof to assume `Extremal S` rather than mere validity: a too-large `πᵤ` admits a
replacement with no matching insertion (`examples/lcm-extremality/ExtremalityNeeded.lean`). Ruling that out
needs a *lower* bound on a least fixpoint, which no clause can impose.

`ηₘ` inverts the polarity. Its single `update` clause is an **upper** bound — everything available at `n'`
was either placed on the way in, or was available at `n` and survived `n`'s instruction — which is the
soundness statement itself, and is the direction every clause already expresses. Validity therefore
suffices; extremality of `ηₘ` only widens how much gets replaced, i.e. optimality.

The two node-locals below are the transform's own insert sets (`BaseLanguage/LCM/Transform.lean`) restated
without a `LcmSpec` parameter, so a `.gsl` clause can name them:

* `nodeGen` = `insertBefore` — written at `n`'s entry, *before* `n`'s instruction, so it is subject to the
  transparency filter `pass(n)` on the way out;
* `edgeGen` = `insertEdge` — written *after* `n`'s instruction, on the edge, so it is not.

That phase difference is why the clause is not the usual `gen ∪ (self ∩ transp)` diamond: the node-entry
generator sits *inside* the transparency filter.

**Scope.** Both use the unfiltered `τᵤ` where the transform uses `τᵤK = τᵤ ∩ keep`. They therefore describe
the *classical* mode exactly; under `--lcm=safe` the filter removes insertions and `ηₘ` would over-state
availability. A `keep`-aware variant needs the filter to be visible to the analysis, which it deliberately
is not (it appears in no validity or extremality clause). See `LcmMat.gsl`.
-/

namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
open BaseLanguage.Analyses.LCM

/-! ## Re-exports

The generator names its module after the analysis and resolves every node-local in that namespace, so the
LCM node-locals this analysis reads are re-exported here rather than restated — the same shim pattern as
`analyses/pdcefault/PdceFaultDefs.lean`. Nothing below is new mathematics. -/

export BaseLanguage.Analyses.LCM
  (Assignments ue pass de allExprs entrySeed haltSeed compl availableOut
   earliest latestNode latestEdge Greatest Least Transfer)

namespace Assignments
export BaseLanguage.Analyses.LCM.Assignments
  (Subset union inter sdiff empty singleton
   mem_union mem_inter mem_sdiff subset_refl subset_trans Sup)
end Assignments

/-- `latestOut` without the `LcmSpec` parameter: the node-exit placement frontier. -/
def latestOutG (P : Program) (πₐ ηₐ ηₚ : Node → Assignments) (i : Node) : Assignments :=
  match P.fetch i with
  | some (.assign _ _ next) => latestEdge P πₐ ηₐ ηₚ i next
  | some (.noop next)       => latestEdge P πₐ ηₐ ηₚ i next
  | some (.ifz _ z nz)      => Assignments.union (latestEdge P πₐ ηₐ ηₚ i z)
                                                 (latestEdge P πₐ ηₐ ηₚ i nz)
  | _                       => Assignments.empty

/-- The **node-entry** generator — `Transform.insertBefore` with `τᵤK` relaxed to `τᵤ`. -/
def nodeGen (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments) (n : Node) : Assignments :=
  Assignments.inter (Assignments.sdiff (latestNode P ηₚ τₚ n) (latestOutG P πₐ ηₐ ηₚ n)) (τᵤ n)

/-- The **edge** generator — `Transform.insertEdge` with `τᵤK` relaxed to `τᵤ`. -/
def edgeGen (P : Program) (πₐ ηₐ ηₚ τᵤ : Node → Assignments) (i j : Node) : Assignments :=
  Assignments.inter (latestEdge P πₐ ηₐ ηₚ i j) (τᵤ i)

/-- The **kill** set at `n`: everything `n`'s instruction invalidates (the complement of `pass`). Naming
    the kill rather than the transparency is what puts the clause in the `place ∪ (self ∖ gres)` form the
    generator recognizes for a forward-must ghost that reads foreign ghosts. -/
def notPass (P : Program) (n : Node) : Assignments := Assignments.sdiff (allExprs P) (pass P n)

/-- The **placement** contributed along the step `n → n'`: the edge insert, plus the node-entry insert
    that survives `n`'s instruction. Folding the transparency filter over `nodeGen` into the placement is
    what lets the carry read as the plain `self ∖ notPass`. -/
def matPlace (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments) (i j : Node) : Assignments :=
  Assignments.union (edgeGen P πₐ ηₐ ηₚ τᵤ i j)
                    (Assignments.inter (nodeGen P πₐ ηₐ ηₚ τₚ τᵤ i) (pass P i))

end BaseLanguage.Analyses.LcmMat
