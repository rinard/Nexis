-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.SelfRead
import BaseLanguage.Normalize.DeDeg
import BaseLanguage.Normalize.PrependEntry
import BaseLanguage.Normalize.FreshSupply

/-!
# `Normalize.Normalize` — the normal-form composition

`normalize P = prependEntry (deDeg (normalizeSelfRead P (freshN P)))` runs the three structural
pre-passes in order. Given the shipped optimizer's input preconditions (`WellFormed`, `AllReachable`),
the result is `WellNormalized`: each field is established by one pass and preserved by the later ones. There is **no** `splitCriticalEdges`
pass: LCM realizes edge placement directly via per-branch `ifz` edge chains, so `NoCriticalEdges` is not
required (dropped from `WellNormalized`). The accompanying fresh-temp supply `freshN (normalize P)` (with
`freshN_freshForN` / `freshN_nonobs`) is the per-pass input a subsequent verified optimization (PRE) consumes.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

/-- **The normal-form pre-pass composition.** No `splitCriticalEdges`: the LCM transform realizes edge
    placement directly via per-branch edge chains (`insertEdge`), so critical edges need not be removed. -/
def normalize (P : Program) : Program :=
  prependEntry (deDeg (normalizeSelfRead P (freshN P)))

/-- The offset supply dodges each node's own RHS operands — the `normalize_noSelfRead` hypothesis. -/
theorem normalize_hfresh (P : Program) :
    ∀ {nd x e next}, P.fetch nd = some (.assign x e next) →
      exprReadsVar e (freshN P nd) = false := by
  intro nd x e next h
  have hunread : freshN P nd ∉ exprVars e := (freshN_freshForN P).unread nd h
  cases hr : exprReadsVar e (freshN P nd) with
  | false => rfl
  | true => exact absurd (readsVar_imp_mem hr) hunread

/-- **`normalize` produces a `WellNormalized` program** from the two shipped preconditions.
    `normalizeSelfRead` establishes `NoSelfRead`; `deDeg` establishes `DistinctSuccs`; `prependEntry`
    establishes `EntryNoIncoming` + `EntryUnused`; and reachability/well-formedness thread through. -/
theorem normalize_wellNormalized (P : Program)
    (hwf : WellFormed P) (har : AllReachable P) :
    WellNormalized (normalize P) := by
  -- N := normalizeSelfRead P (freshN P)
  have hwfN : WellFormed (normalizeSelfRead P (freshN P)) := normalize_wellFormed P (freshN P) hwf
  have hnsN : NoSelfRead (normalizeSelfRead P (freshN P)) :=
    normalize_noSelfRead P (freshN P) (normalize_hfresh P)
  have harN : AllReachable (normalizeSelfRead P (freshN P)) := normalize_allReach P (freshN P) hwf har
  -- D := deDeg N
  have hwfD : WellFormed (deDeg (normalizeSelfRead P (freshN P))) := deDeg_wellFormed _ hwfN
  have hnsD : NoSelfRead (deDeg (normalizeSelfRead P (freshN P))) := deDeg_noSelfRead _ hnsN
  have hdsD : DistinctSuccs (deDeg (normalizeSelfRead P (freshN P))) := deDeg_distinctSuccs _
  have harD : AllReachable (deDeg (normalizeSelfRead P (freshN P))) := deDeg_allReach _ harN
  -- R := prependEntry D
  show WellNormalized (prependEntry (deDeg (normalizeSelfRead P (freshN P))))
  exact
    { wf := prependEntry_wellFormed hwfD
      noSelfRead := prependEntry_noSelfRead hnsD
      distinctSuccs := prependEntry_distinctSuccs hdsD
      entryNoIncoming := prependEntry_freshEntry hwfD
      allReach := prependEntry_allReach hwfD harD
      entryUnused := prependEntry_entryUnused _ }

/-- **`normalize` preserves the observable set.** Each of its three sub-passes does, structurally, so
    this is `rfl` — but stating it lets a caller rewrite instead of unfolding `normalize` at a large
    concrete argument, which is the difference between a cheap step and an expensive one. -/
@[simp] theorem normalize_obs (P : Program) : (normalize P).obs = P.obs := rfl

/-- The per-pass fresh-temp supply for the normalized program satisfies `FreshForN`. -/
theorem normalize_freshForN (P : Program) : FreshForN (normalize P) (freshN (normalize P)) :=
  freshN_freshForN (normalize P)

/-- …and is non-observable. -/
theorem normalize_nonobs (P : Program) : Nonobs (freshN (normalize P)) :=
  freshN_nonobs (normalize P)

end Normalize
end BaseLanguage
