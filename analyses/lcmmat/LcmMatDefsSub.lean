-- Copyright (c) 2026 Martin Rinard
import analyses.lcmmat.LcmMatDefs
import analyses.lcm.LcmDefsSub

/-!
# `Analyses.LcmMat` — the universe bounds for the materialization node-locals.

Both generators end in `∩ τᵤ n`, so each is bounded by the caller's bound on the foreign ghost `τᵤ` —
the same shape as `earliest_sub` in `LcmDefsSub`, and it needs nothing about the placements themselves.
-/

namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
open BaseLanguage.Analyses.LCM

export BaseLanguage.Analyses.LCM
  (interL_sub interR_sub diffL_sub union_sub ue_sub pass_sub haltSeed_sub de_sub entrySeed_sub
   earliest_sub latestNode_sub latestEdge_sub)

theorem nodeGen_sub (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments)
    (hτᵤ : ∀ n, (τᵤ n).Subset (allExprs P)) (n : Node) :
    (nodeGen P πₐ ηₐ ηₚ τₚ τᵤ n).Subset (allExprs P) :=
  fun x hx => hτᵤ n x (Assignments.mem_inter.mp hx).2

theorem edgeGen_sub (P : Program) (πₐ ηₐ ηₚ τᵤ : Node → Assignments)
    (hτᵤ : ∀ n, (τᵤ n).Subset (allExprs P)) (i j : Node) :
    (edgeGen P πₐ ηₐ ηₚ τᵤ i j).Subset (allExprs P) :=
  fun x hx => hτᵤ i x (Assignments.mem_inter.mp hx).2

theorem notPass_sub (P : Program) (n : Node) : (notPass P n).Subset (allExprs P) :=
  fun x hx => (Assignments.mem_sdiff.mp hx).1

/-- The generator passes one universe bound per foreign ghost, in declaration order (the `earliest_sub`
    convention), so all five appear even though only `hτᵤ` is used — both generators end in `∩ τᵤ`. -/
theorem matPlace_sub (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments)
    (_hπₐ : ∀ n, (πₐ n).Subset (allExprs P)) (_hηₐ : ∀ n, (ηₐ n).Subset (allExprs P))
    (_hηₚ : ∀ n, (ηₚ n).Subset (allExprs P)) (_hτₚ : ∀ n, (τₚ n).Subset (allExprs P))
    (hτᵤ : ∀ n, (τᵤ n).Subset (allExprs P)) (i j : Node) :
    (matPlace P πₐ ηₐ ηₚ τₚ τᵤ i j).Subset (allExprs P) := by
  intro x hx
  rcases Assignments.mem_union.mp hx with h | h
  · exact edgeGen_sub P πₐ ηₐ ηₚ τᵤ hτᵤ i j x h
  · exact nodeGen_sub P πₐ ηₐ ηₚ τₚ τᵤ hτᵤ i x (Assignments.mem_inter.mp h).1

end BaseLanguage.Analyses.LcmMat
