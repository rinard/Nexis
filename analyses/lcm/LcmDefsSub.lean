-- Copyright (c) 2026 Martin Rinard
import analyses.lcm.LcmDefs
import BaseLanguage.IR.SubPeeler

/-!
# `LCM.LcmDefsSub` — the node-local + placement `_sub` (⊆ universe) domain lemmas.

For every own def/placement `f`, the fact `f P … n ⊆ allExprs P` (needed for the `MTC.Wf` obligation).
Authored domain facts (like the base-family `BaseLanguage/IR/LocalsSub.lean`), so the general generator
(`GenGeneral`) references them by the mechanical name `<fam>_sub`. The generic set-combinator subset lemmas
(`interL_sub`/`union_sub`/…) and the placement `_sub` (which thread the foreign ghosts' `_sub` as
hypotheses) live here too. Each is axiom-clean.
-/

namespace BaseLanguage.Analyses.LCM
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem interL_sub {a b c : Assignments} (h : a.Subset c) : (a.inter b).Subset c := fun x hx => h x (Assignments.mem_inter.mp hx).1
theorem interR_sub {a b c : Assignments} (h : b.Subset c) : (a.inter b).Subset c := fun x hx => h x (Assignments.mem_inter.mp hx).2
theorem diffL_sub {a b c : Assignments} (h : a.Subset c) : (a.sdiff b).Subset c := fun x hx => h x (Assignments.mem_sdiff.mp hx).1
theorem union_sub {a b c : Assignments} (ha : a.Subset c) (hb : b.Subset c) : (a.union b).Subset c := fun x hx => (Assignments.mem_union.mp hx).elim (ha x) (hb x)

theorem ue_sub (P : Program) (n : Node) : (ue P n).Subset (allExprs P) := by
  fold_sub ue P n into allExprs set Assignments close [Assignments.empty]

theorem pass_sub (P : Program) (n : Node) : (pass P n).Subset (allExprs P) := fun x hx => (Analysis.SetOps.mem_filter'.mp hx).1

theorem haltSeed_sub (P : Program) : (haltSeed P).Subset (allExprs P) := by
  intro x hx; simp [haltSeed, Assignments.empty] at hx

theorem de_sub (P : Program) (n : Node) : (de P n).Subset (allExprs P) := by
  simp only [de]
  repeat first
    | with_reducible (exact ue_sub P _) | with_reducible (exact pass_sub P _) | with_reducible (exact Assignments.subset_refl)
    | with_reducible (apply interL_sub) | with_reducible (apply interR_sub)
    | with_reducible (apply diffL_sub) | with_reducible (apply union_sub)

theorem entrySeed_sub (P : Program) : (entrySeed P).Subset (allExprs P) := by
  intro x hx; simp [entrySeed, Assignments.empty] at hx

theorem earliest_sub (P : Program) (anti avail : Node → Assignments) (hanti : ∀ n, (anti n).Subset (allExprs P)) (havail : ∀ n, (avail n).Subset (allExprs P)) (i j : Node) :
    (earliest P anti avail i j).Subset (allExprs P) := by
  simp only [earliest, compl, availableOut, de]
  repeat first
    | exact hanti _ | exact havail _ | with_reducible (exact Assignments.subset_refl)
    | with_reducible (apply interL_sub) | with_reducible (apply interR_sub)
    | with_reducible (apply diffL_sub) | with_reducible (apply union_sub)

theorem latestNode_sub (P : Program) (postp tauP : Node → Assignments) (hpostp : ∀ n, (postp n).Subset (allExprs P)) (htauP : ∀ n, (tauP n).Subset (allExprs P)) (n : Node) :
    (latestNode P postp tauP n).Subset (allExprs P) := by
  simp only [latestNode, compl]
  repeat first
    | exact hpostp _ | exact htauP _ | with_reducible (exact Assignments.subset_refl)
    | with_reducible (apply interL_sub) | with_reducible (apply interR_sub)
    | with_reducible (apply diffL_sub) | with_reducible (apply union_sub)

theorem latestEdge_sub (P : Program) (anti avail postp : Node → Assignments) (hanti : ∀ n, (anti n).Subset (allExprs P)) (havail : ∀ n, (avail n).Subset (allExprs P)) (hpostp : ∀ n, (postp n).Subset (allExprs P)) (i j : Node) :
    (latestEdge P anti avail postp i j).Subset (allExprs P) := by
  simp only [latestEdge, earliest, compl, availableOut, de]
  repeat first
    | exact hanti _ | exact havail _ | exact hpostp _ | with_reducible (exact Assignments.subset_refl)
    | with_reducible (apply interL_sub) | with_reducible (apply interR_sub)
    | with_reducible (apply diffL_sub) | with_reducible (apply union_sub)

end BaseLanguage.Analyses.LCM
