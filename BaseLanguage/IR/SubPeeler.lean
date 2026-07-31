-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Fold

/-!
# `IR.SubPeeler` — the shared `_sub` fold-peeling tactic.

Every "gen/kill family ⊆ its fold universe" `_sub` proof is the same skeleton over `foldl_union_contrib`,
varying only in the family, the set-type namespace (which supplies `union`/`mem_union`/`empty`), the
universe, and the reduction lemmas that collapse `f P n` to `∅` in the out-of-range branch. `fold_sub`
captures that skeleton once, so a family's containment proof is a single line. Two universe shapes are
handled by one `first`: a bare `union`-fold (`allExprs = ⋃ₙ genExprs n`) and a seeded `obs ∪ ⋃…` fold
(`allVars`).

Because it references the caller's `P`/`n` binders, both are passed positionally. This is proof-authoring
metadata for the authored `_sub` companions (`IR.LocalsSub`, the per-analysis `…DefsSub`); it lives under
`IR/`, never touching the verified `BaseLanguage/Analysis/Solver/*` transfer backend.
-/

open Lean BaseLanguage.Tac BaseLanguage.IR.SetFold in
/-- Prove `(<fam> P n).Subset (<univ> P)` for a `union`-fold family. `set` names the set-type namespace
    (so `<set>.union`/`<set>.mem_union`/`<set>.empty`); `close` lists the extra lemmas that reduce
    `<fam> P n` to `∅` when `P.fetch n = none`. One `first` handles the bare-fold and seeded-fold
    universes alike. -/
macro "fold_sub " fam:ident P:ident n:ident " into " univ:ident " set " ns:ident
      " close " "[" close:term,+ "]" : tactic => do
  let nm := ns.getId
  let u  := mkIdentFrom ns (nm ++ `union)
  let mu := mkIdentFrom ns (nm ++ `mem_union)
  let em := mkIdentFrom ns (nm ++ `empty)
  let cs := close.getElems
  `(tactic| (
    intro x hx
    unfold $univ:ident
    by_cases hn : ($n) < ($P).size
    · first
        | (refine BaseLanguage.IR.SetFold.foldl_union_contrib (· ∈ ·) $u:ident (fun _ _ _ => $mu:ident) _
              (List.range ($P).size) ∅ (List.mem_range.mpr hn) ?_
           first
             | exact hx | exact ($mu:ident).mpr (Or.inl hx) | exact ($mu:ident).mpr (Or.inr hx)
             | (unfold $fam:ident at hx; split at hx <;>
                  first | exact ($mu:ident).mpr (Or.inl hx) | exact ($mu:ident).mpr (Or.inr hx)
                        | simp_all [$em:ident]))
        | (refine ($mu:ident).mpr (Or.inr (BaseLanguage.IR.SetFold.foldl_union_contrib (· ∈ ·) $u:ident (fun _ _ _ => $mu:ident) _
              (List.range ($P).size) ∅ (List.mem_range.mpr hn) ?_))
           first
             | exact hx | exact ($mu:ident).mpr (Or.inl hx) | exact ($mu:ident).mpr (Or.inr hx)
             | (unfold $fam:ident at hx; split at hx <;>
                  first | exact ($mu:ident).mpr (Or.inl hx) | exact ($mu:ident).mpr (Or.inr hx)
                        | simp_all [$em:ident]))
    · exfalso
      have hnone : ($P).fetch ($n) = none := by
        cases hf : ($P).fetch ($n) with | none => rfl | some i => exact absurd (BaseLanguage.Semantics.fetch_lt hf) hn
      simp [$fam:ident, $[$cs:term],*, hnone] at hx))
