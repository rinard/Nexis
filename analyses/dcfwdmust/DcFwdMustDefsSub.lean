-- Copyright (c) 2026 Martin Rinard
import analyses.dcfwdmust.DcFwdMustDefs
import BaseLanguage.IR.LocalsSub

/-! # `DcFwdMustDefsSub` — `_sub` (⊆ universe) + the band `dcfmLo ⊆ dcfmHi` for `DcFwdMust`. -/

namespace BaseLanguage.Analyses.DcFwdMust

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

theorem dcfmLo_sub (P : Program) (n : Node) : ∀ x ∈ dcfmLo P n, x ∈ allExprs P :=
  fun x hx => genExprs_sub P n x hx

theorem dcfmHi_sub (P : Program) (n : Node) : ∀ x ∈ dcfmHi P n, x ∈ allExprs P :=
  fun x hx => (Exprs.mem_union.mp hx).elim (genExprs_sub P n x) (transpExprs_sub P n x)

/-- The band: `dcfmLo ⊆ dcfmHi` (union-left). -/
theorem dcfmLo_sub_dcfmHi (P : Program) : ∀ n, ∀ x ∈ dcfmLo P n, x ∈ dcfmHi P n :=
  fun _ x hx => Exprs.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.DcFwdMust
