-- Copyright (c) 2026 Martin Rinard
import analyses.dcfwdmay.DcFwdMayDefs
import BaseLanguage.IR.LocalsSub

/-! # `DcFwdMayDefsSub` — `_sub` + band `dcfmayLo ⊆ dcfmayHi` for `DcFwdMay`. -/

namespace BaseLanguage.Analyses.DcFwdMay

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

theorem dcfmayLo_sub (P : Program) (n : Node) : ∀ x ∈ dcfmayLo P n, x ∈ allExprs P :=
  fun x hx => genExprs_sub P n x hx

theorem dcfmayHi_sub (P : Program) (n : Node) : ∀ x ∈ dcfmayHi P n, x ∈ allExprs P :=
  fun x hx => (Exprs.mem_union.mp hx).elim (genExprs_sub P n x) (transpExprs_sub P n x)

theorem dcfmayLo_sub_dcfmayHi (P : Program) : ∀ n, ∀ x ∈ dcfmayLo P n, x ∈ dcfmayHi P n :=
  fun _ x hx => Exprs.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.DcFwdMay
