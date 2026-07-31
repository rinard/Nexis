-- Copyright (c) 2026 Martin Rinard
import analyses.dcbwdmay.DcBwdMayDefs
import BaseLanguage.IR.LocalsSub

/-! # `DcBwdMayDefsSub` — `_sub` + band `dcbmayLo ⊆ dcbmayHi` for `DcBwdMay`. -/

namespace BaseLanguage.Analyses.DcBwdMay

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

theorem dcbmayLo_sub (P : Program) (n : Node) : ∀ x ∈ dcbmayLo P n, x ∈ allExprs P :=
  fun x hx => genExprs_sub P n x hx

theorem dcbmayHi_sub (P : Program) (n : Node) : ∀ x ∈ dcbmayHi P n, x ∈ allExprs P :=
  fun x hx => (Exprs.mem_union.mp hx).elim (genExprs_sub P n x) (transpExprs_sub P n x)

theorem dcbmayLo_sub_dcbmayHi (P : Program) : ∀ n, ∀ x ∈ dcbmayLo P n, x ∈ dcbmayHi P n :=
  fun _ x hx => Exprs.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.DcBwdMay
