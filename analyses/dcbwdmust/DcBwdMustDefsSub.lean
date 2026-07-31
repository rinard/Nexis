-- Copyright (c) 2026 Martin Rinard
import analyses.dcbwdmust.DcBwdMustDefs
import BaseLanguage.IR.LocalsSub

/-!
# `DcBwdMustDefsSub` — the `_sub` (⊆ universe) domain facts + the band `dcbmLo ⊆ dcbmHi`.

These are the authored obligations the generated `DcBwdMust` `Solve` threads into `resBMC_correct`:
`dcbmLo_sub`/`dcbmHi_sub` discharge `hlo`/`hhi` (⊆ the universe `allExprs`); `dcbmLo_sub_dcbmHi` is the
band hypothesis `hlohi` (`lo ⊆ hi`) that makes the clean floor clause hold.
-/

namespace BaseLanguage.Analyses.DcBwdMust

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

theorem dcbmLo_sub (P : Program) (n : Node) : ∀ x ∈ dcbmLo P n, x ∈ allExprs P :=
  fun x hx => genExprs_sub P n x hx

theorem dcbmHi_sub (P : Program) (n : Node) : ∀ x ∈ dcbmHi P n, x ∈ allExprs P :=
  fun x hx => (Exprs.mem_union.mp hx).elim (genExprs_sub P n x) (transpExprs_sub P n x)

/-- The band: `dcbmLo ⊆ dcbmHi` — union-left, a one-liner. -/
theorem dcbmLo_sub_dcbmHi (P : Program) : ∀ n, ∀ x ∈ dcbmLo P n, x ∈ dcbmHi P n :=
  fun _ x hx => Exprs.mem_union.mpr (Or.inl hx)

end BaseLanguage.Analyses.DcBwdMust
