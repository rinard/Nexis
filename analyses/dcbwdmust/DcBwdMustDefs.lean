-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals

/-!
# `DcBwdMustDefs` — floor/ceiling families for the doubly-clamped backward-must demonstrator.

`DcBwdMust` exercises the `resBMC` (cap-the-transfer, `lo ∪ gMTCBM`) emit path: a backward-must ghost
carrying BOTH a floor `dcbmLo` and a ceiling `dcbmHi`, with a provable band `dcbmLo ⊆ dcbmHi` (a one-line
union-left, `DcBwdMustDefsSub`). Both bounds are single families so the generator's `<lo>_sub`/`<hi>_sub`/
`<lo>_sub_<hi>` naming convention resolves.
-/

namespace BaseLanguage.Analyses.DcBwdMust

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

/-- The floor clamp `lo`: the gen expressions (a lower bound on the anticipated set). -/
def dcbmLo (P : Program) (n : Node) : Exprs := genExprs P n

/-- The ceiling clamp `hi`: `gen ∪ transp` — a genuine superset of the floor (the band is union-left). -/
def dcbmHi (P : Program) (n : Node) : Exprs := (genExprs P n).union (transpExprs P n)

end BaseLanguage.Analyses.DcBwdMust
