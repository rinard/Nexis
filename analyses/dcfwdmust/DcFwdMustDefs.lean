-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals

/-! # `DcFwdMustDefs` — floor/ceiling families for the doubly-clamped forward-must demonstrator (`resFMC`). -/

namespace BaseLanguage.Analyses.DcFwdMust

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

/-- The floor clamp `lo`: the gen expressions. -/
def dcfmLo (P : Program) (n : Node) : Exprs := genExprs P n

/-- The ceiling clamp `hi`: `gen ∪ transp` (band is union-left). -/
def dcfmHi (P : Program) (n : Node) : Exprs := (genExprs P n).union (transpExprs P n)

end BaseLanguage.Analyses.DcFwdMust
