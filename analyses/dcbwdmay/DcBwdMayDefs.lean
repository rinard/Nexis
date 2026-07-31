-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals

/-! # `DcBwdMayDefs` — floor/ceiling families for the doubly-clamped backward-may demonstrator (`resBmC`). -/

namespace BaseLanguage.Analyses.DcBwdMay

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

def dcbmayLo (P : Program) (n : Node) : Exprs := genExprs P n
def dcbmayHi (P : Program) (n : Node) : Exprs := (genExprs P n).union (transpExprs P n)

end BaseLanguage.Analyses.DcBwdMay
