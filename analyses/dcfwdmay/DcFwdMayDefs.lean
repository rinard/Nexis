-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals

/-! # `DcFwdMayDefs` — floor/ceiling families for the doubly-clamped forward-may demonstrator (`resFmC`). -/

namespace BaseLanguage.Analyses.DcFwdMay

open BaseLanguage.Tac BaseLanguage.Tac.Locals Std

def dcfmayLo (P : Program) (n : Node) : Exprs := genExprs P n
def dcfmayHi (P : Program) (n : Node) : Exprs := (genExprs P n).union (transpExprs P n)

end BaseLanguage.Analyses.DcFwdMay
