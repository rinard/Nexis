-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.BwdMay` — a NON-DIAMOND backward-may liveness analysis (general `predict`, least fixpoint).

`m n` = the definition-nodes live at `n`, bounded below by `genDefs(n) ∪ (m(n') ∩ transpDefs(n)) ∪ extraM(n)`
with a floor clamp. The extra `∪ extraM` term makes the transfer non-diamond and drives the general
backward path (`lowerSetExpr` + `flowBwd` pass-through, `resMTCB_correct`).

Base node-locals (`allDefs`/`genDefs`/`transpDefs`) come from `Tac.Locals` via `include Tac.Locals`.
This file authors only the analysis's own additions: `extraM`/`floorM` — node-indexed *wrappers* of the
CONSTANT `Tac.Locals.obsDefs` (a transfer summand is read at `n`, so a bare constant can't stand in).
Surface `BwdMay.gsl`; `_sub` in `BwdMayDefsSub`.
-/
namespace BaseLanguage.Analyses.BwdMay
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

/-- The non-diamond extra term (observable definitions, always live) — a node-indexed wrapper of the
    constant `Tac.Locals.obsDefs`, so it reads at `n` as a transfer summand. -/
def extraM (P : Program) (_n : Node) : Defs := Tac.Locals.obsDefs P
/-- The `check` floor (= `extraM`): the observable definitions are a genuine non-trivial lower bound,
    forced in even at the boundary where the transfer is empty. -/
def floorM (P : Program) (n : Node) : Defs := extraM P n

-- The `BwdMay` clause predicate is emitted by GenGeneral (`emitClauses`/`printEvs`).
end BaseLanguage.Analyses.BwdMay
