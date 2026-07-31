-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.BwdChain` — a NON-DIAMOND backward-must anticipation analysis.

`g n` = the definition-nodes anticipated on entry to `n`, computed by an **arbitrary monotone `predict`
RHS** — the three-way union `genDefs(n) ∪ (g(n') ∩ transpDefs(n)) ∪ extraN(n)`, past the canonical diamond,
so it drives the general backward path (`Lower.lowerSetExpr` + `Emit.flowBwd`). The extra `∪ extraN` term
makes it non-diamond and is meaningful: observable definitions are always anticipated (the program output).

Base node-locals (`allDefs`/`genDefs`/`transpDefs`) come from `Tac.Locals` via `include Tac.Locals`. This
file authors only the analysis's own additions: `extraN` — a node-indexed wrapper of the CONSTANT
`Tac.Locals.obsDefs` — and the `ceilN` ceiling composite. Surface `BwdChain.gsl`; `_sub` in `BwdChainDefsSub`.
-/
namespace BaseLanguage.Analyses.BwdChain
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

/-- The non-diamond extra term (observable definitions, always anticipated) — a node-indexed wrapper of
    the constant `Tac.Locals.obsDefs`, so it reads at `n` as a transfer summand. -/
def extraN (P : Program) (_n : Node) : Defs := Tac.Locals.obsDefs P
/-- The `check` ceiling — a genuine upper bound: `genDefs(n) ∪ transpDefs(n) ∪ extraN(n)`. -/
def ceilN (P : Program) (n : Node) : Defs := (genDefs P n).union ((transpDefs P n).union (extraN P n))

-- The `BwdChain` clause predicate is emitted by GenGeneral (`emitClauses`/`printEvs`).
end BaseLanguage.Analyses.BwdChain
