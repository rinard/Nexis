-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-!
# `Analyses.PrimeAdd` — a COMPOUND-atom (`gather ∩ gate`) gated data-dependency analysis, fwd·may.

`g n` = the definition-nodes tracked on entry to `n`: the observable definitions (`obsGen`, added ungated
to prime the pump) plus every node `z` whose data-dependencies are all tracked AND for which some
observable is already tracked — the compound guard `below(z) ⊆ g(n) ∧ primes meets g(n)` (an AND-gather
intersected with a gate). Exercises `var`, `gather`, `gate`, `∧` (→ `inter`), and accumulate, all through
the one term-generic path. The gate is essential: with an empty seed a gate-only analysis would deadlock
(nothing enters `g`), so `obsGen` seeds the observables ungated and the gate arms once one is present.

Defs are real read-offs of the IR: `obsGen`/`primes` = the observable definitions (defined var ∈
`P.obs`); `below P _ z` = the nodes whose defined variable is an operand of `z` (its data-dependency set).
Surface `PrimeAdd.gsl`; `_sub` in `PrimeAddDefsSub`.
-/
namespace BaseLanguage.Analyses.PrimeAdd
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis

-- `allDefs` (universe) comes from `Tac.Locals` via `include Tac.Locals`.
/-- The ungated pump (gen): the observable definitions — tracked unconditionally so the gate can arm. -/
def obsGen (P : Program) (_n : Node) : Defs := Tac.Locals.obsDefs P
/-- The gate trigger set (`primes meets g`): the observable definitions (same set as `obsGen`). -/
def primes (P : Program) (_n : Node) : Defs := Tac.Locals.obsDefs P
/-- The gather per-element precondition (`below(z) ⊆ g`): `z`'s data-dependency set — the nodes whose
    defined variable is an operand of the computation at `z`. -/
def below (P : Program) (_n : Node) (z : Node) : Defs := Tac.Locals.dataDeps P z

-- The `PrimeAdd` clause predicate (the spelled-out `evs(gT)`, `var ∪ obsGen ∪ (gather ∩ gate)`) is
-- **emitted** by GenGeneral (`emitClauses`/`printEvs`), not hand-transcribed here.

end BaseLanguage.Analyses.PrimeAdd
