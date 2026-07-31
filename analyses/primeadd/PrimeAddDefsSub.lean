-- Copyright (c) 2026 Martin Rinard
import analyses.primeadd.PrimeAddDefs
import BaseLanguage.IR.LocalsSub
/-!
# `Analyses.PrimeAdd.PrimeAddDefsSub` — the `_sub` (⊆ universe) domain lemmas.

The compound term `var ∪ obsGen ∪ (gather allDefs below ∩ gate primes allDefs)` needs: `obsGen_sub` (the
ungated gen), `primes_sub` (the gate trigger), `allNums_sub` (the gate result is the whole universe ⇒
identity). The empty `∅` seed needs no authored `_sub` (discharged inline by the emitter). `obsGen`/`primes` are filters of the universe (`mem_filter'`). The
`gather`'s universe `Wf` is `mem_toList` (U = universe), so `below` needs no `_sub`. Axiom-clean.
-/
namespace BaseLanguage.Analyses.PrimeAdd
open Tac Tac.Locals Semantics Std BaseLanguage.Analysis
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

theorem obsGen_sub (P : Program) (n : Node) : (obsGen P n).Subset (allDefs P) :=
  Tac.Locals.obsDefs_sub P

theorem primes_sub (P : Program) (n : Node) : (primes P n).Subset (allDefs P) :=
  Tac.Locals.obsDefs_sub P

-- the gate result is the whole universe ⇒ the generator needs the universe's (trivial) self-sub.
theorem allDefs_sub (P : Program) : (allDefs P).Subset (allDefs P) := fun x hx => hx

end BaseLanguage.Analyses.PrimeAdd
