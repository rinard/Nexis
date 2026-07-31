-- Copyright (c) 2026 Martin Rinard
import Lean

/-!
# `Meta.AxiomCheck` — a build-failing axiom-cleanliness gate.

`#assert_clean_axioms foo` fails elaboration (hence `lake build`) unless `foo` depends **only** on the
permitted axioms `{propext, Classical.choice, Quot.sound}` — in particular it rejects any `sorryAx`. Unlike
`#print axioms` (which only *prints* the axiom set, so a regression that dirties it slips through silently),
this is a real gate: the generated `ValidExtremal` files assert it on every emitted `_valid`/extremal
theorem, so the project-wide axiom-cleanliness claim is mechanically enforced, not eyeballed.

Subsets of the permitted set pass (a cleaner theorem is still clean); only a *disallowed* axiom fails.
-/

open Lean Elab Command in
/-- Fail the build unless the named constant depends only on `propext`, `Classical.choice`, `Quot.sound`. -/
elab "#assert_clean_axioms " id:ident : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let axs ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError m!"AXIOM CHECK FAILED: '{name}' depends on disallowed axiom(s) {bad.toList} \
      (permitted: propext, Classical.choice, Quot.sound)"
