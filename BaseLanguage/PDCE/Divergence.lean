-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Correctness
import BaseLanguage.Behavior.Outcomes

/-!
# `PDCE.Divergence` — PDCE preserves divergence

`Correctness.lean` proves observable preservation on **halting** runs; faults/divergence were left
don't-care (PDCE.md §4.5 table). This file discharges the `Diverge → Diverge` cell: if `P` from its
entry runs forever, so does `transform P S`.

The whole content is that PDCE's forward simulation is **non-stuttering**: every source node maps to a
block of length `blockLen = |matNode| + 1 + edges ≥ 1`, so each source step is matched by **≥ 1** target
steps (the `+1` control instruction). `match_step` already produces exactly the leading-`Step`-then-
`Steps` shape the generic engine `Semantics.diverges_of_stepsimG` consumes, over the declarative `Match`
relation — no dataflow solver, no extremality (no `Extremal S`), any valid `S : PdceSpec P`. -/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-- **PDCE preserves divergence.** If `P` started at its entry on store `σ` runs forever, then
    `transform P S` started at *its* entry on the same `σ` also runs forever. Fills the last cell of the
    §4.5 outcome table left open by `transform_preserves_halt`; holds for any valid bundle `S`. -/
theorem transform_preserves_diverges {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (transform P S) ⟨(transform P S).entry, σ⟩ := by
  rw [transform_entry]
  exact diverges_of_stepsimG (Rel := Match P S)
    (fun _ hm hstep => match_step S wf hm hstep) wf wf.entry_lt (match_init S σ) hdiv

end BaseLanguage.Analyses.PDCE
