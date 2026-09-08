-- Copyright (c) 2026 Martin Rinard
import analyses.pdce.PdceAdapter
import Generated.Seam.pdcefault.ValidExtremal
import BaseLanguage.Meta.AxiomCheck

/-!
# The fault-preserving PDCE bundle

Assembles the `PDCEFault` solver (`Pdce.gsl` with its liveness floor widened from `condVars` to
`condVars ∪ faultingRhsVars`) into the *same* `PdceSpec` structure the verified transform consumes, with
the sinking filter aimed at `Expr.faultFree`.

Two things make this work without a second transform or a second correctness development:

* the strengthened `Live` **implies** the classical one — its floor is a superset, every other clause is
  character-for-character identical — so the bundle is a perfectly ordinary valid `PdceSpec`; and
* the widened floor is exactly the bundle's `keepLive` obligation: for a node whose assignment can fault,
  `faultingRhsVars = rhsVars`, so the floor says precisely "the operands of a computation this mode
  refuses to sink are live".

What is *not* inherited is extremality of `π`: the fault-preserving `π` is the least solution of a
**stronger** system, so it is extremal for that system, not for the classical one. That is the honest cost
— fewer computations are eliminated — and it is why `PDCE.Optimality`'s comparisons are stated against
competitors carrying the same filter.
-/

namespace BaseLanguage.Analyses.PDCE
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std

/-- The strengthened liveness satisfies every classical `Live` clause: only the floor differs, and it
    grew (`condVars ⊆ liveFloorF`). -/
theorem live_of_faultLive {P : Program} {π : Node → Variables}
    (h : PDCEFault.Live P π) : Live P π where
  predict := h.predict
  check   := fun n x hx => h.check n x (Variables.mem_union.mpr (Or.inl hx))
  gate    := h.gate
  seed    := h.seed
  within  := h.within

/-- …and the classical `Sink` is literally the same clause set. -/
theorem sink_of_faultSink {P : Program} {η : Node → Assignments}
    (h : PDCEFault.Sink P η) : Sink P η where
  update := h.update
  seed   := h.seed
  within := h.within

/-- **The widened floor discharges `keepLive`.** At a node whose assignment can fault,
    `faultingRhsVars = rhsVars`, so the floor puts the operands in `π`. -/
theorem keepLive_of_faultLive {P : Program} {π : Node → Variables}
    (h : PDCEFault.Live P π) :
    ∀ n a, a ∈ born P n → (fun b : Asgn => b.rhs.faultFree) a = false →
      (rhsVars P n).Subset (π n) := by
  intro n a ha hff x hx
  refine h.check n x (Variables.mem_union.mpr (Or.inr ?_))
  -- `born n` is the singleton at an `assign` node, so `a.rhs` is that node's right-hand side
  unfold born at ha
  cases hf : P.fetch n with
  | none => rw [hf] at ha; exact absurd ha Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign y e nx =>
          rw [hf] at ha
          have haeq : a = (⟨y, e⟩ : Asgn) := Analysis.SetOps.mem_singleton.mp ha
          subst haeq
          simp only at hff
          unfold faultingRhsVars
          rw [hf]; simp only
          rw [if_neg (by simpa using hff)]
          unfold rhsVars at hx; rw [hf] at hx; exact hx
      | _ => rw [hf] at ha; exact absurd ha Std.HashSet.not_mem_empty

/-- **The fault-preserving PDCE bundle.** Same structure the classical transform consumes; the sinking
    filter admits only `faultFree` right-hand sides, and its liveness obligation is discharged by the
    analysis's widened floor. -/
def pdceFaultSolved (P : Program) (wf : WellFormed P) : PdceSpec P :=
  { π   := PDCEFault.πSol P
    η   := PDCEFault.ηSol P
    keep := fun a => a.rhs.faultFree
    isLive := live_of_faultLive (PDCEFault.πSol_valid P wf)
    isSink := sink_of_faultSink (PDCEFault.ηSol_valid P wf)
    keepLive := keepLive_of_faultLive (PDCEFault.πSol_valid P wf) }

@[simp] theorem pdceFaultSolved_keep (P : Program) (wf : WellFormed P) :
    (pdceFaultSolved P wf).keep = fun a => a.rhs.faultFree := rfl

/-- The bundle only ever sinks assignments that cannot fault — the hypothesis
    `transform_preserves_faulting` needs. -/
theorem pdceFaultSolved_keep_faultFree (P : Program) (wf : WellFormed P) :
    ∀ a : Asgn, (pdceFaultSolved P wf).keep a = true → a.rhs.faultFree = true := fun _ h => h

#assert_clean_axioms pdceFaultSolved
end BaseLanguage.Analyses.PDCE
