-- Copyright (c) 2026 Martin Rinard
import Generated.Seam.reachable.ValidExtremal
import BaseLanguage.Pass.UCE
/-!
# `generated/reachable/Adapter.lean` — instantiate the abstract UCE `ReachSpec`.

The generator already emits the **clean clause predicate** `Reachable` (set-ops over `Step`, no
`MTC.evs`) together with its validity `reachSol_valid : Reachable (reachSol)` and extremality
`reach_least` (in `generated/reachable/ValidExtremal.lean`, via the generated `reach_iff_flow` bridge —
the same machinery `pdce`/`lcm` use). So this adapter does **no** solver-calculus unfolding.

`reachSpecOf` turns *any* valid+extremal solution of the `.gsl` reachability clauses — i.e. any `sol` with
`Reachable P sol` and its leastness — into a `Pass.UCE.ReachSpec`. The only work is the leaf
specialisation `genNode = {n}` / `transp = ⊤` that puts the generic reaching update into the shape UCE
consumes; that is genuine per-analysis leaf reasoning (the analogue of an authored `_sub` fact), not solver
internals. `reachSol`/`reach_correct` is just the concrete instance.
-/
namespace BaseLanguage.Analyses.Reachable
open BaseLanguage Tac Tac.Locals Semantics Pass Std

variable {P : Program}

/-- **The reachability `ReachSpec` the compiler consumes: a plain `succList` graph BFS**
    (`Pass.UCE.bfsReachSpec`), not the ancestor-set dataflow solve — reachability is a traversal, so it is
    computed as one, isolated behind this seam. The generated `reachSol`/`Reachable` (`ValidExtremal`)
    remain a stand-alone demonstration of the ghost-spec framework; UCE no longer consumes them. -/
def reachSpec (P : Program) (wf : WellFormed P) : Pass.UCE.ReachSpec P := Pass.UCE.bfsReachSpec P wf

/-! ## The concrete UCE pass (specialised to the generated solution) + its verification. -/

/-- **Unreachable-code elimination**, on the generated reachability solution. -/
def uce (P : Program) (wf : WellFormed P) : Program := Pass.UCE.run P (reachSpec P wf)

theorem uce_wellFormed (wf : WellFormed P) : WellFormed (uce P wf) :=
  Pass.UCE.wellFormed (reachSpec P wf) wf

theorem uce_allReachable (wf : WellFormed P) : AllReachable (uce P wf) :=
  Pass.UCE.allReachable (reachSpec P wf) wf

theorem uce_preserves_halt (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (uce P wf) ⟨(uce P wf).entry, σ⟩ df ∧ Final (uce P wf) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v :=
  Pass.UCE.preserves_halt (reachSpec P wf) wf hrun hfin

theorem uce_preserves_faults (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (uce P wf) ⟨(uce P wf).entry, σ⟩ df ∧ Faulting (uce P wf) df :=
  Pass.UCE.preserves_faults (reachSpec P wf) wf hrun hfault

theorem uce_preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (uce P wf) ⟨(uce P wf).entry, σ⟩ :=
  Pass.UCE.preserves_diverges (reachSpec P wf) wf hdiv

end BaseLanguage.Analyses.Reachable
