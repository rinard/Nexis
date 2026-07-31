-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Correctness.PipelineToAsm
import BaseLanguage.Behavior.PipelineBehavior

namespace BaseLanguage

/-!
# `OptPipeline` — full **trichotomy** for the LCM/PDCE-free optimizing pipeline

`pipeline_to_asm` gives the whole compiler, but only for **halting** runs: the two heavy optimizers each
break one non-halting outcome, and by design —

* **LCM** (PRE / lazy code motion) does not preserve **divergence**: it may hoist a faulting computation in
  front of an infinite loop, turning a divergent run into a fault (`⊥ ⇝ fault`).
* **PDCE** (partial-dead sinking) does not preserve **faults**: it may delete a dead `x := y/0` (or sink one
  off the path that doesn't need it), turning a faulting run into a halt or divergence (a *refinement*;
  `PDCE.md` §4.5).

So neither fault nor divergence survives the full pipeline. They *do* survive the pipeline with **LCM and
PDCE removed**, because every remaining pass is a behaviour-exact bisimulation (no code motion, no
dead-code deletion): `lower → peephole → normalize → constFold∘branchFold∘UCE → cleanup → codegen`. This
module states all three outcomes for that pipeline:

* `optpipe_preserves_halt`    — `evalS … = .ok σ'` ⟹ machine halts, frame holds `σ'` on observables;
* `optpipe_preserves_fault`   — `evalS … = .fault` ⟹ `Asm.Faults`;
* `optpipe_preserves_diverge` — `∀ fuel, evalS … = .timeout` ⟹ `Asm.Diverges`.

Each is `skeleton_preserves_*` (`Behavior/PipelineBehavior.lean`) extended through the const-propagation
round (`Pass.iterateOpt`, any `Provider`/count) and the verified `cleanup`. The const-prop passes are
abstract over their specs, so — like `pipeline_to_asm` — these reference no solver.
-/

namespace AstToTac

open Tac Ast Semantics Normalize

/-- **Trichotomy ①/③ — halting.** `evalS s = .ok σ'` ⟹ the LCM/PDCE-free pipeline
    `codegen ∘ cleanup ∘ iterateOpt ∘ normalize ∘ peephole ∘ lower` halts, its frame holding `σ'` for
    every observable source variable. (`pipeline_to_asm` with the two optimizer stages dropped.) -/
theorem optpipe_preserves_halt (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ')
    (wf₀ : WellFormed (normalize (Peephole.peephole (lower s))))
    (prov : Pass.Provider) (N : Nat) :
    let P₀ := normalize (Peephole.peephole (lower s))
    let Pc := Pass.Cleanup.cleanup (Pass.iterateOpt prov N P₀ wf₀)
    ∃ f sf, Asm.run (TacToAsm.codegen Pc) f (TacToAsm.initState Pc Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars Pc) v) = TacToAsm.encode (σ' v) := by
  intro P₀ Pc
  have hobs0 : ∀ v ∈ (lower s).obs, varIsOrig v = true := by
    intro v hv; obtain ⟨n, rfl⟩ := lower_obs_orig s v hv; rfl
  obtain ⟨cf0, hs0, hfin0, hframe0⟩ := lower_correct s fuel σ' hnt h
  obtain ⟨cfpe, hspe, hfinpe, hope⟩ := Peephole.peephole_preserves_halt hs0 hfin0
  obtain ⟨cf1, hs1, hfin1, ho1⟩ :=
    normalize_preserves_halt (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hobs0 hspe hfinpe
  obtain ⟨cfOpt, hsOpt, hfinOpt, hoOpt⟩ :=
    Pass.iterateOpt_preserves_halt prov N P₀ wf₀ hs1 hfin1
  obtain ⟨cf4, hs4, hfin4, ho4⟩ :=
    Pass.Cleanup.cleanup_preserves_halt (Pass.iterateOpt_wf prov N P₀ wf₀) hsOpt hfinOpt
  obtain ⟨f, sf, hrun, hmem⟩ := TacToAsm.codegen_simulates hs4 hfin4
  refine ⟨f, sf, hrun, fun v hv => ?_⟩
  rw [hmem v, ho4 v (by rw [Pass.iterateOpt_obs]; exact hv), hoOpt v hv, ho1 v hv, hope v hv,
    hframe0 v (lower_obs_orig s v hv)]

/-- **Trichotomy ②/③ — faulting.** `evalS s = .fault` ⟹ the LCM/PDCE-free pipeline faults. -/
theorem optpipe_preserves_fault (s : Stmt) (fuel : Nat) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .fault)
    (wf₀ : WellFormed (normalize (Peephole.peephole (lower s))))
    (prov : Pass.Provider) (N : Nat) :
    let P₀ := normalize (Peephole.peephole (lower s))
    let Pc := Pass.Cleanup.cleanup (Pass.iterateOpt prov N P₀ wf₀)
    Asm.Faults (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init) := by
  intro P₀ Pc
  obtain ⟨cf0, hs0, hflt0⟩ := lower_faultSteps s fuel hnt h
  obtain ⟨cfpe, hspe, hfltpe⟩ :=
    Peephole.peephole_preserves_faultSteps (lower_wellFormed s) hs0 hflt0
  obtain ⟨cf1, hs1, hflt1⟩ :=
    normalize_preserves_faultSteps (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hspe hfltpe
  obtain ⟨cfOpt, hsOpt, hfltOpt⟩ := Pass.iterateOpt_preserves_faults prov N P₀ wf₀ hs1 hflt1
  obtain ⟨cf4, hs4, hflt4⟩ :=
    Pass.Cleanup.cleanup_preserves_faults (Pass.iterateOpt_wf prov N P₀ wf₀) hsOpt hfltOpt
  exact TacToAsm.codegen_faults hs4 hflt4

/-- **Trichotomy ③/③ — divergence.** `∀ fuel, evalS s = .timeout` ⟹ the LCM/PDCE-free pipeline runs
    forever. -/
theorem optpipe_preserves_diverge (s : Stmt) (hnt : Stmt.noTmp s)
    (h : ∀ fuel, Ast.evalS fuel s Store.init = .timeout)
    (wf₀ : WellFormed (normalize (Peephole.peephole (lower s))))
    (prov : Pass.Provider) (N : Nat) :
    let P₀ := normalize (Peephole.peephole (lower s))
    let Pc := Pass.Cleanup.cleanup (Pass.iterateOpt prov N P₀ wf₀)
    Asm.Diverges (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init) := by
  intro P₀ Pc
  have hd0 := lower_diverges s hnt h
  have hdpe := Peephole.peephole_preserves_diverge (lower_wellFormed s) hd0
  have hd1 := normalize_preserves_diverge (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hdpe
  have hdOpt := Pass.iterateOpt_preserves_diverges prov N P₀ wf₀ hd1
  have hd4 := Pass.Cleanup.cleanup_preserves_diverges (Pass.iterateOpt_wf prov N P₀ wf₀) hdOpt
  exact TacToAsm.codegen_diverges hd4

end AstToTac

end BaseLanguage
