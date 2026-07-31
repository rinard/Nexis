-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Correctness.AstToTacCorrect
import BaseLanguage.Normalize.Sim
import BaseLanguage.Normalize.FromLower
import BaseLanguage.LCM.Transform
import BaseLanguage.LCM.Correctness
import BaseLanguage.LCM.Layout
import BaseLanguage.PDCE.Transform
import BaseLanguage.PDCE.Correctness
import BaseLanguage.PDCE.Layout
import BaseLanguage.Pass.CleanupCorrect
import BaseLanguage.Pass.Optimize
import BaseLanguage.Peephole.Pass

namespace BaseLanguage

/-!
# `PipelineToAsm` — end-to-end correctness for the *full* compiler pipeline

`ast_to_asm` (in `AstToTacCorrect`) covers `codegen ∘ lower`. This module threads the middle stages —
`normalize`, the const-prop round, and the LCM (PRE / lazy code motion) and PDCE (partial-dead sinking)
optimizers — to give the full pipeline of `prophecyc`:

```
lower → peephole → normalize → iterateOpt → normalize → LCM → PDCE → cleanup → codegen
```

**Const-prop runs before LCM/PDCE**, so the expensive structural passes see the simplified program: UCE
has already deleted unreachable blocks, branch-folding has removed join points (turning *partial*
redundancies into *full* ones), and const-folding has shrunk `listExpr P` — the bitvector width of every
LCM ghost. The second `normalize` rebuilds every `WellNormalized` field by construction, which is exactly
LCM's hypothesis; it costs one extra entry `noop`, which `cleanup` then eliminates.

The composition chains the forward-simulation results:
* `AstToTac.lower_correct`         (frontend)         — `evalS … = .ok σ'` ⟹ `lower s` halts ≈ `σ'` on origs
* `Normalize.normalize_preserves_halt`                 — normal-form pre-passes preserve the halting run
* `Pass.iterateOpt_preserves_halt`                     — the const-prop round preserves it
* `Analyses.LCM.transform_preserves_halt`                    — PRE preserves it (extremal bundle)
* `Analyses.PDCE.transform_preserves_halt`                   — PDCE preserves it (any valid bundle)
* `TacToAsm.codegen_simulates`     (backend)           — IR halt ⟹ ARM64 halt with the matching frame

The agreement is on the program's **observables** `(lower s).obs` (the source variables that occur in
`s`) — the optimizers only preserve observables, by design. It is stated for an *extremal* LCM bundle
`Slcm` (LCM correctness needs down-safety) and an *arbitrary valid* PDCE bundle `Spdce`, so it does **not**
depend on the (still-stubbed) dataflow `solve`.
-/

namespace AstToTac

open Tac Ast Semantics Normalize

/-- **`normalize ∘ peephole ∘ lower` is `WellNormalized` — unconditionally.** `lower`'s structural
    guarantees discharge both preconditions, and `peephole` keeps reachability (it rewrites only
    assignment RHSs, leaving the CFG identical). This is the const-prop round's input. -/
theorem wn_preOpt (s : Stmt) : WellNormalized (normalize (Peephole.peephole (lower s))) :=
  normalize_wellNormalized (Peephole.peephole (lower s))
    (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s))
    (Peephole.peephole_allReachable (lower s) (lower_allReachable s))

/-- **Full-pipeline forward simulation.** If the reference interpreter runs `s` to `σ'`, then the ARM64
    program produced by the whole pipeline
    `codegen ∘ cleanup ∘ PDCE ∘ LCM ∘ normalize ∘ iterateOpt ∘ normalize ∘ peephole ∘ lower` runs from
    its initial state to a `halted` machine state whose frame holds `σ'`'s value (under `encode`) for
    every observable source variable. Holds for any valid PDCE bundle and any **extremal** LCM bundle —
    LCM placement correctness (isolation / no-reinsertion) is proved from the ghosts being the extremal
    KRS solution, so `Extremal Slcm` is required here, whereas PDCE sinking is correct for any valid
    bundle.

    `wfPre` is a parameter only so the statement can *name* the witness `iterateOpt` consumes; it is
    derivable (`(wn_preOpt s).wf`), and `WellFormed` is a `Prop`, so any two choices agree. -/
theorem pipeline_to_asm (s : Stmt) (fuel : Nat) (σ' : Store)
    (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ')
    (prov : Pass.Provider) (N : Nat)
    (wfPre : WellFormed (normalize (Peephole.peephole (lower s))))
    (Slcm : Analyses.LCM.LcmSpec
      (normalize (Pass.iterateOpt prov N (normalize (Peephole.peephole (lower s))) wfPre)))
    (hLcm : Analyses.LCM.Extremal Slcm)
    (Spdce : Analyses.PDCE.PdceSpec (Analyses.LCM.transform
      (normalize (Pass.iterateOpt prov N (normalize (Peephole.peephole (lower s))) wfPre)) Slcm)) :
    let Pn := normalize (Peephole.peephole (lower s))
    let Pi := Pass.iterateOpt prov N Pn wfPre
    let P₀ := normalize Pi
    let P₁ := Analyses.LCM.transform P₀ Slcm
    let Pf := Analyses.PDCE.transform P₁ Spdce
    let Pc := Pass.Cleanup.cleanup Pf
    ∃ f sf, Asm.run (TacToAsm.codegen Pc) f (TacToAsm.initState Pc Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars Pc) v) = TacToAsm.encode (σ' v) := by
  intro Pn Pi P₀ P₁ Pf Pc
  -- observables of `lower s` are all source (`.orig`) variables
  have hobs0 : ∀ v ∈ (lower s).obs, varIsOrig v = true := by
    intro v hv; obtain ⟨n, rfl⟩ := lower_obs_orig s v hv; rfl
  -- the const-prop output: well-formed, and `AllReachable` because every round ends in UCE
  have hwfPi : WellFormed Pi := Pass.iterateOpt_wf prov N Pn wfPre
  have harPi : AllReachable Pi :=
    Pass.iterateOpt_allReachable prov N Pn wfPre (wn_preOpt s).allReach
  -- re-normalizing rebuilds *all* of `WellNormalized` by construction — exactly LCM's hypothesis
  have hwn : WellNormalized P₀ := normalize_wellNormalized Pi hwfPi harPi
  -- `iterateOpt` preserves `obs`, so the const-prop output's observables are still source vars
  have hobsPi : ∀ v ∈ Pi.obs, varIsOrig v = true := by
    intro v hv; rw [Pass.iterateOpt_obs] at hv; exact hobs0 v hv
  -- ① frontend
  obtain ⟨cf0, hsteps0, _hfin0, hframe0⟩ := lower_correct s fuel σ' hnt h
  -- ①.5 peephole (the first pass)
  obtain ⟨cfpe, hstepspe, hfinpe, hope⟩ := Peephole.peephole_preserves_halt hsteps0 _hfin0
  -- ② normalize
  obtain ⟨cf1, hsteps1, hfin1, ho1⟩ :=
    normalize_preserves_halt (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s))
      hobs0 hstepspe hfinpe
  -- ③ const-propagation iterated `N` rounds (constFold ∘ branchFold ∘ UCE, re-analyzed each round)
  obtain ⟨cfOpt, hstepsOpt, hfinOpt, hoOpt⟩ :=
    Pass.iterateOpt_preserves_halt prov N Pn wfPre hsteps1 hfin1
  -- ④ re-normalize (a second entry `noop`; `cleanup` removes it)
  obtain ⟨cf2, hsteps2, hfin2, ho2⟩ := normalize_preserves_halt hwfPi hobsPi hstepsOpt hfinOpt
  -- ⑤ LCM (PRE)
  obtain ⟨ne, hen⟩ := normalize_entry_noop Pi
  obtain ⟨cf3, hsteps3, hfin3, ho3⟩ :=
    Analyses.LCM.transform_preserves_halt Slcm hLcm hwn hen hobsPi hsteps2 hfin2
  rw [← Analyses.LCM.transform_entry Slcm] at hsteps3
  -- ⑥ PDCE
  obtain ⟨cf4, hsteps4, hfin4, ho4⟩ :=
    Analyses.PDCE.transform_preserves_halt Spdce (Analyses.LCM.transform_wellFormed Slcm hwn.wf) hsteps3 hfin3
  -- ⑦ cleanup (noop-elimination + index compaction)
  obtain ⟨cf5, hsteps5, hfin5, ho5⟩ :=
    Pass.Cleanup.cleanup_preserves_halt
      (Analyses.PDCE.transform_wellFormed Spdce (Analyses.LCM.transform_wellFormed Slcm hwn.wf)) hsteps4 hfin4
  -- ⑧ backend
  obtain ⟨f, sf, hrun, hmem⟩ := TacToAsm.codegen_simulates hsteps5 hfin5
  refine ⟨f, sf, hrun, ?_⟩
  intro v hv
  -- chase the observable frame back to σ'; everything from ④ on is stated over `Pi.obs`
  have hvPi : v ∈ Pi.obs := by rw [Pass.iterateOpt_obs]; exact hv
  rw [hmem v, ho5 v hvPi, ho4 v hvPi, ho3 v hvPi, ho2 v hvPi, hoOpt v hv, ho1 v hv,
    hope v hv, hframe0 v (lower_obs_orig s v hv)]

end AstToTac

end BaseLanguage
