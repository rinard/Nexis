-- Copyright (c) 2026 Martin Rinard
import Seam.compile.CompileCorrect
import Seam.pdce.Mode
import BaseLanguage.LCM.Mode
import BaseLanguage.Pass.Correctness.OptPipeline
/-!
# `compile.SafeOutcomes` — the full **trichotomy** for the *optimizing* compiler

`Compile.main_compile_correct` covers the whole pipeline, LCM and PDCE included, but only for **halting**
source runs. That is forced in the default modes, and `Pass/Correctness/OptPipeline.lean` says why: each
heavy optimizer breaks one non-halting outcome by design.

* **LCM** (classical) does not preserve **divergence** — it may hoist a faulting computation in front of an
  infinite loop, turning `⊥` into a fault.
* **PDCE** (classical) does not preserve **faults** — it may sink or delete a dead `x := y/0`.

`OptPipeline` therefore states all three outcomes only for the pipeline with **LCM and PDCE removed**.

But each optimizer has a *behaviour-preserving mode* that does keep its missing outcome
(`LCM.runLcm_safe_preserves_all`, `PDCE.runPdce_safe_preserves_all`), and the CLI can run both at once
(`--lcm=safe --pdce=safe`). This module is what those two per-pass results were missing: it composes them
through `cleanup` and `codegen`, so the *optimizing* compiler gets a trichotomy too.

```
lower → peephole → normalize → iterateOpt → normalize → LCM(safe) → PDCE(safe) → cleanup → codegen
```

* `safepipe_preserves_halt`    — `evalS … = .ok σ'` ⟹ the machine halts, frame holding `σ'` on observables;
* `safepipe_preserves_fault`   — `evalS … = .fault` ⟹ `Asm.Faults`;
* `safepipe_preserves_diverge` — `∀ fuel, evalS … = .timeout` ⟹ `Asm.Diverges`.

All three are stated over `LCM.GateSound`, the single obligation LCM's replace gate owes the simulation, so
each comes in the two flavours the two `GateMode`s buy:

* `safe_compile_preserves_all` — the seven-ghost analysis with the materialization gate. **No
  extremality**: `gateSound_materialized` discharges the obligation from the bundle's validity.
* `safe_compile_preserves_all_demand` — the six-ghost analysis with the classical demand gate, where the
  obligation costs `Extremal S` and the `prependEntry` `noop` entry.

Both are closed theorems about the program `Main` emits under `--lcm=safe --pdce=safe`, so — like
`main_compile_correct` — they are statements about the compiler actually shipped, not an abstract family.
-/
namespace BaseLanguage.Compile
open BaseLanguage Tac Ast Semantics Normalize AstToTac

/-! ## The stages, named

`mainOptWith` inlines these as `let`s. The safe pipeline needs to *talk* about the intermediate program
`P₀` (the LCM bundle, and hence the `GateSound` obligation, is indexed by it), so they are named here.
Definitionally identical to the corresponding `let`s in `Main.optStages`. -/

/-- `normalize ∘ peephole ∘ lower` — the const-prop round's input. -/
noncomputable def safePn (s : Stmt) : Program := normalize (Peephole.peephole (lower s))

/-- …after the const-propagation round. -/
noncomputable def safePi (s : Stmt) : Program :=
  Pass.iterateOpt optProvider (safePn s).size (safePn s) (wn_preOpt s).wf

/-- …re-normalized: the program LCM sees. -/
noncomputable def safeP₀ (s : Stmt) : Program := normalize (safePi s)

theorem safePi_wf (s : Stmt) : WellFormed (safePi s) :=
  Pass.iterateOpt_wf optProvider (safePn s).size (safePn s) (wn_preOpt s).wf

theorem safePi_allReachable (s : Stmt) : AllReachable (safePi s) :=
  Pass.iterateOpt_allReachable optProvider (safePn s).size (safePn s) (wn_preOpt s).wf
    (wn_preOpt s).allReach

/-- `normalize` rebuilds every `WellNormalized` field by construction — exactly LCM's hypothesis. -/
theorem safeP₀_wn (s : Stmt) : WellNormalized (safeP₀ s) :=
  normalize_wellNormalized (safePi s) (safePi_wf s) (safePi_allReachable s)

theorem safeP₀_wf (s : Stmt) : WellFormed (safeP₀ s) := (safeP₀_wn s).wf

/-- Every stage preserves the observable set, so `lower`'s observables are the ones LCM sees. -/
theorem safePi_obs (s : Stmt) : (safePi s).obs = (lower s).obs := by
  show (Pass.iterateOpt optProvider (safePn s).size (safePn s) (wn_preOpt s).wf).obs = _
  rw [Pass.iterateOpt_obs]
  rfl

theorem safePi_obsOrig (s : Stmt) : ∀ v ∈ (safePi s).obs, varIsOrig v = true := by
  intro v hv
  rw [safePi_obs] at hv
  obtain ⟨n, rfl⟩ := lower_obs_orig s v hv; rfl

/-- The LCM bundle the safe pipeline hands to the transform: the chosen analysis, the chosen replace
    gate, and the hoisting filter aimed at `Expr.faultFree` (which is what `--lcm=safe` *is*). -/
noncomputable def safeSlcm (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode) (s : Stmt) :
    Analyses.LCM.LcmSpec (safeP₀ s) :=
  ((a.bundle (safeP₀ s) (safeP₀_wf s)).withGate g).withKeep Expr.faultFree

/-- The LCM output: `runLcm .preserveDivergence` on the chosen bundle, i.e. the hoist that moves only
    fault-free expressions. -/
noncomputable def safeLcmOut (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) : Program := Analyses.LCM.transform (safeP₀ s) (safeSlcm a g s)

theorem safeLcmOut_wf (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode) (s : Stmt) :
    WellFormed (safeLcmOut a g s) :=
  Analyses.LCM.transform_wellFormed (safeSlcm a g s) (safeP₀_wf s)

theorem safeLcmOut_entry (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode) (s : Stmt) :
    (safeLcmOut a g s).entry
      = Analyses.LCM.blockOff (safeP₀ s) (safeSlcm a g s) (safeP₀ s).entry := rfl

theorem safeLcmOut_obs (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode) (s : Stmt) :
    (safeLcmOut a g s).obs = (safePi s).obs := rfl

/-- The IR the compiler emits under `--lcm=safe --pdce=safe`.

    `Main.optStages` builds exactly this at `mode := .preserveDivergence`, `pmode := .preserveFaults`:
    `runLcm .preserveDivergence P₀ bL` unfolds to `transform P₀ (bL.withKeep Expr.faultFree)`, which is
    `safeLcmOut`. **Must keep mirroring `Main.optStages`**, or the theorems below stop being statements
    about the compiler we actually ship. -/
noncomputable def mainOptSafe (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) : Program :=
  Analyses.PDCE.runPdce .preserveFaults (safeLcmOut a g s) (safeLcmOut_wf a g s)

theorem mainOptSafe_wf (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode) (s : Stmt) :
    WellFormed (mainOptSafe a g s) :=
  Analyses.PDCE.runPdce_wellFormed .preserveFaults _ (safeLcmOut_wf a g s)

/-! ## The three outcomes

Each is the corresponding chain of behaviour lemmas, one per pass. The LCM link is the only one that
takes a hypothesis beyond well-formedness, and `hg` is it. -/

set_option maxHeartbeats 800000 in
/-- **Trichotomy ①/③ — halting.** With the observable store, as `main_compile_correct` gives.

    (The observable-agreement chain threads eight stages, each phrased over its own program's `obs`;
    the defeq between them is cheap individually but adds up, hence the raised budget.) -/
theorem safepipe_preserves_halt (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ')
    (hg : Analyses.LCM.GateSound (safeP₀ s) (safeSlcm a g s)) :
    let Pc := Pass.Cleanup.cleanup (mainOptSafe a g s)
    ∃ f sf, Asm.run (TacToAsm.codegen Pc) f (TacToAsm.initState Pc Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars Pc) v) = TacToAsm.encode (σ' v) := by
  intro Pc
  have hobs0 : ∀ v ∈ (lower s).obs, varIsOrig v = true := by
    intro v hv; obtain ⟨n, rfl⟩ := lower_obs_orig s v hv; rfl
  have hobsPi := safePi_obsOrig s
  obtain ⟨cf0, hs0, hfin0, hframe0⟩ := lower_correct s fuel σ' hnt h
  obtain ⟨cfpe, hspe, hfinpe, hope⟩ := Peephole.peephole_preserves_halt hs0 hfin0
  obtain ⟨cf1, hs1, hfin1, ho1⟩ :=
    normalize_preserves_halt (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s))
      hobs0 hspe hfinpe
  obtain ⟨cfOpt, hsOpt, hfinOpt, hoOpt⟩ :=
    Pass.iterateOpt_preserves_halt optProvider (safePn s).size (safePn s) (wn_preOpt s).wf hs1 hfin1
  obtain ⟨cf2, hs2, hfin2, ho2⟩ :=
    normalize_preserves_halt (safePi_wf s) hobsPi hsOpt hfinOpt
  -- ⑤ LCM, hoisting only fault-free expressions
  obtain ⟨cf3, hs3, hfin3, ho3⟩ :=
    Analyses.LCM.transform_preserves_halt (safeSlcm a g s) hg (safeP₀_wn s) hobsPi hs2 hfin2
  have hs3' : Steps (safeLcmOut a g s) ⟨(safeLcmOut a g s).entry, Store.init⟩ cf3 := by
    rw [safeLcmOut_entry]; exact hs3
  have hfin3' : Final (safeLcmOut a g s) cf3 := hfin3
  -- ⑥ PDCE, declining to sink or delete a possibly-faulting assignment
  obtain ⟨cf4, hs4, hfin4, ho4⟩ :=
    Analyses.PDCE.runPdce_preserves_halt .preserveFaults (safeLcmOut_wf a g s) hs3' hfin3'
  have hs4' : Steps (mainOptSafe a g s) ⟨(mainOptSafe a g s).entry, Store.init⟩ cf4 := hs4
  have hfin4' : Final (mainOptSafe a g s) cf4 := hfin4
  obtain ⟨cf5, hs5, hfin5, ho5⟩ :=
    Pass.Cleanup.cleanup_preserves_halt (mainOptSafe_wf a g s) hs4' hfin4'
  obtain ⟨f, sf, hrun, hmem⟩ := TacToAsm.codegen_simulates hs5 hfin5
  refine ⟨f, sf, hrun, fun v hv => ?_⟩
  -- the observable set is the same at every stage; name the membership at each stage's type so the
  -- defeq is checked once, in a small context
  have hvPi : v ∈ (safePi s).obs := by rw [safePi_obs]; exact hv
  have hvP₀ : v ∈ (safeP₀ s).obs := hvPi
  have hvL : v ∈ (safeLcmOut a g s).obs := hvPi
  have hvM : v ∈ (mainOptSafe a g s).obs := hvPi
  have hchain : cf5.store v = σ' v := by
    rw [ho5 v hvM, ho4 v hvL, ho3 v hvP₀, ho2 v hvPi, hoOpt v hv, ho1 v hv, hope v hv,
      hframe0 v (lower_obs_orig s v hv)]
  exact (hmem v).trans (congrArg TacToAsm.encode hchain)

/-- **Trichotomy ②/③ — faulting.** The cell classical PDCE gives up; `--pdce=safe` keeps it, and LCM
    preserves faults in either mode. -/
theorem safepipe_preserves_fault (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) (fuel : Nat) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .fault)
    (hg : Analyses.LCM.GateSound (safeP₀ s) (safeSlcm a g s)) :
    let Pc := Pass.Cleanup.cleanup (mainOptSafe a g s)
    Asm.Faults (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init) := by
  intro Pc
  obtain ⟨cf0, hs0, hflt0⟩ := lower_faultSteps s fuel hnt h
  obtain ⟨cfpe, hspe, hfltpe⟩ :=
    Peephole.peephole_preserves_faultSteps (lower_wellFormed s) hs0 hflt0
  obtain ⟨cf1, hs1, hflt1⟩ :=
    normalize_preserves_faultSteps
      (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hspe hfltpe
  obtain ⟨cfOpt, hsOpt, hfltOpt⟩ :=
    Pass.iterateOpt_preserves_faults optProvider (safePn s).size (safePn s) (wn_preOpt s).wf hs1 hflt1
  obtain ⟨cf2, hs2, hflt2⟩ := normalize_preserves_faultSteps (safePi_wf s) hsOpt hfltOpt
  obtain ⟨cf3, hs3, hflt3⟩ :=
    Analyses.LCM.transform_preserves_faulting (safeSlcm a g s) hg (safeP₀_wn s) hs2 hflt2
  have hs3' : Steps (safeLcmOut a g s) ⟨(safeLcmOut a g s).entry, Store.init⟩ cf3 := by
    rw [safeLcmOut_entry]; exact hs3
  have hflt3' : Faulting (safeLcmOut a g s) cf3 := hflt3
  obtain ⟨cf4, hs4, hflt4⟩ :=
    Analyses.PDCE.runPdce_preserves_faulting (safeLcmOut_wf a g s) hs3' hflt3'
  have hs4' : Steps (mainOptSafe a g s) ⟨(mainOptSafe a g s).entry, Store.init⟩ cf4 := hs4
  have hflt4' : Faulting (mainOptSafe a g s) cf4 := hflt4
  obtain ⟨cf5, hs5, hflt5⟩ :=
    Pass.Cleanup.cleanup_preserves_faults (mainOptSafe_wf a g s) hs4' hflt4'
  exact TacToAsm.codegen_faults hs5 hflt5

/-- **Trichotomy ③/③ — divergence.** The cell classical LCM gives up; `--lcm=safe` keeps it, and PDCE
    preserves divergence in either mode. -/
theorem safepipe_preserves_diverge (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) (hnt : Stmt.noTmp s)
    (h : ∀ fuel, Ast.evalS fuel s Store.init = .timeout)
    (hg : Analyses.LCM.GateSound (safeP₀ s) (safeSlcm a g s)) :
    let Pc := Pass.Cleanup.cleanup (mainOptSafe a g s)
    Asm.Diverges (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init) := by
  intro Pc
  have hd0 := lower_diverges s hnt h
  have hdpe := Peephole.peephole_preserves_diverge (lower_wellFormed s) hd0
  have hd1 :=
    normalize_preserves_diverge
      (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hdpe
  have hdOpt :=
    Pass.iterateOpt_preserves_diverges optProvider (safePn s).size (safePn s) (wn_preOpt s).wf hd1
  have hd2 := normalize_preserves_diverge (safePi_wf s) hdOpt
  -- the `keep = Expr.faultFree` filter discharges `SafeInserts` by construction
  have hd3 :=
    Analyses.LCM.transform_preserves_diverges (safeSlcm a g s) hg (safeP₀_wn s) (safeP₀_wf s)
      (Analyses.LCM.safeInserts_faultFree ((a.bundle (safeP₀ s) (safeP₀_wf s)).withGate g)) hd2
  have hd3' : Diverges (safeLcmOut a g s) ⟨(safeLcmOut a g s).entry, Store.init⟩ := by
    rw [safeLcmOut_entry]; exact hd3
  have hd4 :=
    Analyses.PDCE.runPdce_preserves_diverges .preserveFaults (safeLcmOut_wf a g s) hd3'
  have hd4' : Diverges (mainOptSafe a g s) ⟨(mainOptSafe a g s).entry, Store.init⟩ := hd4
  have hd5 := Pass.Cleanup.cleanup_preserves_diverges (mainOptSafe_wf a g s) hd4'
  exact TacToAsm.codegen_diverges hd5

/-! ## The shipped safe compiler, both gates

`Main` under `--lcm=safe --pdce=safe` emits `cleanup (mainOptSafe ana gate s)`. The two theorems below are
that program's complete behaviour, one per `GateMode`. -/

/-- **The safe-mode compiler preserves every outcome — from validity alone.**

    Halting with the observable store, faulting, and divergence, for the program the compiler emits under
    `--lcm=safe --pdce=safe` with the shipped seven-ghost analysis and the materialization gate.

    Nothing in this proof appeals to `πᵤ` being the least solution: the LCM obligation is discharged by
    `gateSound_materialized`, i.e. by three clauses of one ghost's **validity**. -/
theorem safe_compile_preserves_all (s : Stmt) (hnt : Stmt.noTmp s) :
    let Pc := Pass.Cleanup.cleanup (mainOptSafe .materialized .materialized s)
    (∀ fuel σ', Ast.evalS fuel s Store.init = .ok σ' →
        ∃ f sf, Asm.run (TacToAsm.codegen Pc) f (TacToAsm.initState Pc Store.init) = .halted sf
              ∧ ∀ v ∈ (lower s).obs,
                  sf.mem (TacToAsm.slot (TacToAsm.collectVars Pc) v) = TacToAsm.encode (σ' v))
  ∧ (∀ fuel, Ast.evalS fuel s Store.init = .fault →
        Asm.Faults (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init))
  ∧ ((∀ fuel, Ast.evalS fuel s Store.init = .timeout) →
        Asm.Diverges (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init)) :=
  have hg : Analyses.LCM.GateSound (safeP₀ s) (safeSlcm .materialized .materialized s) :=
    Analyses.LCM.gateSound_materialized _ rfl
  ⟨fun fuel σ' h => safepipe_preserves_halt _ _ s fuel σ' hnt h hg,
   fun fuel h => safepipe_preserves_fault _ _ s fuel hnt h hg,
   fun h => safepipe_preserves_diverge _ _ s hnt h hg⟩

/-- **…and from extremality**, for the classical demand gate on the six-ghost analysis — the safe-mode
    compiler exactly as it stood before the seventh ghost existed. Same three conclusions; the LCM
    obligation is discharged by `gateSound_demand`, which costs `Extremal` and the entry `noop`. -/
theorem safe_compile_preserves_all_demand (s : Stmt) (hnt : Stmt.noTmp s) :
    let Pc := Pass.Cleanup.cleanup (mainOptSafe .classic .demand s)
    (∀ fuel σ', Ast.evalS fuel s Store.init = .ok σ' →
        ∃ f sf, Asm.run (TacToAsm.codegen Pc) f (TacToAsm.initState Pc Store.init) = .halted sf
              ∧ ∀ v ∈ (lower s).obs,
                  sf.mem (TacToAsm.slot (TacToAsm.collectVars Pc) v) = TacToAsm.encode (σ' v))
  ∧ (∀ fuel, Ast.evalS fuel s Store.init = .fault →
        Asm.Faults (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init))
  ∧ ((∀ fuel, Ast.evalS fuel s Store.init = .timeout) →
        Asm.Diverges (TacToAsm.codegen Pc) (TacToAsm.initState Pc Store.init)) :=
  by
  obtain ⟨ne, hen⟩ := normalize_entry_noop (safePi s)
  have hg : Analyses.LCM.GateSound (safeP₀ s) (safeSlcm .classic .demand s) :=
    Analyses.LCM.gateSound_demand (safeSlcm .classic .demand s) rfl
      (((Analyses.LcmMat.LcmAnalysis.classic.bundle_extremal (safeP₀ s) (safeP₀_wf s)).withGate
          .demand).withKeep Expr.faultFree)
      (safeP₀_wn s) hen
  exact ⟨fun fuel σ' h => safepipe_preserves_halt _ _ s fuel σ' hnt h hg,
    fun fuel h => safepipe_preserves_fault _ _ s fuel hnt h hg,
    fun h => safepipe_preserves_diverge _ _ s hnt h hg⟩

#assert_clean_axioms safepipe_preserves_halt
#assert_clean_axioms safepipe_preserves_fault
#assert_clean_axioms safepipe_preserves_diverge
#assert_clean_axioms safe_compile_preserves_all
#assert_clean_axioms safe_compile_preserves_all_demand

end BaseLanguage.Compile
