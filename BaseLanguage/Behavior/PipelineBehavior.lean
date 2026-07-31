-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Behavior.LowerBehavior
import BaseLanguage.Behavior.NormalizeBehavior
import BaseLanguage.Behavior.CodegenBehavior
import BaseLanguage.Peephole.Pass

namespace BaseLanguage

/-!
# `Behavior/PipelineBehavior.lean` — full behavioral preservation of the optimizer-free skeleton

The headline. For the **non-optimizing** compiler skeleton `Pf := codegen (normalize (lower s))` — the
`prophecyc` pipeline with the two optimizer passes (`Analyses.LCM.transform`, `Analyses.PDCE.transform`) **omitted** —
all three source outcomes are preserved:

* `skeleton_preserves_halt`    — `evalS … = .ok σ'` ⟹ machine halts, frame holds `σ'` on observables;
* `skeleton_preserves_fault`   — `evalS … = .fault` ⟹ `Asm.Faults`;
* `skeleton_preserves_diverge` — `∀ fuel, evalS … = .timeout` ⟹ `Asm.Diverges`.

This is the guarantee the end-to-end `pipeline_to_asm` (which *includes* the optimizers) deliberately does
**not** give: that one is halting-run observable refinement only. Faults/divergence are preserved here
precisely because the skeleton has no code motion — `lower`/`normalize`/`codegen` are deterministic,
structure-preserving plus-simulations (each source step ⟹ ≥ 1 target steps, nothing speculatively moved,
deleted, or reordered). The three results compose the per-stage lemmas from `LowerBehavior`,
`NormalizeBehavior`, `CodegenBehavior`; they reference **no** optimizer transform or solver.
-/

namespace AstToTac

open Tac Ast Semantics Normalize

/-- **Skeleton preserves halting.** `evalS s = .ok σ'` ⟹ `codegen (normalize (lower s))` halts, its frame
    holding `σ'` for every observable source variable. (Recomposes the existing halting simulations, with
    the optimizers omitted.) -/
theorem skeleton_preserves_halt (s : Stmt) (fuel : Nat) (σ' : Store)
    (hnt : Stmt.noTmp s) (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (normalize (Peephole.peephole (lower s))))
              f (TacToAsm.initState (normalize (Peephole.peephole (lower s))) Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (normalize (Peephole.peephole (lower s)))) v)
                = TacToAsm.encode (σ' v) := by
  have hobs0 : ∀ v ∈ (lower s).obs, varIsOrig v = true := by
    intro v hv; obtain ⟨n, rfl⟩ := lower_obs_orig s v hv; rfl
  -- ① frontend
  obtain ⟨cf0, hs0, hfin0, hframe0⟩ := lower_correct s fuel σ' hnt h
  -- ①.5 peephole (the first pass)
  obtain ⟨cfpe, hspe, hfinpe, hope⟩ := Peephole.peephole_preserves_halt hs0 hfin0
  -- ② normalize
  obtain ⟨cf1, hs1, hfin1, ho1⟩ :=
    normalize_preserves_halt (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hobs0 hspe hfinpe
  -- ③ backend
  obtain ⟨f, sf, hrun, hmem⟩ := TacToAsm.codegen_simulates hs1 hfin1
  refine ⟨f, sf, hrun, fun v hv => ?_⟩
  rw [hmem v, ho1 v hv, hope v hv, hframe0 v (lower_obs_orig s v hv)]

/-- **Skeleton preserves faults.** `evalS s = .fault` ⟹ the machine faults. -/
theorem skeleton_preserves_fault (s : Stmt) (fuel : Nat)
    (hnt : Stmt.noTmp s) (h : Ast.evalS fuel s Store.init = .fault) :
    Asm.Faults (TacToAsm.codegen (normalize (Peephole.peephole (lower s))))
      (TacToAsm.initState (normalize (Peephole.peephole (lower s))) Store.init) := by
  obtain ⟨cf0, hs0, hflt0⟩ := lower_faultSteps s fuel hnt h
  obtain ⟨cfpe, hspe, hfltpe⟩ :=
    Peephole.peephole_preserves_faultSteps (lower_wellFormed s) hs0 hflt0
  obtain ⟨cf1, hs1, hflt1⟩ :=
    normalize_preserves_faultSteps (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hspe hfltpe
  exact TacToAsm.codegen_faults hs1 hflt1

/-- **Skeleton preserves divergence.** `∀ fuel, evalS s = .timeout` ⟹ the machine runs forever. -/
theorem skeleton_preserves_diverge (s : Stmt)
    (hnt : Stmt.noTmp s) (h : ∀ fuel, Ast.evalS fuel s Store.init = .timeout) :
    Asm.Diverges (TacToAsm.codegen (normalize (Peephole.peephole (lower s))))
      (TacToAsm.initState (normalize (Peephole.peephole (lower s))) Store.init) := by
  have hd0 := lower_diverges s hnt h
  have hdpe := Peephole.peephole_preserves_diverge (lower_wellFormed s) hd0
  have hd1 := normalize_preserves_diverge (Peephole.peephole_wellFormed (lower s) (lower_wellFormed s)) hdpe
  exact TacToAsm.codegen_diverges hd1

end AstToTac

end BaseLanguage
