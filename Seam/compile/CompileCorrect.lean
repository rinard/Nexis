-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Correctness.PipelineToAsm
import Seam.lcm.Adapter
import Seam.lcmmat.Adapter
import Seam.pdce.Adapter
import Seam.reachable.Adapter
import Seam.constprop.Adapter
/-!
# `compile.CompileCorrect` — the `prophecyc` compiler is correct, end to end.

`main_compile_correct` is `pipeline_to_asm` instantiated with the compiler's *concrete* passes — the
generated `lcmSolved`/`pdceSolved` bundles, the constant-propagation `optProvider`, and the `Pn.size`
fixpoint bound — so it is a statement about the program `Main` actually emits, not an abstract family:

```
codegen ∘ cleanup ∘ PDCE ∘ LCM ∘ normalize ∘ iterateOpt optProvider Pn.size ∘ normalize ∘ peephole ∘ lower
```

`optProvider` and `mainOpt` here are exactly what `Main` runs (`Main` imports them), so `main_compile_correct`
covers the real compiler. Axiom-clean `[propext, Classical.choice, Quot.sound]`, and — since the LCM
replace gate started reading the materialization ghost — free of any extremality hypothesis: the LCM
bundle enters as an arbitrary **valid** `LcmSpec`.
-/
namespace BaseLanguage.Compile
open BaseLanguage Tac Ast Semantics Normalize AstToTac

/-- The re-analysis provider `Main` feeds to `Pass.iterateOpt`: analyse a program into the three specs one
    optimization round needs. Computable (spec proofs erase; only `cpSol`/`reachSol` are data). -/
def optProvider : Pass.Provider := fun Q wfQ =>
  let s1 := Analyses.ConstProp.cpSpec Q wfQ
  let wf1 := Pass.ConstFold.run_wellFormed s1 wfQ
  let s2 := Analyses.ConstProp.cpSpec (Pass.ConstFold.run Q s1) wf1
  let wf2 := Pass.BranchFold.run_wellFormed s2 wf1
  { scp1 := s1, scp2 := s2,
    sreach := Analyses.Reachable.reachSpec (Pass.BranchFold.run (Pass.ConstFold.run Q s1) s2) wf2 }

/-- The optimized IR (fed to `cleanup` then codegen), exactly as `Main.optStages` builds it,
    parameterized by **which LCM analysis** supplies the bundle.

    Parameterized by **which LCM analysis** supplies the bundle and **which replace gate** the transform
    consults. `.classic` is the six-ghost analysis (`Lcm.gsl`), `.materialized` the seven-ghost one
    (`LcmMat.gsl`); `.demand` is the classical `πᵤ` gate, `.materialized` the `ηₘ` gate. The end-to-end
    theorem below covers every combination with one proof, discharging the LCM obligation from
    validity or from extremality as the gate requires.

    **Must keep mirroring `Main.optStages`**, or `main_compile_correct` stops being a statement about
    the compiler we actually ship. -/
noncomputable def mainOptWith (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) : Program :=
  -- normalize #1, then const-prop to a fixpoint — before the expensive structural passes
  let Pn := normalize (Peephole.peephole (lower s))
  let Pi := Pass.iterateOpt optProvider Pn.size Pn (wn_preOpt s).wf
  -- normalize #2 rebuilds every `WellNormalized` field for LCM
  let P₀ := normalize Pi
  let wf₀ := (normalize_wellNormalized Pi
    (Pass.iterateOpt_wf optProvider Pn.size Pn (wn_preOpt s).wf)
    (Pass.iterateOpt_allReachable optProvider Pn.size Pn (wn_preOpt s).wf (wn_preOpt s).allReach)).wf
  let Slcm := (a.bundle P₀ wf₀).withGate g
  let Spdce := Analyses.PDCE.pdceSolved (Analyses.LCM.transform P₀ Slcm) (Analyses.LCM.transform_wellFormed Slcm wf₀)
  Analyses.PDCE.transform (Analyses.LCM.transform P₀ Slcm) Spdce

/-- **The `prophecyc` compiler is correct.** If the reference interpreter runs `s` to `σ'`, the ARM64
    program the compiler emits (`codegen ∘ cleanup ∘ mainOpt`) runs from its initial state to a halted
    machine state whose frame holds `σ'`'s value (under `encode`) for every observable source variable. -/
theorem main_compile_correct_with (a : Analyses.LcmMat.LcmAnalysis) (g : Analyses.LCM.GateMode)
    (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (Pass.Cleanup.cleanup (mainOptWith a g s))) f
              (TacToAsm.initState (Pass.Cleanup.cleanup (mainOptWith a g s)) Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (Pass.Cleanup.cleanup (mainOptWith a g s))) v)
                = TacToAsm.encode (σ' v) :=
  pipeline_to_asm s fuel σ' hnt h optProvider _ _ _
    (by
      -- generic over both gates, so this one *does* touch both discharges
      obtain ⟨ne, hen⟩ := normalize_entry_noop
        (Pass.iterateOpt optProvider (normalize (Peephole.peephole (lower s))).size
          (normalize (Peephole.peephole (lower s))) (wn_preOpt s).wf)
      cases hgate : ((a.bundle _ _).withGate g).gate with
      | materialized => exact Analyses.LCM.gateSound_materialized _ hgate
      | demand       =>
          exact Analyses.LCM.gateSound_demand _ hgate ((a.bundle_extremal _ _).withGate g)
            (normalize_wellNormalized _
              (Pass.iterateOpt_wf optProvider _ _ (wn_preOpt s).wf)
              (Pass.iterateOpt_allReachable optProvider _ _ (wn_preOpt s).wf
                (wn_preOpt s).allReach)) hen) _

/-- The IR the shipped default emits — the six-ghost analysis with the classical demand gate, exactly
    the configuration `Main` selects when no flag is given. **Must keep mirroring `Main.optStages`.** -/
noncomputable def mainOpt (s : Stmt) : Program := mainOptWith .classic .demand s

/-- **The `prophecyc` compiler is correct**, for the shipped default: the six-ghost analysis with the
    classical KRS demand gate — the compiler as it stood before the seventh ghost existed.

    This path supplies `gateSound_demand`, so it *does* rest on `πᵤ` being the **least** solution:
    `recoverable = πᵤK ∪ insertBefore` is kept honest by bounding a least fixpoint from below, which is
    second-order and therefore assumable only as `Extremal S`. Contrast `main_compile_correct_mat`. -/
theorem main_compile_correct (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (Pass.Cleanup.cleanup (mainOpt s))) f
              (TacToAsm.initState (Pass.Cleanup.cleanup (mainOpt s)) Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (Pass.Cleanup.cleanup (mainOpt s))) v)
                = TacToAsm.encode (σ' v) :=
  -- `gateSound_demand` and nothing else — deliberately *not* routed through `main_compile_correct_with`,
  -- so that ablating either gate's discharge breaks exactly one of these two theorems.
  pipeline_to_asm s fuel σ' hnt h optProvider _ _ _
    (by
      obtain ⟨ne, hen⟩ := normalize_entry_noop
        (Pass.iterateOpt optProvider (normalize (Peephole.peephole (lower s))).size
          (normalize (Peephole.peephole (lower s))) (wn_preOpt s).wf)
      exact Analyses.LCM.gateSound_demand _ rfl
        ((Analyses.LcmMat.LcmAnalysis.classic.bundle_extremal _ _).withGate .demand)
        (normalize_wellNormalized _
          (Pass.iterateOpt_wf optProvider _ _ (wn_preOpt s).wf)
          (Pass.iterateOpt_allReachable optProvider _ _ (wn_preOpt s).wf
            (wn_preOpt s).allReach)) hen) _

/-- **…and for the seventh-ghost configuration**, selected by
    `--lcm-analysis=mat --lcm-gate=materialized`. Same statement, same emitted code — but proved
    **without extremality**: `gateSound_materialized` discharges `pipeline_to_asm`'s LCM hypothesis from
    the gate alone, so nothing on this path appeals to `πᵤ` being the least solution, to the
    `prependEntry` `noop` entry, or to `Extremal` in any form.

    Both theorems are live, and the difference between their proofs is the whole result. -/
theorem main_compile_correct_mat (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen
                (Pass.Cleanup.cleanup (mainOptWith .materialized .materialized s))) f
              (TacToAsm.initState
                (Pass.Cleanup.cleanup (mainOptWith .materialized .materialized s)) Store.init)
              = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars
                (Pass.Cleanup.cleanup (mainOptWith .materialized .materialized s))) v)
                = TacToAsm.encode (σ' v) :=
  pipeline_to_asm s fuel σ' hnt h optProvider _ _ _
    (Analyses.LCM.gateSound_materialized _ rfl) _

#assert_clean_axioms main_compile_correct_with
#assert_clean_axioms main_compile_correct
#assert_clean_axioms main_compile_correct_mat

end BaseLanguage.Compile
