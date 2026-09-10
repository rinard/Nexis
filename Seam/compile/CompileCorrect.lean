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
covers the real compiler. Axiom-clean `[propext, Classical.choice, Quot.sound]`.
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

    Both settings of `a` deliver a valid, extremal `LcmSpec`, and the transform is generic over that, so
    the end-to-end theorem below is proved once and covers both. `.classic` is the six-ghost shipped
    analysis; `.materialized` is the seven-ghost one whose extra `Materialized` ghost carries the
    availability fact the validity-sufficient replace gate reads (`Seam/lcmmat/Sound.lean`).

    **Must keep mirroring `Main.optStages`**, or `main_compile_correct` stops being a statement about
    the compiler we actually ship. -/
noncomputable def mainOptWith (a : Analyses.LcmMat.LcmAnalysis) (s : Stmt) : Program :=
  -- normalize #1, then const-prop to a fixpoint — before the expensive structural passes
  let Pn := normalize (Peephole.peephole (lower s))
  let Pi := Pass.iterateOpt optProvider Pn.size Pn (wn_preOpt s).wf
  -- normalize #2 rebuilds every `WellNormalized` field for LCM
  let P₀ := normalize Pi
  let wf₀ := (normalize_wellNormalized Pi
    (Pass.iterateOpt_wf optProvider Pn.size Pn (wn_preOpt s).wf)
    (Pass.iterateOpt_allReachable optProvider Pn.size Pn (wn_preOpt s).wf (wn_preOpt s).allReach)).wf
  let Slcm := a.bundle P₀ wf₀
  let Spdce := Analyses.PDCE.pdceSolved (Analyses.LCM.transform P₀ Slcm) (Analyses.LCM.transform_wellFormed Slcm wf₀)
  Analyses.PDCE.transform (Analyses.LCM.transform P₀ Slcm) Spdce

/-- **The `prophecyc` compiler is correct.** If the reference interpreter runs `s` to `σ'`, the ARM64
    program the compiler emits (`codegen ∘ cleanup ∘ mainOpt`) runs from its initial state to a halted
    machine state whose frame holds `σ'`'s value (under `encode`) for every observable source variable. -/
theorem main_compile_correct_with (a : Analyses.LcmMat.LcmAnalysis)
    (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (Pass.Cleanup.cleanup (mainOptWith a s))) f
              (TacToAsm.initState (Pass.Cleanup.cleanup (mainOptWith a s)) Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (Pass.Cleanup.cleanup (mainOptWith a s))) v)
                = TacToAsm.encode (σ' v) :=
  pipeline_to_asm s fuel σ' hnt h optProvider _ _ _ (a.bundle_extremal _ _) _

/-- The IR the shipped default emits — `mainOptWith .classic`. -/
noncomputable def mainOpt (s : Stmt) : Program := mainOptWith .classic s

/-- **The `prophecyc` compiler is correct**, for the shipped default analysis: the `.classic` instance of
    `main_compile_correct_with`. -/
theorem main_compile_correct (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (Pass.Cleanup.cleanup (mainOpt s))) f
              (TacToAsm.initState (Pass.Cleanup.cleanup (mainOpt s)) Store.init) = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (Pass.Cleanup.cleanup (mainOpt s))) v)
                = TacToAsm.encode (σ' v) :=
  main_compile_correct_with .classic s fuel σ' hnt h

/-- **…and for the seven-ghost analysis**, by the same proof. This is the statement that the
    materialization-augmented LCM can be wired into the compiler driver with the end-to-end correctness
    theorem intact. -/
theorem main_compile_correct_mat (s : Stmt) (fuel : Nat) (σ' : Store) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (Pass.Cleanup.cleanup (mainOptWith .materialized s))) f
              (TacToAsm.initState (Pass.Cleanup.cleanup (mainOptWith .materialized s)) Store.init)
              = .halted sf
          ∧ ∀ v ∈ (lower s).obs,
              sf.mem (TacToAsm.slot
                (TacToAsm.collectVars (Pass.Cleanup.cleanup (mainOptWith .materialized s))) v)
                = TacToAsm.encode (σ' v) :=
  main_compile_correct_with .materialized s fuel σ' hnt h

end BaseLanguage.Compile
