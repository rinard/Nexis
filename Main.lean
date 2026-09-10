-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Frontend.TextToAst
import BaseLanguage.Pass.AstToTac
import BaseLanguage.Normalize.Normalize
import BaseLanguage.Normalize.FromLower
import BaseLanguage.Backend.AsmToText
import BaseLanguage.PDCE.Transform
import BaseLanguage.PDCE.Layout
import BaseLanguage.LCM.Transform
import BaseLanguage.LCM.Layout
import BaseLanguage.LCM.Mode
import BaseLanguage.IR.Pretty
import BaseLanguage.Pass.Cleanup
import BaseLanguage.Pass.Optimize
import Seam.compile.CompileCorrect
import BaseLanguage.Peephole.Pass
import Seam.pdce.Adapter
import Seam.pdce.Mode
import Seam.lcm.Adapter
import Seam.reachable.Adapter
import Seam.constprop.Adapter

/-!
# `prophecyc` — the compiler CLI

`TextToAst.parse → AstToTac.lower → Normalize.normalize → LCM.transform → PDCE.transform → AsmToText.emitText`.

* The **LCM** step is the KRS lazy-code-motion / PRE hoisting transform (`Analyses.LCM.transform`, the two-valued
  `Latestin`/`Latestout` lifetime-optimal variant — `transform_preserves_halt` proven, `Optimality.lean`),
  run over the bundle `Analyses.LCM.lcmSolved`.
* The **PDCE** step is the KRS partial-dead sinking transform (`Analyses.PDCE.transform`), run over `pdceSolved`.

Both bundles come from the generator (`lake exe gen`): the executable layer is the memoizing `solve`
**bundle** inside `Solver/{lcm,pdce}/Solve.lean`, and `lcmSolved`/`pdceSolved` (the adapters, in
`Seam/{lcm,pdce}/Adapter.lean`) project each ghost + carry its validity/extremality witness.
The witnesses are `sorry`-free under `WellFormed`, discharged here by `normalize_lower_wellNormalized` +
`transform_wellFormed`. Each transform is parameterized over an arbitrary valid, extremal bundle and is
verified correct for it (LCM: `transform_preserves_halt` + `Optimality`).
-/

open BaseLanguage

/-- The optimizer pipeline as three IR snapshots — `(beforeLCM, afterLCM, afterPDCE)` — or `none` on a
    parse error. `beforeLCM` is already const-propagated and re-normalized (const-prop runs *before* the
    structural passes). `compile` emits from the last; `--show-opt` prints all three. -/
def optStages (ana : Analyses.LcmMat.LcmAnalysis) (mode : Analyses.LCM.LcmMode)
    (pmode : Analyses.PDCE.PdceMode) (src : String) :
    Option (Tac.Program × Tac.Program × Tac.Program) :=
  (TextToAst.parse src).map fun s =>
    -- The peephole is the FIRST pass (verified: `pipeline_to_asm` / `skeleton_preserves_*` cover
    -- `codegen ∘ … ∘ normalize ∘ peephole ∘ lower`); it keeps reachability, so `normalize` stays
    -- `WellNormalized` and the LCM/PDCE `WellFormed` hypotheses are discharged as before.
    let Ppe := Tac.Peephole.peephole (AstToTac.lower s)
    let Pn := Normalize.normalize Ppe
    -- Constant-propagation optimization, iterated to a fixpoint: each round is
    -- `constFold ∘ branchFold ∘ UCE` re-analyzed (`optProvider`), so constant chains propagate to any
    -- depth. `Pn.size` rounds is a safe bound (a chain is at most that long); extra rounds are no-ops.
    -- It runs BEFORE LCM/PDCE so the expensive structural passes see the simplified program: UCE has
    -- already dropped unreachable blocks, branchFold has removed join points (so more partial
    -- redundancies are full ones), and constFold has shrunk `listExpr` — the LCM ghosts' bitvector width.
    let Pi := Pass.iterateOpt Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf
    -- Re-normalize: rebuilds every `WellNormalized` field by construction (LCM's hypothesis). Costs one
    -- extra entry `noop`, which `cleanup` eliminates before codegen.
    let P₀ := Normalize.normalize Pi
    have wf₀ := (Normalize.normalize_wellNormalized Pi
      (Pass.iterateOpt_wf Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf)
      (Pass.iterateOpt_allReachable Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf
        (AstToTac.wn_preOpt s).allReach)).wf
    -- LCM (PRE / lazy code motion) hoist. `lcmSolved`/`pdceSolved` are the bundle-backed adapters
    -- (`Seam/{lcm,pdce}/Adapter.lean`): the memoizing `solve` bundle computed once, each ghost projected
    -- as `decF(solve).x` with its validity+extremality witness from `Solve.lean`. Each verified
    -- `transform` is parameterized over an arbitrary valid, extremal bundle.
    -- `runLcm` selects the mode by re-aiming the bundle's hoisting filter: `classic` is the KRS hoist
    -- (divergence out of scope); `preserve-divergence` hoists only fault-free expressions — per
    -- expression, leaving a `div`/`mod` in place while still hoisting everything else — which buys
    -- `runLcm_preserves_diverges` with no side condition. Both preserve halting behavior
    -- (`runLcm_preserves_halt`) and both are well-formed (`runLcm_wellFormed`).
    let bL := ana.bundle P₀ wf₀
    let P := Analyses.LCM.runLcm mode P₀ bL
    have wfP := Analyses.LCM.runLcm_wellFormed mode bL wf₀
    -- PDCE (partial-dead sinking) — LCM hoists into fresh temps and PDCE only sinks, so neither creates
    -- constants: a trailing const-prop pass would gain ~nothing.
    -- `runPdce` selects the PDCE mode: `classic` is the KRS sinking transform (faults out of scope);
    -- `preserve-faults` runs the widened-floor analysis and declines to sink or eliminate a
    -- possibly-faulting assignment, which buys `runPdce_preserves_faulting`. Both preserve halting
    -- behavior and divergence.
    (P₀, P, Analyses.PDCE.runPdce pmode P wfP)

/-- The full source-to-assembler pipeline; `none` on a parse error. `clean` (on by default) runs the
    verified `Pass.Cleanup` noop-elimination + index-compaction before codegen — the whole path
    `codegen ∘ cleanup ∘ PDCE ∘ LCM ∘ normalize ∘ iterateOpt ∘ normalize ∘ peephole ∘ lower` is covered
    by `pipeline_to_asm`. -/
def compile (ana : Analyses.LcmMat.LcmAnalysis) (mode : Analyses.LCM.LcmMode)
    (pmode : Analyses.PDCE.PdceMode) (clean : Bool)
    (src : String) : Option String :=
  (optStages ana mode pmode src).map (fun (_, _, final) =>
    AsmToText.emitText (if clean then Pass.Cleanup.cleanup final else final))

/-- Emit assembly through the optimizer-free skeleton `codegen ∘ normalize ∘ lower` (behavior-preserving,
    proved in `BaseLanguage.Behavior.*`), skipping every optimizing pass. For very large programs the
    optimizing dataflow analyses dominate compile time; `--no-opt` compiles them directly. The observable
    behavior is identical, since the optimizations preserve it. -/
def compileNoOpt (src : String) : Option String :=
  (TextToAst.parse src).map fun s =>
    AsmToText.emitText (Normalize.normalize (AstToTac.lower s))

/-- Print the IR before optimization, after LCM, after PDCE, and after cleanup. -/
def showOpt (ana : Analyses.LcmMat.LcmAnalysis) (mode : Analyses.LCM.LcmMode)
    (pmode : Analyses.PDCE.PdceMode) (src : String) : IO UInt32 :=
  match optStages ana mode pmode src with
  | some (before, afterLCM, afterPDCE) => do
    IO.println "===== BEFORE OPTIMIZATION  (normalized IR) ====="
    IO.println (Tac.ppProgram before)
    IO.println s!"\n===== AFTER LCM  (lazy code motion / PRE; mode: {mode.name}) ====="
    IO.println (Tac.ppProgram afterLCM)
    IO.println s!"\n===== AFTER PDCE  (partial dead-code elimination; mode: {pmode.name}) ====="
    IO.println (Tac.ppProgram afterPDCE)
    IO.println "\n===== AFTER CLEANUP  (noop-elim + compaction; verified; fed to codegen) ====="
    IO.println (Tac.ppProgram (Pass.Cleanup.cleanup afterPDCE))
    pure 0
  | none => do
    IO.eprintln "prophecyc: parse error"
    pure 1

/-- Emit a single IR stage as text: the **lowered** (normalized) IR (`lowered = true`), or the
    **optimized** IR fed to codegen — after LCM, PDCE, and the verified cleanup noop-elimination
    (`lowered = false`). Used to dump one pipeline stage per file. -/
def emitStage (ana : Analyses.LcmMat.LcmAnalysis) (mode : Analyses.LCM.LcmMode) (pmode : Analyses.PDCE.PdceMode) (lowered : Bool)
    (src : String) : IO UInt32 :=
  match optStages ana mode pmode src with
  | some (before, _, afterPDCE) => do
      IO.println (Tac.ppProgram (if lowered then before else Pass.Cleanup.cleanup afterPDCE)); pure 0
  | none => do IO.eprintln "prophecyc: parse error"; pure 1

def main (args : List String) : IO UInt32 := do
  -- Optional leading flags: `--show-opt` (dump all IR stages), `--emit-lowered` (only the lowered IR),
  -- `--emit-opt` (only the optimized IR fed to codegen: after LCM+PDCE+cleanup), `--no-opt` (emit assembly
  -- via the optimizer-free skeleton `codegen ∘ normalize ∘ lower`), `--no-clean` (skip the verified cleanup
  -- pass, on by default). The remaining argument is the source path (stdin if absent).
  let dump  := args.contains "--show-opt"
  let clean := !args.contains "--no-clean"
  -- `--lcm=<mode>` picks the LCM mode: `classic` (default; the KRS hoist, divergence out of scope) or
  -- `safe` / `preserve-divergence` (hoist only fault-free expressions, so divergence is preserved).
  let modeArg := args.filter (fun a => a.startsWith "--lcm=")
  let mode ← match modeArg with
    | []     => pure Analyses.LCM.LcmMode.classic
    | a :: _ =>
      let spelling := (a.drop "--lcm=".length).toString
      match Analyses.LCM.LcmMode.ofString? spelling with
      | some m => pure m
      | none   => do
          IO.eprintln s!"prophecyc: unknown --lcm mode '{spelling}' \
                        (expected: classic | safe | preserve-divergence)"
          IO.Process.exit 1
  -- `--pdce=<mode>`: `classic` (default) or `safe` / `preserve-faults` (do not sink or eliminate a
  -- possibly-faulting assignment, so faults are preserved).
  let pmodeArg := args.filter (fun a => a.startsWith "--pdce=")
  let pmode ← match pmodeArg with
    | []     => pure Analyses.PDCE.PdceMode.classic
    | a :: _ =>
      let spelling := (a.drop "--pdce=".length).toString
      match Analyses.PDCE.PdceMode.ofString? spelling with
      | some m => pure m
      | none   => do
          IO.eprintln s!"prophecyc: unknown --pdce mode '{spelling}' \
                        (expected: classic | safe | preserve-faults)"
          IO.Process.exit 1
  -- `--lcm-analysis=<name>`: which LCM ghost specification supplies the bundle — `classic` (default,
  -- `analyses/lcm/Lcm.gsl`, six ghosts) or `mat` / `materialized` (`analyses/lcmmat/LcmMat.gsl`, the same
  -- six plus the `Materialized` availability ghost). Both are valid and extremal, so the emitted program
  -- is identical and `Compile.main_compile_correct_with` covers both with one proof.
  let anaArg := args.filter (fun a => a.startsWith "--lcm-analysis=")
  let ana ← match anaArg with
    | []     => pure Analyses.LcmMat.LcmAnalysis.classic
    | a :: _ =>
      let spelling := (a.drop "--lcm-analysis=".length).toString
      match Analyses.LcmMat.LcmAnalysis.ofString? spelling with
      | some m => pure m
      | none   => do
          IO.eprintln s!"prophecyc: unknown --lcm-analysis '{spelling}' \
                        (expected: classic | mat | materialized)"
          IO.Process.exit 1
  let rest  := args.filter (fun a => !a.startsWith "--")
  let src ← match rest with
    | path :: _ => IO.FS.readFile path
    | []        => (← IO.getStdin).readToEnd
  if args.contains "--emit-lowered" then
    emitStage ana mode pmode true src
  else if args.contains "--emit-opt" then
    emitStage ana mode pmode false src
  else if args.contains "--no-opt" then
    match compileNoOpt src with
    | some asm => IO.print asm; pure 0
    | none     => IO.eprintln "prophecyc: parse error"; pure 1
  else if dump then
    showOpt ana mode pmode src
  else
    match compile ana mode pmode clean src with
    | some asm => IO.print asm; pure 0
    | none     => IO.eprintln "prophecyc: parse error"; pure 1
