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
import BaseLanguage.IR.Pretty
import BaseLanguage.Pass.Cleanup
import BaseLanguage.Pass.Optimize
import Seam.compile.CompileCorrect
import BaseLanguage.Peephole.Pass
import Seam.pdce.Adapter
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
def optStages (src : String) : Option (Tac.Program × Tac.Program × Tac.Program) :=
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
    let bL := Analyses.LCM.lcmSolved P₀ wf₀
    let P := Analyses.LCM.transform P₀ bL
    have wfP := Analyses.LCM.transform_wellFormed bL wf₀
    -- PDCE (partial-dead sinking) — LCM hoists into fresh temps and PDCE only sinks, so neither creates
    -- constants: a trailing const-prop pass would gain ~nothing.
    let S := Analyses.PDCE.pdceSolved P wfP
    (P₀, P, Analyses.PDCE.transform P S)

/-- The full source-to-assembler pipeline; `none` on a parse error. `clean` (on by default) runs the
    verified `Pass.Cleanup` noop-elimination + index-compaction before codegen — the whole path
    `codegen ∘ cleanup ∘ PDCE ∘ LCM ∘ normalize ∘ iterateOpt ∘ normalize ∘ peephole ∘ lower` is covered
    by `pipeline_to_asm`. -/
def compile (clean : Bool) (src : String) : Option String :=
  (optStages src).map (fun (_, _, final) =>
    AsmToText.emitText (if clean then Pass.Cleanup.cleanup final else final))

/-- Emit assembly through the optimizer-free skeleton `codegen ∘ normalize ∘ lower` (behavior-preserving,
    proved in `BaseLanguage.Behavior.*`), skipping every optimizing pass. For very large programs the
    optimizing dataflow analyses dominate compile time; `--no-opt` compiles them directly. The observable
    behavior is identical, since the optimizations preserve it. -/
def compileNoOpt (src : String) : Option String :=
  (TextToAst.parse src).map fun s =>
    AsmToText.emitText (Normalize.normalize (AstToTac.lower s))

/-- Print the IR before optimization, after LCM, after PDCE, and after cleanup. -/
def showOpt (src : String) : IO UInt32 :=
  match optStages src with
  | some (before, afterLCM, afterPDCE) => do
    IO.println "===== BEFORE OPTIMIZATION  (normalized IR) ====="
    IO.println (Tac.ppProgram before)
    IO.println "\n===== AFTER LCM  (lazy code motion / PRE) ====="
    IO.println (Tac.ppProgram afterLCM)
    IO.println "\n===== AFTER PDCE  (partial dead-code elimination) ====="
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
def emitStage (lowered : Bool) (src : String) : IO UInt32 :=
  match optStages src with
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
  let rest  := args.filter (fun a => !a.startsWith "--")
  let src ← match rest with
    | path :: _ => IO.FS.readFile path
    | []        => (← IO.getStdin).readToEnd
  if args.contains "--emit-lowered" then
    emitStage true src
  else if args.contains "--emit-opt" then
    emitStage false src
  else if args.contains "--no-opt" then
    match compileNoOpt src with
    | some asm => IO.print asm; pure 0
    | none     => IO.eprintln "prophecyc: parse error"; pure 1
  else if dump then
    showOpt src
  else
    match compile clean src with
    | some asm => IO.print asm; pure 0
    | none     => IO.eprintln "prophecyc: parse error"; pure 1
