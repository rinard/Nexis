-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Emit

/-!
# `GenGeneral.Driver` — the `gen` executable's driver (`lake exe gen`)

Emits each analysis's `Generated/Solver/<name>/Solve.lean` (below the seam) + `Generated/Seam/<name>/ValidExtremal.lean` +
`Generated/Seam/<name>/Augmented.lean` (the seam) from its `.gsl` surface + authored defs, via the pure-data
pipeline (`GenGeneral.lowerGsl` → `emitSolve` / `emitValidExtremal` / `emitAugmented`). **No reflection,
no `MetaM`** — pure text-in/text-out.

Everything the emitter needs is on the `.gsl` surface: element types (`: Dom[Elem]`), node-local sources
(`include`), predicate names (the ghost names), output dir + emit namespace (the `analysis <Name>`). So the
manifest is just the **list of `.gsl` paths** — no per-analysis config at all.

All 25 shipped/demo analyses are on this path: the base-family fixpoints, `pdce`/`lcm`/`live` (bundle /
meets-form), the atom analyses `structavail`/`taint`/`primeadd` (gather / image / gather∩gate), the
general-`predict` / backward-atom analyses `bwdchain`/`bwdmay`/`bwdslice`/`gatedlive`, the generality demo
`demogate`, and the four doubly-clamped demos `dcbwdmust`/`dcfwdmust`/`dcfwdmay`/`dcbwdmay` (the `res*C`
cap-the-transfer solvers). The compiler-facing `lcm`/`pdce` additionally have a hand-authored `Adapter.lean`.
-/

namespace GenGeneral

/-- Emit one analysis: lower its `.gsl` to the `AnalysisIR`, then write `Generated/Solver/<dir>/Solve.lean` +
    `Generated/Seam/<dir>/ValidExtremal.lean` via the term-generic emitter. -/
def emitAnalysis (gslPath : String) : IO Unit := do
  let src ← IO.FS.readFile gslPath
  match lowerGsl src with
  | .error e => throw (IO.userError s!"GenGeneral lower failed for {gslPath}: {e}")
  | .ok irs =>
    let dir := (irs.head?.map (·.dir)).getD ""   -- derived: the analysis name, lower-cased
    match emitSolve irs, emitValidExtremal irs, emitAugmented irs with
    | .ok solve, .ok valid, .ok augmented =>
      IO.FS.createDirAll s!"Generated/Solver/{dir}"
      IO.FS.createDirAll s!"Generated/Seam/{dir}"
      IO.FS.writeFile s!"Generated/Solver/{dir}/Solve.lean" solve
      IO.FS.writeFile s!"Generated/Seam/{dir}/ValidExtremal.lean" valid
      IO.FS.writeFile s!"Generated/Seam/{dir}/Augmented.lean" augmented
      IO.println s!"wrote Generated/Solver/{dir}/Solve.lean + Generated/Seam/{dir}/ValidExtremal.lean + Generated/Seam/{dir}/Augmented.lean (GenGeneral)"
    | s, v, g =>
      let msg := (match s with | .error e => s!" Solve: {e}" | _ => "") ++ (match v with | .error e => s!" VE: {e}" | _ => "")
                 ++ (match g with | .error e => s!" Aug: {e}" | _ => "")
      throw (IO.userError s!"GenGeneral emit failed for {dir}:{msg}")

/-- The emit manifest — every shipped analysis's `.gsl`, in emit order. The **single source of truth** for
    both `runGen` (writes the files) and `gengen-check` (re-emits and byte-diffs them), so the two can never
    drift. Just paths — every per-analysis knob now lives on the `.gsl` surface. -/
def manifest : List String :=
  [ "analyses/live/Live.gsl"              -- standalone bwd·may·gate (meets-form), non-bundle demo
  , "analyses/pdce/Pdce.gsl"              -- Sink (fwd·must) + Live (bwd·may·gate), bundle; compiler-facing
  , "analyses/pdcefault/PdceFault.gsl"    -- PDCE + one floor clause: fault-preserving liveness
  -- the base-family fixpoint analyses (fwd/bwd · must/may), node-locals from `Tac.Locals`
  , "analyses/available/Available.gsl"
  , "analyses/availdefs/AvailDefs.gsl"
  , "analyses/definiteassign/DefiniteAssign.gsl"
  , "analyses/partialavail/PartialAvail.gsl"
  , "analyses/reaching/Reaching.gsl"
  , "analyses/maybeassign/MaybeAssign.gsl"
  , "analyses/verybusy/VeryBusy.gsl"
  , "analyses/anticdefs/AnticDefs.gsl"
  , "analyses/reachable/Reachable.gsl"
  , "analyses/constprop/ConstProp.gsl"   -- fwd·must over ⟨var,const⟩ (`ConstPairs[CPair]`)
  , "analyses/lcm/Lcm.gsl"               -- 7 ghosts, every quadrant + both confluence ops; compiler-facing
  , "analyses/lcmmat/LcmMat.gsl"         -- Lcm + a materialization ghost: validity-sufficient replace gate
  , "analyses/structavail/StructAvail.gsl" -- `gather` atom (AND-gather)
  , "analyses/taint/Taint.gsl"           -- `image` atom (OR-gather / ∃)
  , "analyses/primeadd/PrimeAdd.gsl"     -- compound `gather ∩ gate`
  -- general-`predict` / backward-atom analyses (non-diamond via the `flowBwd` pass-through)
  , "analyses/bwdchain/BwdChain.gsl"
  , "analyses/bwdmay/BwdMay.gsl"
  , "analyses/bwdslice/BwdSlice.gsl"     -- backward `image` atom
  , "analyses/gatedlive/GatedLive.gsl"   -- set-level `gate` atom (meets-form)
  , "analyses/demogate/DemoGate.gsl"     -- GENERALITY DEMO: gate + GENERAL carrier ⇒ evs-form pass-through (no other corpus instance)
  -- doubly-clamped DEMOS: both a floor AND a ceiling ⇒ the `res*C` cap-the-transfer solvers (one per quadrant)
  , "analyses/dcbwdmust/DcBwdMust.gsl"   -- bwd·must doubly-clamped ⇒ resBMC
  , "analyses/dcfwdmust/DcFwdMust.gsl"   -- fwd·must doubly-clamped ⇒ resFMC
  , "analyses/dcfwdmay/DcFwdMay.gsl"     -- fwd·may  doubly-clamped ⇒ resFmC
  , "analyses/dcbwdmay/DcBwdMay.gsl"     -- bwd·may  doubly-clamped ⇒ resBmC
  -- lone FORWARD single-clamp DEMOS: no forward single-clamp solver, so routed to res*C with the opposite
  -- bound defaulted (∅ floor / universe ceiling)
  , "analyses/fwdceil/FwdCeil.gsl"       -- fwd·must lone ceiling ⇒ resFMC (floor defaulted to ∅)
  , "analyses/fwdfloor/FwdFloor.gsl"     -- fwd·may  lone floor   ⇒ resFmC (ceiling defaulted to universe)
  , "analyses/fwdmustfloor/FwdMustFloor.gsl" -- fwd·must lone floor   ⇒ resFMC (ceiling defaulted to universe)
  , "analyses/fwdmayceil/FwdMayCeil.gsl" ]   -- fwd·may  lone ceiling ⇒ resFmC (floor defaulted to ∅)

/-- The whole `gen` run: emit every analysis in the `manifest`. -/
def runGen : IO Unit := do
  for gslPath in manifest do
    emitAnalysis gslPath

end GenGeneral
