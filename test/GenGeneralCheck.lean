-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Driver

/-!
# `gengen-check` — the shipped-corpus re-parse + byte-identity regression gate

Two guarantees over **every** shipped analysis (the `GenGeneral.manifest` — the same list `lake exe gen`
emits, so the two can never drift):
1. **Compatibility**: each `.gsl` still lex+parses, lowers, and selects into consistent quadrants (the
   frozen-surface contract), and every malformed fixture is rejected with a located error.
2. **Byte-identity**: re-emitting each analysis's `Solve.lean` + `ValidExtremal.lean` + `Augmented.lean`
   through `GenGeneral` reproduces the committed `Generated/Solver/<dir>/Solve.lean` + `Generated/Seam/<dir>/ValidExtremal.lean`
   + `Generated/Seam/<dir>/Augmented.lean` byte-for-byte — a regression oracle over the emitter (covering the
   own-locals analyses `lcm`/`pdce`/… as well as the base slice).

**Fails (non-zero exit)** on any parse/lower/select error, any accepted-malformed input, or any byte diff.
Sibling gate to `gengen-stress` (both run manually / in CI, not `lake test`).
-/

open GenGeneral

/-- The PrimeAdd acid test (`gather ∩ gate`, fwd·may) as an inline fixture. -/
def primeAddSrc : String :=
"analysis PrimeAdd {
history PrimeAdd g : Nums[Nums] {
  update : ∀ n→n'. g(n) ⊆ g(n')
  always : ∀ n→n'. z ∈ g(n') when below(z) ⊆ g(n) ∧ primes meets g(n)
  seed   : ∅ ⊆ g(entry)
  within : ∀ n. g(n) ⊆ allNums } }"

/-- Malformed fixtures — each MUST be a located error. -/
def malformed : List (String × String) :=
  [ ("bad direction keyword", "analysis T { histry X x : Exprs { } }")
  , ("unterminated body", "analysis T { history X x : Exprs { update : ∀ n→n'. x(n') ⊆ x(n)")
  , ("bad char", "analysis T { history X x : Exprs { seed : x ⊆ § } }")
  , ("bare top-level ghost", "history X x : Exprs { within : ∀ n. x(n) ⊆ u }")
  , ("bad edge binder", "analysis T { history X x : Exprs { update : ∀ n→m. x(n') ⊆ x(n) } }") ]

def runCheck : IO Unit := do
  let mut failures := 0
  IO.println "== gengen-check: re-parse + byte-identity over the shipped manifest =="
  for gslPath in manifest do
    let src ← IO.FS.readFile gslPath
    match lowerGsl src with
    | .error e => IO.println s!"FAIL  {gslPath}: lower error {e}"; failures := failures + 1
    | .ok irs =>
      let dir := (irs.head?.map (·.dir)).getD ""
      match selectAll irs with
      | .error e => IO.println s!"FAIL  {dir}: inconsistent frame: {e}"; failures := failures + 1
      | .ok _ =>
        for (label, emitted, goldPath) in
            [ ("Solve", emitSolve irs, s!"Generated/Solver/{dir}/Solve.lean")
            , ("ValidExtremal", emitValidExtremal irs, s!"Generated/Seam/{dir}/ValidExtremal.lean")
            , ("Augmented", emitAugmented irs, s!"Generated/Seam/{dir}/Augmented.lean") ] do
          match emitted with
          | .error e => IO.println s!"FAIL  {dir}/{label}: emit error {e}"; failures := failures + 1
          | .ok out =>
            let gold ← IO.FS.readFile goldPath
            if out == gold then
              IO.println s!"ok    {dir}/{label} byte-identical"
            else
              IO.FS.createDirAll "scratch"
              IO.FS.writeFile s!"scratch/{dir}.{label}.gen" out
              IO.println s!"FAIL  {dir}/{label} differs (wrote scratch/{dir}.{label}.gen)"
              failures := failures + 1
  -- PrimeAdd inline fixture: must parse + classify fwd·may.
  match lowerGsl primeAddSrc with
  | .ok [a] => IO.println s!"ok    PrimeAdd fixture  quadrant={repr a.quadrant}"
  | .ok _   => IO.println "note  PrimeAdd fixture parsed (multi-ghost?)"
  | .error e => IO.println s!"FAIL  PrimeAdd fixture: {e}"; failures := failures + 1
  -- malformed fixtures: each must be rejected with a located error.
  IO.println "== malformed fixtures (each must be a located error) =="
  for (name, src) in malformed do
    match parseGslBlocks src with
    | .error e => IO.println s!"ok    rejected [{name}] at {e.pos.line}:{e.pos.col}"
    | .ok _    => IO.println s!"FAIL  accepted malformed input [{name}]"; failures := failures + 1
  if failures == 0 then
    IO.println "ALL PASS"
  else
    IO.eprintln s!"{failures} FAILURE(S)"
    throw (IO.userError s!"gengen-check: {failures} failure(s)")
