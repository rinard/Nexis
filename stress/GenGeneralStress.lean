-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Lower
import GenGeneral.Select
import GenGeneral.Printer

/-!
# `gengen-stress` — a spiky stress corpus + regression **gate** for the general pipeline

Reads every `stress/*.gsl` (deliberately bizarre / compound / deeply-nested specifications, taking
`PrimeAdd` as the seed) and classifies each: does it **lex+parse** the frozen grammar and **lower+select**
into quadrants, or is it **rejected** by the totality contract with a located error — at lowering (a
non-`Leaf` `∩`, a standalone `∅`, a missing `within`) or selection (a cyclic / self-referential frame)?

Unlike a pure diagnostic, this is a **gate**: each spec has an *expected* outcome and the runner exits
nonzero on any deviation (a parse break, a wrong quadrant, a lost/spurious rejection, an unexpected lower).
So the 28 boundary-probing specs are regression-tested — the success paths (every quadrant/atom/compound),
the generalized combinators (compound gather-sub / gate singleton, forward+backward set-level gate), AND
the reject paths (the totality contract's located errors) are all pinned. Sibling gate to `gengen-check`;
run both manually or wire them into CI (they exit nonzero on regression) — they are not part of `lake test`.
-/

open GenGeneral

/-- The classification of a spec's pipeline outcome (coarser than the human report, for stable
    expectations). `rejects` is the totality contract producing a **located error** — at either lowering (a
    non-`Leaf` `∩`, a standalone `∅`, a missing `within`) or selection (a cyclic / self-referential /
    clamp-inconsistent frame); the human report says which. -/
inductive Outcome
  | lowers (quads : String)   -- PARSE+LOWER+SELECT ok, with this `name·quadrant …` summary
  | rejects                   -- PARSE ok, a located error at LOWER or SELECT (the totality contract)
  | parseFail                 -- lex/parse error
deriving BEq, Repr

/-- Classify a spec, returning `(outcome, human-readable report line)`. -/
def classify (src : String) : Outcome × String :=
  match parseGslBlocks src with
  | .error e => (.parseFail, s!"PARSE-FAIL at {e.pos.line}:{e.pos.col}: {e.msg}")
  | .ok blocks =>
    let names := String.intercalate "," (blocks.map (·.name))
    match lowerGsl src with
    | .ok irs =>
      match selectAll irs with
      | .ok pairs =>
        let qs := String.intercalate " " (pairs.map (fun (a, q) => s!"{a.name}·{reprStr q |>.replace "GenGeneral.Quadrant." ""}"))
        (.lowers qs, s!"PARSE+LOWER ok  ({blocks.length} ghost: {names})  ⇒  {qs}")
      | .error e => (.rejects, s!"PARSE+LOWER ok; SELECT rejects: {e}")
    | .error e => (.rejects, s!"PARSE ok ({blocks.length} ghost: {names}); LOWER rejects: {e.msg}")

/-- The stress corpus, each with its **expected** pipeline outcome (deterministic order). A deviation from
    these is a regression (or a deliberate generalization that should update the expectation here). -/
def corpus : List (String × Outcome) :=
  [ ("01-PrimeAdd",        .lowers "PrimeAdd·fwdMay"),
    ("02-TriGuard",        .lowers "TriGuard·fwdMay"),
    ("03-DisjImage",       .lowers "DisjImage·fwdMay"),
    ("04-NestedGuard",     .lowers "NestedGuard·fwdMay"),
    ("05-ConstReach",      .lowers "ConstReach·fwdMust"),
    ("06-MeetChain",       .lowers "Base·fwdMust MeetA·meet JoinB·join MeetC·meet"),
    ("07-EdgeStorm",       .lowers "H1·fwdMust P1·bwdMust Edge·fwdMust"),
    ("08-DeepSet",         .lowers "DeepSet·fwdMust"),
    ("09-WideConj",        .lowers "WideConj·fwdMay"),
    ("10-DoubleAtom",      .lowers "DoubleAtom·bwdMay"),   -- backward, multi-atom guards (gather+image+set-gate)
    -- (11-20 continue below; 21-28 extend the corpus: reject-path + generalized-combinator coverage.)
    ("11-MutualConfluence", .rejects),                     -- cyclic foreign deps (no topological order)
    ("12-GatherDiff",      .lowers "GatherDiff·fwdMay"),   -- `∖`-compound gather-sub (now general)
    ("13-DiagGuard",       .lowers "DiagGuard·fwdMay"),
    ("14-TwoImages",       .lowers "TwoImages·fwdMay"),
    ("15-QuadZoo",         .lowers "FMust·fwdMust FMay·fwdMay BMust·bwdMust Meet·meet Join·join"),
    ("16-SelfRefMeet",     .rejects),                      -- confluence reading itself
    ("17-DeepParenGuard",  .lowers "DeepParen·fwdMay"),
    ("18-BareWithin",      .lowers "BareWithin·fwdMust"),
    ("19-BwdImage",        .lowers "BwdImage·bwdMay"),     -- backward analysis with an image-guarded `check`
    ("20-HugeConj",        .lowers "HugeConj·fwdMay"),
    -- reject paths (the totality contract as a corpus gate) — a located error, never a silent mislower:
    ("21-InterGatherSub",  .rejects),                      -- `∩` in a gather-sub (not `Leaf`-shaped)
    ("22-EmptyTransfer",   .rejects),                      -- `∅` as a standalone transfer term
    ("23-NoWithin",        .rejects),                      -- a ghost with no `within` universe
    ("24-InterGate",       .rejects),                      -- `∩` in a gate singleton (not `Leaf`-shaped)
    -- generalized combinators (pin this session's generalizations — should lower):
    ("25-UnionGatherSub",  .lowers "UnionGatherSub·fwdMay"),  -- `∪` gather-sub (complements GatherDiff's `∖`)
    ("26-UnionGate",       .lowers "UnionGate·fwdMay"),       -- `∪` gate singleton
    ("27-CarryImage",      .lowers "CarryImage·fwdMay"),      -- compound guarded-base (`self ∪ gen`) + image (taint shape)
    ("28-FwdSetGate",      .lowers "FwdSetGate·fwdMay"),      -- FORWARD set-level gate (gatedlive's forward twin)
    -- doubly-clamped (both a floor AND a ceiling) ⇒ the `res*C` cap-the-transfer quadrant, extremal from
    -- the propagation orientation; and the forward-single-clamp totality guard (rejected):
    ("29-DoubleClamp",     .lowers "DoubleClamp·bwdMust"),    -- floor + ceiling ⇒ doubly-clamped bwd·must
    -- lone FORWARD single clamps ⇒ res*C with the opposite bound defaulted (no forward single-clamp solver):
    ("30-FwdClamp",        .lowers "FwdClamp·fwdMust"),       -- lone forward ceiling ⇒ resFMC (floor = ∅)
    ("31-FwdFloor",        .lowers "FwdFloor·fwdMay"),        -- lone forward floor   ⇒ resFmC (ceiling = universe)
    ("32-FwdGuardClamp",   .rejects),                         -- forward guard + unguarded clamp ⇒ still rejected
    ("33-FwdMustFloor",    .lowers "FwdMustFloor·fwdMust"),   -- fwd·must + lone floor   ⇒ resFMC (ceiling = universe)
    ("34-FwdMayCeil",      .lowers "FwdMayCeil·fwdMay"),     -- fwd·may  + lone ceiling ⇒ resFmC (floor = ∅)
    ("35-BareFamily",      .parseFail),                      -- domain with no `[Elem]` ⇒ located error, not silent

    -- A const (non-ghost) family in a transfer is a `.src` leaf: it reads the CURRENT node. Applying one
    -- to `n'` / `n n'` cannot be honoured (only a parameterised *placement* `f(…)(n')` carries a `readAt`),
    -- so it must be a LOCATED ERROR rather than a silent read-at-`n` — a misparse that would emit the
    -- `gen(n)` analysis under a spec that says `gen(n')`.
    ("36-SuccConst",       .rejects),                        -- `gen(n')` in the canonical diamond
    ("37-EdgeConst",       .rejects) ]                       -- `gen(n,n')` on the general structural path

def runStress : IO UInt32 := do
  IO.println "== gengen-stress: the spiky stress corpus (regression gate) =="
  let mut fails := 0
  for (name, want) in corpus do
    let src ← IO.FS.readFile s!"stress/{name}.gsl"
    let (got, report) := classify src
    if got == want then
      IO.println s!"  ok    {name}.gsl  ⇒  {report}"
    else
      IO.println s!"  FAIL  {name}.gsl  expected {reprStr want}, got {reprStr got}\n           {report}"
      fails := fails + 1
  if fails == 0 then
    IO.println s!"== ALL {corpus.length} specs match expected (parse · lower/reject) =="
    return 0
  else
    IO.eprintln s!"== {fails} stress spec(s) DEVIATED from expected =="
    return 1
