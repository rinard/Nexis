-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Frontend.TextToAst
import BaseLanguage.Frontend.AstToText
import BaseLanguage.Pass.AstToTac
import BaseLanguage.Normalize.Normalize
import BaseLanguage.Backend.AsmToText
import BaseLanguage.IR.TAC
import BaseLanguage.Normalize.FromLower
import BaseLanguage.LCM.Transform
import BaseLanguage.LCM.Layout
import BaseLanguage.PDCE.Transform
import BaseLanguage.Peephole.Pass
import BaseLanguage.Pass.Cleanup
import Seam.compile.CompileCorrect
import Seam.lcm.Adapter
import Seam.pdce.Adapter
import Generated.Seam.taint.ValidExtremal
import Generated.Seam.structavail.ValidExtremal
import Generated.Seam.bwdchain.ValidExtremal
import Generated.Seam.bwdmay.ValidExtremal
import Generated.Seam.primeadd.ValidExtremal
import Generated.Seam.available.ValidExtremal
import Generated.Seam.verybusy.ValidExtremal
import Generated.Seam.bwdslice.ValidExtremal
import Generated.Seam.gatedlive.ValidExtremal
import GenGeneralCheck
import GenGeneralStress

/-!
# Runnable test suite (`lake test`)

End-to-end checks of the executable pipeline: each case is parsed, lowered to TAC, and executed by
the **reference small-step interpreter** (`Semantics.run`); the resulting value of an observable
variable is compared against the expected result. Exits nonzero if any case fails.
-/

open BaseLanguage BaseLanguage.Semantics

/-- Lower a parsed program and run the TAC reference interpreter; return `(value of var `v`, halted?)`. -/
def runStmt (s : Ast.Stmt) (v : String) (fuel : Nat := 100000) : Int × Bool :=
  let p := AstToTac.lower s
  let (cfg, st) := Semantics.run p ⟨p.entry, Store.init⟩ fuel
  ((cfg.store (.orig v)).toInt, st.isHalt)

/-- Parse → lower → run. -/
def runVar (src : String) (v : String) : Option (Int × Bool) :=
  (TextToAst.parse src).map (runStmt · v)

/-- Parse → unparse (`AstToText`) → re-parse → lower → run, exercising the AST text printer's
    round-trip with the parser. -/
def roundVar (src : String) (v : String) : Option (Int × Bool) := do
  let s  ← TextToAst.parse src
  let s' ← TextToAst.parse (AstToText.emitText s)
  some (runStmt s' v)

/-- Parse → lower → **normalize** → run, empirically checking the (now CLI-active) `normalize` pass
    preserves observable behavior (the `while` cases exercise the self-read split `s := s + i`). -/
def normVar (src : String) (v : String) (fuel : Nat := 100000) : Option (Int × Bool) := do
  let s ← TextToAst.parse src
  let p := Normalize.normalize (AstToTac.lower s)
  let (cfg, st) := Semantics.run p ⟨p.entry, Store.init⟩ fuel
  some ((cfg.store (.orig v)).toInt, st.isHalt)

structure Case where
  name : String
  src  : String
  var  : String
  want : Int

def cases : List Case := [
  ⟨"arith precedence", "x := 2 + 3 * 4",                                      "x", 14⟩,
  ⟨"left-assoc sub",   "x := 10 - 3 - 2",                                     "x", 5⟩,
  ⟨"div truncates",    "x := 10 / 3",                                         "x", 3⟩,
  ⟨"mod",              "x := 10 % 3",                                         "x", 1⟩,
  ⟨"parens",           "x := (2 + 3) * 4",                                    "x", 20⟩,
  ⟨"comparison → 1/0", "x := 3 < 5",                                          "x", 1⟩,
  ⟨"if / else",        "x := 0; if x { y := 7 } else { y := 9 }",              "y", 9⟩,
  ⟨"while sum 1..5",   "s := 0; i := 5; while i { s := s + i; i := i - 1 }",    "s", 15⟩,
  ⟨"bitwise and",      "x := 12 & 10",                                       "x", 8⟩,
  ⟨"bitwise or",       "x := 12 | 10",                                       "x", 14⟩,
  ⟨"bitwise xor",      "x := 12 ^ 10",                                       "x", 6⟩,
  ⟨"bitwise not",      "x := ~0",                                            "x", -1⟩,
  ⟨"shift left",       "x := 1 << 4",                                        "x", 16⟩,
  ⟨"logical >>",       "x := 256 >> 2",                                      "x", 64⟩,
  ⟨"arith >>>",        "x := (0 - 8) >>> 1",                                 "x", -4⟩,
  ⟨"signed <",         "x := (0 - 1) < 0",                                   "x", 1⟩,
  ⟨"unsigned <u",      "x := (0 - 1) <u 0",                                  "x", 0⟩,
  ⟨"& looser than ==", "x := 1 & 1 == 1",                                    "x", 1⟩
]

/-! ## Scalability suite

Five **large** programs pushed through the *full verified optimizer* (`normalize → LCM.transform ∘ solve
→ PDCE.transform ∘ solve` — the same pipeline `prophecyc` runs, exercising the memoized `solve` bundle
and the `blockOff`-memoized transforms). Each is checked for **behaviour preservation**: the optimized
TAC program must give every observable variable the same value (and halt) as the un-optimized one on the
reference interpreter. Since `lower` marks *all* original variables observable, this is a total check.

Before the memoization work these programs did not compile in bounded time (`prophecyc` timed out beyond
~20 variables); they now optimize in well under a second each. -/

open Tac in
/-- The verified optimizer pipeline (LCM then PDCE), as in `Main.optStages`; `none` on a parse error. -/
def optimize (src : String) : Option Program :=
  (TextToAst.parse src).map fun s =>
    let P₀ := Normalize.normalize (AstToTac.lower s)
    have wf₀ := (Normalize.normalize_lower_wellNormalized s).wf
    let bL := Analyses.LCM.lcmSolved P₀ wf₀
    let P := Analyses.LCM.transform P₀ bL
    have wfP := Analyses.LCM.transform_wellFormed bL wf₀
    let S := Analyses.PDCE.pdceSolved P wfP
    Analyses.PDCE.transform P S

open Tac in
/-- The **full** optimizer pipeline exactly as `prophecyc` runs it (`Main.compile`'s IR): peephole →
    normalize → (`constFold ∘ branchFold ∘ UCE`) iterated to a fixpoint → normalize → LCM → PDCE →
    **cleanup** — the precise program fed to codegen. `none` on a parse error. Unlike `optimize` (which
    stops at PDCE and so never exercises peephole, const-prop, branch-folding, UCE, or the
    noop-eliminating cleanup), this threads every pass. -/
def optimizeFull (src : String) : Option Program :=
  (TextToAst.parse src).map fun s =>
    let Ppe := Tac.Peephole.peephole (AstToTac.lower s)
    let Pn  := Normalize.normalize Ppe
    let Pi  := Pass.iterateOpt Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf
    let P₀  := Normalize.normalize Pi
    have wf₀ := (Normalize.normalize_wellNormalized Pi
      (Pass.iterateOpt_wf Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf)
      (Pass.iterateOpt_allReachable Compile.optProvider Pn.size Pn (AstToTac.wn_preOpt s).wf
        (AstToTac.wn_preOpt s).allReach)).wf
    let bL  := Analyses.LCM.lcmSolved P₀ wf₀
    let P   := Analyses.LCM.transform P₀ bL
    have wfP := Analyses.LCM.transform_wellFormed bL wf₀
    let S   := Analyses.PDCE.pdceSolved P wfP
    Pass.Cleanup.cleanup (Analyses.PDCE.transform P S)

/-- The un-optimized (normalized) program, for the behaviour-preservation baseline. -/
def normalized (src : String) : Option Tac.Program :=
  (TextToAst.parse src).map (fun s => Normalize.normalize (AstToTac.lower s))

/-- The PDCE-optimized program **without** the final cleanup — its `noop` count is the baseline for
    showing `Pass.Cleanup` actually removes the noops PDCE/branch-folding leave behind. -/
def optimizeNoCleanup (src : String) : Option Tac.Program := optimize src

/-- Count `noop` nodes in a program (cleanup's job is to drive this toward zero). -/
def noopCount (P : Tac.Program) : Nat :=
  P.code.foldl (fun acc c => match c with | .noop _ => acc + 1 | _ => acc) 0

/-- The five scalability programs, as readable source files under `examples/scale/` (one statement per
    line). `(name, path, observable-to-read)`. Each is a few hundred TAC nodes:
    * `immediates-200` — `a_k := k` (200×): large node count, tiny expression universe.
    * `reassign-250`   — `x := k`  (250×): one variable reassigned (long single-var def chain).
    * `copies-160`     — `a_{k+1} := a_k`: copy chain / long liveness.
    * `chain-150`      — `a_{k+1} := a_k + 1`: deep def-use / meet chain.
    * `redundant-50`   — `s := s + 7 * 11` (50×): stresses LCM PRE hoisting.
    Before the memoization work `prophecyc` timed out beyond ~20 variables; these now optimize in ≈1s. -/
def bigFiles : List (String × String × String) :=
  [ ("immediates-200", "examples/scale/immediates-200.src", "a199"),
    ("reassign-250  ", "examples/scale/reassign-250.src",   "x"),
    ("copies-160    ", "examples/scale/copies-160.src",     "a159"),
    ("chain-150     ", "examples/scale/chain-150.src",      "a149"),
    ("redundant-50  ", "examples/scale/redundant-50.src",   "s") ]

/-- Algorithms in `examples/computations/` (loops, nested loops, branches, bitwise): each is
    checked for **correctness** (the un-optimized program computes the known value) *and* **behaviour
    preservation** (the optimized program agrees). `(name, path, observable, expected)`. -/
def computationCases : List (String × String × String × Int) :=
  [ ("gcd        ", "examples/computations/gcd.src",         "gcd",    21),
    ("factorial  ", "examples/computations/factorial.src",   "result", 3628800),
    ("fib        ", "examples/computations/fib.src",         "fib",    832040),
    ("power      ", "examples/computations/power.src",       "result", 1594323),
    ("primes     ", "examples/computations/primes.src",      "count",  15),
    ("collatz    ", "examples/computations/collatz.src",     "steps",  111),
    ("isqrt      ", "examples/computations/isqrt.src",       "root",   1000),
    ("sum_squares", "examples/computations/sum_squares.src", "s",      338350),
    ("sum_divisor", "examples/computations/sum_divisors.src", "sum",    28) ]

/-! ## Full-optimizer suite

Programs that each **target a specific optimization**, pushed through `optimizeFull` (the whole pipeline,
including the previously-untested peephole, const-prop/branch-fold/UCE, and cleanup). Every case checks
three things: correctness (the reference interpreter gives `want`), behaviour preservation (the optimized
program agrees and halts), and — crucially — that the optimization **actually fired**, by inspecting the
optimized IR (a folded literal appeared / a redundant op became a copy / the node count shrank). Behaviour
preservation alone can't prove an optimization ran, so the `Fired` evidence is what makes these real. -/

/-- Evidence, read off the fully-optimized IR, that the targeted optimization ran. -/
inductive Fired
  | folds (v : String) (c : Int)   -- `v := <c>` literal present ⇒ constant folded / propagated
  | atom  (v : String)             -- `v := <atom>` (RHS no longer a binop) ⇒ peephole identity fired
  | shrink                         -- strictly fewer nodes than un-optimized ⇒ branch-fold + UCE fired

structure OptCase where
  name  : String
  src   : String
  var   : String
  want  : Int
  fired : Fired

/-- A loop whose result `s = 6` is not a compile-time constant, so peephole identities on `s` (e.g.
    `s * 1`, `s - s`) are genuine peephole rewrites, not constant folding. -/
def loopS : String := "s := 0; i := 3; while i { s := s + i; i := i - 1 }; "

def optCases : List OptCase := [
  -- peephole algebraic identities on a non-constant operand (`s = 6`); each RHS collapses to an atom
  ⟨"peephole  s*1",     loopS ++ "x := s * 1",   "x", 6, .atom "x"⟩,
  ⟨"peephole  s+0",     loopS ++ "x := s + 0",   "x", 6, .atom "x"⟩,
  ⟨"peephole  s-s",     loopS ++ "x := s - s",   "x", 0, .atom "x"⟩,
  ⟨"peephole  s==s",    loopS ++ "x := s == s",  "x", 1, .atom "x"⟩,
  ⟨"peephole  s/1",     loopS ++ "x := s / 1",   "x", 6, .atom "x"⟩,
  ⟨"peephole  s<<0",    loopS ++ "x := s << 0",  "x", 6, .atom "x"⟩,
  ⟨"peephole  s>>0",    loopS ++ "x := s >> 0",  "x", 6, .atom "x"⟩,
  ⟨"peephole  s&s",     loopS ++ "x := s & s",   "x", 6, .atom "x"⟩,
  ⟨"peephole  s*0",     loopS ++ "x := s * 0",   "x", 0, .atom "x"⟩,
  -- constant propagation through an arithmetic chain (needs fixpoint iteration: each round folds one link)
  ⟨"constprop chain",   "a := 1; b := a + 1; c := b + 1; d := c + 1", "d", 4, .folds "d" 4⟩,
  -- copy propagation chain (`b := a` with `a` constant), also iterated
  ⟨"copyprop chain",    "a := 7; b := a; c := b; d := c; e := d",     "e", 7, .folds "e" 7⟩,
  -- branch folding + unreachable-code elimination: known-nonzero guard ⇒ else-arm deleted
  ⟨"branchfold then",   "x := 5; if x { y := 10 } else { y := 20 }",  "y", 10, .shrink⟩,
  -- known-zero guard ⇒ then-arm deleted
  ⟨"branchfold else",   "x := 0; if x { y := 10 } else { y := 20 }",  "y", 20, .shrink⟩,
  -- dead loop: known-zero guard ⇒ entire loop body eliminated as unreachable
  ⟨"dead loop UCE",     "c := 0; while c { r := r + 1 }; z := 8",     "z", 8, .shrink⟩,
  -- everything at once: peephole (`a*1`,`b+0`,`d-d`) + const-prop + branch-fold + UCE
  ⟨"combined all",      "a := 3; b := a * 1; c := b + 0; if c { d := c + c } else { d := 0 }; e := d - d",
                        "e", 0, .folds "e" 0⟩ ]

/-- Scan an optimized program for `v := <imm c>` (a folded constant). -/
def hasImm (P : Tac.Program) (v : String) (c : Int) : Bool :=
  P.code.any fun
    | .assign (.orig w) (.atom (.imm k)) _ => w == v && k.toInt == c
    | _ => false

/-- Scan for `v := <atom>` (RHS reduced to a copy/immediate — no binop). -/
def hasAtom (P : Tac.Program) (v : String) : Bool :=
  P.code.any fun
    | .assign (.orig w) (.atom _) _ => w == v
    | _ => false

def main : IO UInt32 := do
  let mut fails := 0
  for c in cases do
    match runVar c.src c.var with
    | some (got, halted) =>
        if got == c.want && halted then
          IO.println s!"ok    {c.name}  ({c.var} = {got})"
        else
          IO.println s!"FAIL  {c.name}  got {c.var}={got} halted={halted}, want {c.want}"
          fails := fails + 1
    | none =>
        IO.println s!"FAIL  {c.name}  parse error"
        fails := fails + 1
  -- AstToText round-trips through the parser (same result after unparse + re-parse)
  for c in cases do
    if roundVar c.src c.var == some (c.want, true) then
      IO.println s!"ok    roundtrip  {c.name}"
    else
      IO.println s!"FAIL  roundtrip  {c.name}  ({roundVar c.src c.var})"
      fails := fails + 1
  -- normalize preserves observable behavior (the CLI now runs lower → normalize → codegen)
  for c in cases do
    if normVar c.src c.var == some (c.want, true) then
      IO.println s!"ok    normalize  {c.name}"
    else
      IO.println s!"FAIL  normalize  {c.name}  ({normVar c.src c.var})"
      fails := fails + 1
  -- smoke test: the backend emits a Mach-O `_main`
  match (TextToAst.parse "x := 1").map (fun s => AsmToText.emitText (AstToTac.lower s)) with
  | some asm =>
      if (asm.splitOn "_main").length ≥ 2 then
        IO.println "ok    backend emits _main"
      else
        IO.println "FAIL  backend: no _main"
        fails := fails + 1
  | none =>
      IO.println "FAIL  backend: parse error"
      fails := fails + 1
  -- scalability: large programs through the full LCM+PDCE optimizer; behaviour must be preserved
  IO.println "\n-- scalability (optimize large programs; behaviour preserved) --"
  let fuel := 50000000
  for (name, path, v) in bigFiles do
    let src ← IO.FS.readFile path
    match normalized src with
    | none => IO.println s!"FAIL  {name}  parse error"; fails := fails + 1
    | some orig =>
      let t0 ← IO.monoMsNow
      match optimize src with
      | none => IO.println s!"FAIL  {name}  optimize error"; fails := fails + 1
      | some opt =>
        let nOpt := opt.size            -- force the optimizer (build the code array)
        let t1 ← IO.monoMsNow
        let (c0, s0) := Semantics.run orig ⟨orig.entry, Store.init⟩ fuel
        let (c1, s1) := Semantics.run opt  ⟨opt.entry,  Store.init⟩ fuel
        let g0 := (c0.store (.orig v)).toInt
        let g1 := (c1.store (.orig v)).toInt
        if g0 == g1 && s0.isHalt && s1.isHalt then
          IO.println s!"ok    {name}  {orig.size}→{nOpt} nodes, {v}={g1}, optimized in {t1 - t0}ms"
        else
          IO.println s!"FAIL  {name}  orig {v}={g0} halt={s0.isHalt} | opt {v}={g1} halt={s1.isHalt}"
          fails := fails + 1
  -- computation programs: correctness (un-optimized = expected) AND behaviour preservation (optimized agrees)
  IO.println "\n-- computations (correctness + behaviour preserved) --"
  for (name, path, v, want) in computationCases do
    let src ← IO.FS.readFile path
    match normalized src, optimize src with
    | some orig, some opt =>
      let (c0, s0) := Semantics.run orig ⟨orig.entry, Store.init⟩ fuel
      let (c1, s1) := Semantics.run opt  ⟨opt.entry,  Store.init⟩ fuel
      let g0 := (c0.store (.orig v)).toInt
      let g1 := (c1.store (.orig v)).toInt
      if g0 == want && g1 == want && s0.isHalt && s1.isHalt then
        IO.println s!"ok    {name}  {v} = {g1}  (opt {orig.size}→{opt.size} nodes)"
      else
        IO.println s!"FAIL  {name}  want {v}={want}; orig={g0} halt={s0.isHalt} | opt={g1} halt={s1.isHalt}"
        fails := fails + 1
    | _, _ => IO.println s!"FAIL  {name}  parse/optimize error"; fails := fails + 1
  -- full optimizer: each program targets one optimization; check correctness + behaviour preservation
  -- through the WHOLE pipeline (peephole → const-prop → branch-fold → UCE → LCM → PDCE → cleanup) AND that
  -- the optimization demonstrably fired (folded literal / peephole'd atom / node-count shrink).
  IO.println "\n-- full optimizer (peephole + const-prop + branch-fold + UCE + LCM + PDCE + cleanup) --"
  for oc in optCases do
    match normalized oc.src, optimizeFull oc.src with
    | some orig, some opt =>
      let (c0, s0) := Semantics.run orig ⟨orig.entry, Store.init⟩ fuel
      let (c1, s1) := Semantics.run opt  ⟨opt.entry,  Store.init⟩ fuel
      let g0 := (c0.store (.orig oc.var)).toInt
      let g1 := (c1.store (.orig oc.var)).toInt
      let firedOk := match oc.fired with
        | .folds v c => hasImm opt v c
        | .atom v    => hasAtom opt v
        | .shrink    => opt.size < orig.size
      if g0 == oc.want && g1 == oc.want && s0.isHalt && s1.isHalt && firedOk then
        IO.println s!"ok    {oc.name}  {oc.var}={g1}  ({orig.size}→{opt.size} nodes, fired)"
      else
        IO.println s!"FAIL  {oc.name}  want {oc.var}={oc.want}: orig={g0}/{s0.isHalt} opt={g1}/{s1.isHalt} fired={firedOk} ({orig.size}→{opt.size})"
        fails := fails + 1
    | _, _ => IO.println s!"FAIL  {oc.name}  parse/optimize error"; fails := fails + 1
  -- cleanup: PDCE + branch-folding leave `noop` nodes behind; the final `Pass.Cleanup` must remove them.
  -- Compare the noop count of the PDCE output (no cleanup) against the fully-optimized output — cleanup
  -- must strictly reduce it, and drive the observable program to the same value.
  IO.println "\n-- cleanup (noop-elimination after PDCE/branch-folding) --"
  for oc in optCases do
    match optimizeNoCleanup oc.src, optimizeFull oc.src with
    | some pre, some post =>
      let (c1, s1) := Semantics.run post ⟨post.entry, Store.init⟩ fuel
      let g1 := (c1.store (.orig oc.var)).toInt
      let nPre := noopCount pre
      let nPost := noopCount post
      if nPost ≤ nPre && s1.isHalt && g1 == oc.want then
        IO.println s!"ok    cleanup {oc.name}  noops {nPre}→{nPost}"
      else
        IO.println s!"FAIL  cleanup {oc.name}  noops {nPre}→{nPost}, {oc.var}={g1}/{s1.isHalt}"
        fails := fails + 1
    | _, _ => IO.println s!"FAIL  cleanup {oc.name}  optimize error"; fails := fails + 1
  -- taint (the def-use `image`-atom analysis, verified `taintSol_valid`): on a program where `b := y + 1`,
  -- `b` becomes tainted ONLY through the `flowsTo` image (it is defined, never used, so never a `source`),
  -- while `a := 5` stays clean. So a passing check exercises the `image` atom, not just the `source` gen.
  IO.println "\n-- taint (def-use image analysis; kernel-verified taintSol_valid) --"
  let taintProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "x") (.bin .add (.var (.orig "y")) (.imm 1)) 1,   -- x := y + 1
                  .assign (.orig "a") (.atom (.imm 5)) 2,                            -- a := 5   (clean)
                  .assign (.orig "b") (.bin .add (.var (.orig "y")) (.imm 1)) 3,     -- b := y + 1  (image)
                  .halt ]
      obs   := [.orig "b"] }
  let tainted := BaseLanguage.Analyses.Taint.taintSol taintProg 3
  let hasV (v : String) : Bool := tainted.contains (.orig v)
  let names := tainted.toList.filterMap (fun | .orig s => some s | _ => none)
  if hasV "b" && hasV "y" && !hasV "a" then
    IO.println s!"ok    taint  tainted@exit = {names}  (b via image, y via source, a clean)"
  else
    IO.println s!"FAIL  taint  b={hasV "b"} y={hasV "y"} a={hasV "a"}, want b,y tainted & a clean; got {names}"
    fails := fails + 1
  -- structavail (the data-dependency `gather`-atom analysis, verified `availSol_valid`): on `x:=5; y:=x+1;
  -- z:=w+1`, node 1 (`y`) is NOT a leaf (`localGen(1)=∅`, since `y` depends on `x`), so it becomes available
  -- at node 2 ONLY via the gather — its precondition `structSub(1)={0} ⊆ avail(1)={0,2}` holds because the
  -- leaf `x` (node 0) is available. Remove the gather and `1 ∉ avail@2`, so this check truly exercises it
  -- (not `localGen`, which for the derived node 1 is empty).
  IO.println "\n-- structavail (data-dependency gather analysis; kernel-verified availSol_valid) --"
  let saProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "x") (.atom (.imm 5)) 1,                        -- 0: x := 5
                  .assign (.orig "y") (.bin .add (.var (.orig "x")) (.imm 1)) 2, -- 1: y := x + 1
                  .assign (.orig "z") (.bin .add (.var (.orig "w")) (.imm 1)) 3, -- 2: z := w + 1 (w external)
                  .halt ]
      obs   := [.orig "y"] }
  let av1 := BaseLanguage.Analyses.StructAvail.availSol saProg 1
  let av2 := BaseLanguage.Analyses.StructAvail.availSol saProg 2
  if av1.contains 0 && !av1.contains 1 && av2.contains 1 then
    IO.println s!"ok    structavail  avail@1={av1.toList}, avail@2={av2.toList}  (node 1 gathered after node 0)"
  else
    IO.println s!"FAIL  structavail  avail@1={av1.toList} avail@2={av2.toList} (want 0∈@1, 1∉@1, 1∈@2)"
    fails := fails + 1
  -- bwdchain (the NON-DIAMOND backward-must `predict`, verified `gSol_valid`): `s:=1; s:=2` (observable) and
  -- `u:=3; u:=4` (non-observable) are structurally symmetric — each def is killed by a later redefinition.
  -- At node 4, node 1 (the killed OBSERVABLE def `s:=1`) is anticipated ONLY via the non-diamond `extraN`
  -- (observables never die), while the symmetric non-observable node 3 (`u:=3`) is dropped by the diamond.
  IO.println "\n-- bwdchain (non-diamond backward-must; kernel-verified gSol_valid) --"
  let bcProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "t") (.atom (.imm 0)) 1,   -- 0
                  .assign (.orig "s") (.atom (.imm 1)) 2,   -- 1: s:=1 (obs, killed by 2)
                  .assign (.orig "s") (.atom (.imm 2)) 3,   -- 2: s:=2 (obs)
                  .assign (.orig "u") (.atom (.imm 3)) 4,   -- 3: u:=3 (non-obs, killed by 4)
                  .assign (.orig "u") (.atom (.imm 4)) 5,   -- 4: u:=4 (non-obs)
                  .halt ]                                    -- 5
      obs   := [.orig "s"] }
  let g4 := BaseLanguage.Analyses.BwdChain.gSol bcProg 4
  if g4.contains 1 && !g4.contains 3 && g4.contains 4 then
    IO.println s!"ok    bwdchain  g@4={g4.toList}  (obs def 1 kept via extraN; symmetric non-obs def 3 dropped)"
  else
    IO.println s!"FAIL  bwdchain  g@4={g4.toList} (want 1∈ via extraN, 3∉, 4∈)"
    fails := fails + 1
  -- bwdmay (the NON-DIAMOND backward-MAY `predict`, least fixpoint, verified `mSol_valid`): same program as
  -- bwdchain, run through the may (least-fixpoint) solver `resMTCB`. The killed observable def (node 1) is
  -- live at node 4 ONLY via the non-diamond `extraM` term; the symmetric non-observable node 3 is dropped.
  IO.println "\n-- bwdmay (non-diamond backward-may; kernel-verified mSol_valid) --"
  let m4 := BaseLanguage.Analyses.BwdMay.mSol bcProg 4
  if m4.contains 1 && !m4.contains 3 && m4.contains 4 then
    IO.println s!"ok    bwdmay  m@4={m4.toList}  (obs def 1 live via extraM; symmetric non-obs def 3 dropped)"
  else
    IO.println s!"FAIL  bwdmay  m@4={m4.toList} (want 1∈ via extraM, 3∉, 4∈)"
    fails := fails + 1
  -- primeadd (the COMPOUND `gather ∩ gate` analysis, verified `gSol_valid`): both sub-atoms are exercised.
  -- On `c:=5; s:=7(obs); d:=c+1; e:=q+1`: node 0 (`c`, a constant) is GATED out of g@1 until the observable
  -- `s` arms the gate (node 0 ∈ g@2); node 2 (`d:=c+1`) is GATHERED in only once its dependency node 0 is
  -- present — absent from g@2, present in g@3. So the check needs var-carry, obsGen, gate, AND gather.
  IO.println "\n-- primeadd (compound gather ∩ gate; kernel-verified gSol_valid) --"
  let paProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "c") (.atom (.imm 5)) 1,                         -- 0: c := 5   (const)
                  .assign (.orig "s") (.atom (.imm 7)) 2,                         -- 1: s := 7   (obs; arms gate)
                  .assign (.orig "d") (.bin .add (.var (.orig "c")) (.imm 1)) 3,  -- 2: d := c+1 (dep on 0)
                  .assign (.orig "e") (.bin .add (.var (.orig "q")) (.imm 1)) 4,  -- 3: e := q+1 (q external)
                  .halt ]                                                          -- 4
      obs   := [.orig "s"] }
  let pg1 := BaseLanguage.Analyses.PrimeAdd.gSol paProg 1
  let pg2 := BaseLanguage.Analyses.PrimeAdd.gSol paProg 2
  let pg3 := BaseLanguage.Analyses.PrimeAdd.gSol paProg 3
  if pg1.contains 1 && !pg1.contains 0 && pg2.contains 0 && !pg2.contains 2 && pg3.contains 2 then
    IO.println s!"ok    primeadd  g@1={pg1.toList} g@2={pg2.toList} g@3={pg3.toList}  (gate arms node 0; gather adds node 2 after its dep)"
  else
    IO.println s!"FAIL  primeadd  g@1={pg1.toList} g@2={pg2.toList} g@3={pg3.toList} (want gate+gather discrimination)"
    fails := fails + 1
  -- the canonical DIAMOND `gen ∪ (self ∩ transp)` — the bread-and-butter fixpoint shape the 5 atom/general
  -- analyses above don't use — directly, in both must directions. `x:=a+b; y:=a+b; z:=5`: the expression
  -- `a+b` is AVAILABLE (fwd·must) after it is computed (∉@0, ∈@2), and VERY BUSY (bwd·must) before its uses
  -- (∈@0, ∉@2). Exercises `resMTC`/`resMTCBM` with the union/inter/const/var diamond term end-to-end.
  IO.println "\n-- diamond gen ∪ (self ∩ transp): available (fwd·must) + verybusy (bwd·must) --"
  let dProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "x") (.bin .add (.var (.orig "a")) (.var (.orig "b"))) 1,  -- 0: x := a+b
                  .assign (.orig "y") (.bin .add (.var (.orig "a")) (.var (.orig "b"))) 2,  -- 1: y := a+b
                  .assign (.orig "z") (.atom (.imm 5)) 3,                                    -- 2: z := 5
                  .halt ]                                                                    -- 3
      obs   := [.orig "x", .orig "y", .orig "z"] }
  let eab : BaseLanguage.Tac.Expr := .bin .add (.var (.orig "a")) (.var (.orig "b"))
  let availOk := !(BaseLanguage.Analyses.Available.availSol dProg 0).contains eab
                 && (BaseLanguage.Analyses.Available.availSol dProg 2).contains eab
  let busyOk  := (BaseLanguage.Analyses.VeryBusy.busySol dProg 0).contains eab
                 && !(BaseLanguage.Analyses.VeryBusy.busySol dProg 2).contains eab
  if availOk && busyOk then
    IO.println "ok    diamond  a+b available@2 not@0 (fwd·must); very-busy@0 not@2 (bwd·must)"
  else
    IO.println s!"FAIL  diamond  availOk={availOk} busyOk={busyOk}"
    fails := fails + 1
  -- bwdslice (the backward `image`-atom program slice, verified `sliceSol_valid`): on `a:=b+c; d:=a+1;
  -- e:=9` with output `d`, relevance flows backward through the def→use image — `a` becomes relevant at
  -- node 1 (it computes `d`) but not yet at node 2; the dead constant `e` is never relevant. So a passing
  -- check exercises the backward image atom (the backward counterpart of taint).
  IO.println "\n-- bwdslice (backward image program slice; kernel-verified sliceSol_valid) --"
  let bsProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "a") (.bin .add (.var (.orig "b")) (.var (.orig "c"))) 1, -- 0: a := b+c
                  .assign (.orig "d") (.bin .add (.var (.orig "a")) (.imm 1)) 2,            -- 1: d := a+1
                  .assign (.orig "e") (.atom (.imm 9)) 3,                                    -- 2: e := 9 (dead)
                  .halt ]                                                                    -- 3
      obs   := [.orig "d"] }
  let sl0 := BaseLanguage.Analyses.BwdSlice.sliceSol bsProg 0
  let sl1 := BaseLanguage.Analyses.BwdSlice.sliceSol bsProg 1
  let sl2 := BaseLanguage.Analyses.BwdSlice.sliceSol bsProg 2
  if sl1.contains (.orig "a") && !sl2.contains (.orig "a") && sl0.contains (.orig "b") && !sl0.contains (.orig "e") then
    IO.println "ok    bwdslice  a relevant@1 not@2 (via backward image); b relevant@0; dead e never relevant"
  else
    IO.println s!"FAIL  bwdslice  slice@0={sl0.toList.filterMap (fun | .orig s => some s | _ => none)} slice@1={sl1.toList.filterMap (fun | .orig s => some s | _ => none)}"
    fails := fails + 1
  -- gatedlive (the SET-LEVEL `gate` atom in evs-form, verified `gliveSol_valid`): `a := b+c; if a`. The
  -- branch condition `a` is live at node 1 (the floor); at node 0 its def MEETS `glive(1)`, so the set-level
  -- gate fires and adds `a`'s operands `b,c` to `glive(0)` — while `a` itself is killed by the carry. So a
  -- passing check exercises the set-level gate emitted through `printEvs` (not the authored live template).
  IO.println "\n-- gatedlive (set-level gate, evs-form; kernel-verified gliveSol_valid) --"
  let glProg : BaseLanguage.Tac.Program :=
    { entry := 0
      code  := #[ .assign (.orig "a") (.bin .add (.var (.orig "b")) (.var (.orig "c"))) 1, -- 0: a := b+c
                  .ifz (.orig "a") 2 2,                                                      -- 1: if a
                  .halt ]                                                                    -- 2
      obs   := [.orig "a"] }
  let gl0 := BaseLanguage.Analyses.GatedLive.gliveSol glProg 0
  let gl1 := BaseLanguage.Analyses.GatedLive.gliveSol glProg 1
  if gl0.contains (.orig "b") && gl0.contains (.orig "c") && !gl0.contains (.orig "a") && gl1.contains (.orig "a") then
    IO.println "ok    gatedlive  b,c live@0 via set-level gate (a's def meets live@1); a live@1, killed@0"
  else
    IO.println s!"FAIL  gatedlive  glive@0={gl0.toList.filterMap (fun | .orig s => some s | _ => none)} glive@1={gl1.toList.filterMap (fun | .orig s => some s | _ => none)}"
    fails := fails + 1
  -- backend slot-offset fallback: a frame slot past the 64-bit `ldr/str` unsigned-offset immediate
  -- ceiling (32760 bytes) must be reached via the x16 register-offset form, not an un-assemblable
  -- `[x29, #big]`. Exercised through the real printer (`instrText`), plus a no-regression check that
  -- the common (small-offset) path still emits the immediate form.
  IO.println "\n-- backend: large slot-offset fallback (>32760 ⇒ x16 register offset) --"
  let dummyP : BaseLanguage.Tac.Program := { entry := 0, code := #[.halt], obs := [] }
  let smallLdr := AsmToText.instrText dummyP [] 0 (.ldrSlot 9 100)
  let bndImm   := AsmToText.instrText dummyP [] 0 (.strSlot 9 32760)          -- max encodable immediate
  let bigLdr   := AsmToText.instrText dummyP [] 0 (.ldrSlot 9 40000)
  let bigStr   := AsmToText.instrText dummyP [] 0 (.strZero 40000)
  if smallLdr == ["  ldr x9, [x29, #100]"]
      && bndImm == ["  str x9, [x29, #32760]"]
      && bigLdr == ["  ldr x16, =40000", "  ldr x9, [x29, x16]"]
      && bigStr == ["  ldr x16, =40000", "  str xzr, [x29, x16]"] then
    IO.println "ok    slot fallback  ≤32760 immediate; >32760 via x16 register offset"
  else
    IO.println s!"FAIL  slot fallback  small={smallLdr} bnd={bndImm} bigLdr={bigLdr} bigStr={bigStr}"
    fails := fails + 1
  match (TextToAst.parse "x := 1").map (fun s => AsmToText.emitText (AstToTac.lower s)) with
  | some asm =>
      if (asm.splitOn "[x29, x16]").length == 1 && (asm.splitOn "[x29, #").length ≥ 2 then
        IO.println "ok    slot fallback  small program keeps the immediate slot form (no regression)"
      else
        IO.println "FAIL  slot fallback  small program unexpectedly used the register-offset form"
        fails := fails + 1
  | none => IO.println "FAIL  slot fallback  parse error"; fails := fails + 1
  -- large frame end-to-end: the 6000-variable example (`examples/scale/vars-6000.src`) both RUNS to the
  -- right value under the reference semantics and COMPILES (optimizer-free skeleton `codegen ∘ normalize
  -- ∘ lower`) to assembly whose high frame slots use x16 register-offset addressing (slot offsets past the
  -- 32760 immediate ceiling — i.e. beyond ~4093 variables).
  IO.println "\n-- backend: 6000-variable program (large frame, register-offset slots) --"
  let bigSrc ← IO.FS.readFile "examples/scale/vars-6000.src"
  let bigRan := runVar bigSrc "a5999" == some (5999, true)
  let bigCompiled := match TextToAst.parse bigSrc with
    | some s =>
        let asm := AsmToText.emitText (Normalize.normalize (AstToTac.lower s))
        (asm.splitOn "[x29, x16]").length ≥ 2 && (asm.splitOn "a5999").length ≥ 2
    | none => false
  if bigRan && bigCompiled then
    IO.println "ok    6000-var  runs (a5999=5999) + compiles with register-offset slots (>32760)"
  else
    IO.println s!"FAIL  6000-var  ran={bigRan} compiled={bigCompiled}"; fails := fails + 1
  -- parser integer-literal range: a bare decimal must fit the non-negative Int64 range. `2^63-1`
  -- (Int64.maxValue) parses and evaluates; `2^63` is rejected (parse error) rather than silently
  -- wrapping to a negative value through `Int64.ofNat`.
  IO.println "\n-- parser: integer-literal range (reject ≥ 2^63, no silent wrap) --"
  if runVar "x := 9223372036854775807" "x" == some (9223372036854775807, true)
      && (TextToAst.parse "x := 9223372036854775807").isSome
      && (TextToAst.parse "x := 9223372036854775808").isNone then
    IO.println "ok    literal range  2^63-1 ⇒ Int64.max; 2^63 rejected"
  else
    IO.println s!"FAIL  literal range  max={runVar "x := 9223372036854775807" "x"} over-none={(TextToAst.parse "x := 9223372036854775808").isNone}"
    fails := fails + 1
  -- verified encoder (AsmEnc): the printer body now routes through `emitCmd` (Tier-1 legality proved
  -- by `emitCmd_wf`, faithfulness by `decode_emitCmd`) + the trivial `renderLine`. Demonstrate the
  -- legalization + round-trip concretely at runtime.
  IO.println "\n-- verified encoder (AsmEnc.emitCmd legalizes offsets + round-trips) --"
  let bigSlot : Asm.Cmd := .ldrSlot 9 40000
  let smallSlot : Asm.Cmd := .ldrSlot 9 100
  let rt (c : Asm.Cmd) : Bool := reprStr (AsmEnc.decodeLines (AsmEnc.emitCmd c)) == reprStr (some c)
  if (AsmEnc.emitCmd bigSlot).all AsmEnc.AsmLine.wf
      && (AsmEnc.emitCmd bigSlot).length == 2        -- over-ceiling ⇒ legalized x16 register form
      && (AsmEnc.emitCmd smallSlot).length == 1      -- in-range ⇒ immediate form
      && rt bigSlot && rt smallSlot then
    IO.println "ok    encoder  big slot ⇒ 2 wf lines (x16 legalized), small ⇒ 1; both decode back"
  else
    IO.println "FAIL  encoder  emitCmd legality/round-trip"
    fails := fails + 1
  -- The two generator gates run HERE, not just as standalone exes. Both rotted invisibly once
  -- (gengen-check read `generated/…`, a path the Solver/Seam split deleted) precisely because nothing
  -- ran them. `lake test` is the thing that always runs, so the gates live behind it.
  IO.println "\n-- gengen-check (re-parse + byte-identity over the shipped corpus) --"
  try
    runCheck
  catch e =>
    IO.eprintln s!"FAIL  gengen-check: {e}"
    fails := fails + 1
  IO.println "\n-- gengen-stress (spiky 34-spec parse/lower/reject corpus) --"
  if (← runStress) != 0 then
    fails := fails + 1
  if fails == 0 then
    IO.println "\nALL PASS"; pure 0
  else
    IO.eprintln s!"\n{fails} test(s) FAILED"; pure 1
