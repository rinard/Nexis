-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Select
import GenGeneral.Printer
import GenGeneral.Wf

/-!
# `GenGeneral.Emit` — the term-generic file emitter

Assembles the printers (`printTermDefs`/`printWf`/`printEvs`) into the full `Solve.lean` +
`ValidExtremal.lean`. The term/`Wf`/quadrant selection comes from the `AnalysisIR`, so every analysis flows
through *one* path — the emit logic has no per-analysis branch beyond the 6-quadrant/mode + bundle selection.

Covers all shapes: the four fixpoint quadrants, confluence (`tMeet`/`tJoin`), bundle mode (the memoized
`solve`), own-locals (authored `_sub`), `bwdMay·gate`, fwdEdge/mayEdge placements, and the `gather`/`image`
atoms. The **`<Name>` clause structure is emitted here too** (`emitClauses`, named after the ghost
variable): a diamond gets the readable role-named natural form; the gate/fwdEdge/mayEdge shapes their
readable clause forms; a doubly-clamped ghost the `MTCSpec*C`-mirroring form; confluence ghosts have no
clause structure (bridged as the generic `Transfer`). EVERY per-ghost predicate is generated —
no analysis authors its own (the node-local defs it reads are the only authored input).

Every emitted `_correct`/`_greatest`/`_valid` is kernel-checked and axiom-clean `[propext, Classical.choice,
Quot.sound]`; the emitted `.lean` is type-checked when the generated file is later built.
-/

namespace GenGeneral

/-! ## Name conventions (from the IR) -/

/-- The emitted namespace — by convention from the analysis name (`PDCE` ⇒ `BaseLanguage.Analyses.PDCE`). -/
def AnalysisIR.nsName (a : AnalysisIR) : String := s!"BaseLanguage.Analyses.{a.analysis}"

/-- The name of the clause structure the ValidExtremal bridges: the ghost variable's own name
    (`Sink`/`Live`/`Anticipated`/`Available`/…), for every ghost — the paper's "the name of this
    structure is the ghost variable name". -/
def AnalysisIR.structN (a : AnalysisIR) : String := a.name

/-- The output dir (`Solver/<dir>`, `Seam/<dir>`) — the analysis name lower-cased (`PDCE` ⇒ `pdce`). -/
def AnalysisIR.dir (a : AnalysisIR) : String := a.analysis.map Char.toLower

/-- Resolve a file-level `include X` to its (import lines, open-namespace). `Tac.Locals` is the shared base
    node-locals (a namespace whose module is `BaseLanguage.IR.Locals` + its `_sub`, opened). A lower-cased
    dotted path (`analyses.pdce.PdceDefs`) is an analysis's own defs MODULE: import it + `<path>Sub`,
    with no open (it lives in the analysis's own namespace, which the emit `namespace` already covers).
    Any other capitalised name is a namespace whose module path equals it (import + open). -/
def resolveInclude : String → (String × String)
  | "Tac.Locals" => ("import BaseLanguage.IR.Locals\nimport BaseLanguage.IR.LocalsSub\n", "BaseLanguage.Tac.Locals")
  | other =>
    if (other.toList.head?.map Char.isLower).getD false then
      (s!"import {other}\nimport {other}Sub\n", "")
    else
      (s!"import {other}\n", other)

/-- The `import` block contributed by an analysis's includes. -/
def includeImports (a : AnalysisIR) : String := String.join (a.includes.map (fun i => (resolveInclude i).1))
/-- The extra `open` namespaces contributed by an analysis's includes (space-prefixed; module-path includes
    open nothing). -/
def includeOpens (a : AnalysisIR) : String :=
  String.join (a.includes.map (fun i => match (resolveInclude i).2 with | "" => "" | ns => s!" {ns}"))

/-! ## Leaf/clamp accessors (bwdMay·gate + bundle floor) -/

/-- A node-family leaf's bare head name (`condVars`), for `<name> P` (a `Node → SetTy` argument). -/
def Leaf.headName : Leaf → String
  | .fam n _ _ => n
  | .bound n _ => n
  | .union a _ => a.headName
  | .sdiff a _ => a.headName
  | .empty     => ""
  | .univ n    => n

/-- The floor (lo-clamp) family name for a bwdMay ghost (`condVars`); "" if none. -/
def Clamp.floorName : Clamp → String
  | .lo l => l.headName
  | _     => ""

/-- The gate's singleton (kill) family name, for a bwdMay·gate transfer. -/
partial def gateKillName : Transfer → String
  | .gate s _  => s.headName
  | .union a b => let l := gateKillName a; if l != "" then l else gateKillName b
  | .inter a b => let l := gateKillName a; if l != "" then l else gateKillName b
  | .diffc a _ => gateKillName a
  | _          => ""

/-- The gate's result (gres) family name — the `⊆ self` RHS guarded by the gate (bwdMay·gate). -/
partial def gateResName : Transfer → String
  | .gate _ r  => r.headName
  | .union a b => let l := gateResName a; if l != "" then l else gateResName b
  | .inter a b => let l := gateResName a; if l != "" then l else gateResName b
  | .diffc a _ => gateResName a
  | _          => ""

/-- The seed's applied form. Every seed is uniformly `Program → SetTy` (uniform seeds — the `∅`
    constants take an ignored `P` too), so a named seed is always `<name> P`,
    matching every other program-indexed leaf (universe/family). -/
def seedApplied : Seed → String
  | .empty  => "∅"
  | .fam f  => s!"{f.name} P"

/-- The seed's short name (for the `<seed>_sub` lemma). -/
def seedShort : Seed → String
  | .empty  => ""
  | .fam f  => f.name

/-! ## Edge/confluence shape detection + accessors (lcm) -/

/-- fwdEdge: a fwdMust fixpoint whose term reads foreign ghosts as placement params (lcm `Postponable`). -/
def AnalysisIR.isFwdEdge (a : AnalysisIR) : Bool := a.quadrant == .fwdMust && !a.foreigns.isEmpty
/-- mayEdge: a bwdMay fixpoint with abstracted edge placements `latN`/`latE` (lcm `Used`). -/
def AnalysisIR.isMayEdge (a : AnalysisIR) : Bool := a.quadrant == .bwdMay && !a.edgeInsts.isEmpty

/-- `(<f>Sol P)` per foreign ghost, space-joined (a fwdEdge term/Wf/valid foreign argument list). -/
def foreignSolArgs (a : AnalysisIR) : String := " ".intercalate (a.foreigns.map (fun f => s!"({f}Sol P)"))
/-- `(<f>Sol_sub P wf)` per foreign ghost, space-joined (the fwdEdge Wf `_sub` hypotheses). -/
def foreignSubArgs (a : AnalysisIR) : String := " ".intercalate (a.foreigns.map (fun f => s!"({f}Sol_sub P wf)"))

/-- The `Transfer` order argument for a confluence quadrant (`<st>.Subset` meet / `<st>.Sup` join). -/
def confLe (st : String) : Quadrant → String
  | .meet => s!"{st}.Subset"
  | _     => s!"{st}.Sup"

/-- The `<c>Sol_sub` projection into `<c>_correct.1` by quadrant (the within-bound conjunct). -/
def boundProj : Quadrant → String
  | .bwdMust | .bwdMay => ".1.2.2.2"
  | .meet | .join      => ".1.2"
  | _                  => ".1.2.2"

/-- The mayEdge placement defs `<c>LatN`/`<c>LatE` + their `_sub` (the solved-value instantiations of the
    edge placements, threading each foreign's `<f>Sol`/`<f>Sol_sub`). Referenced by `<c>_correct`. -/
def mayEdgePlacements (a : AnalysisIR) : String :=
  let c := a.carried; let st := a.dom; let u := a.univ.name
  let nRef := (a.edgeInsts.lookup "latN").getD { name := "" }
  let eRef := (a.edgeInsts.lookup "latE").getD { name := "" }
  let sols (r : FamilyRef) : String := " ".intercalate (r.params.map (fun p => s!"({p}Sol P)"))
  let subs (r : FamilyRef) : String := " ".intercalate (r.params.map (fun p => s!"({p}Sol_sub P wf)"))
  s!"def {c}LatN (P : Program) : Node → {st} := {nRef.name} P {sols nRef}\n" ++
  s!"def {c}LatE (P : Program) : Node → Node → {st} := {eRef.name} P {sols eRef}\n" ++
  s!"theorem {c}LatN_sub (P : Program) (wf : WellFormed P) (n : Node) : ({c}LatN P n).Subset ({u} P) :=\n  {nRef.name}_sub P {sols nRef} {subs nRef} n\n" ++
  s!"theorem {c}LatE_sub (P : Program) (wf : WellFormed P) (i j : Node) : ({c}LatE P i j).Subset ({u} P) :=\n  {eRef.name}_sub P {sols eRef} {subs eRef} i j\n"

/-! ## Solve emission -/

/-- The `resMTC*`/`MTCSpec*` names for a fixpoint quadrant. -/
def solveTriple : Quadrant → Res (String × String)
  | .fwdMust => .ok ("resMTC",   "MTCSpec")
  | .fwdMay  => .ok ("resMTCMF", "MTCSpecMF")
  | .bwdMust => .ok ("resMTCBM", "MTCSpecBM")
  | .bwdMay  => .ok ("resMTCB",  "MTCSpecB")
  | q        => err {} s!"emit: {repr q} is a confluence quadrant, not a fixpoint solver (handled by emitConfluenceSolve)"

/-- The doubly-clamped `res*C`/`MTCSpec*C` names for a fixpoint quadrant (cap-the-transfer solvers). -/
def solveTripleC : Quadrant → Res (String × String)
  | .fwdMust => .ok ("resFMC", "MTCSpecC")
  | .fwdMay  => .ok ("resFmC", "MTCSpecMFC")
  | .bwdMust => .ok ("resBMC", "MTCSpecBMC")
  | .bwdMay  => .ok ("resBmC", "MTCSpecBC")
  | q        => err {} s!"emit: {repr q} is a confluence quadrant, not a doubly-clamped fixpoint solver"

/-- `.2`-direction of `<c>_correct` (`greatest` ⇒ `x ∈ h n, x ∈ Sol`; `least` ⇒ `x ∈ Sol, x ∈ h n`). -/
def isGreatest : Quadrant → Bool
  | .fwdMay | .bwdMay | .join => false
  | _ => true

/-- Ghost `a`'s validity predicate applied to `arg`, with foreign ghosts referenced as fields of `self`
    (`{self}.{foreign}`). Mirrors what `<c>Sol_valid`/`<c>_greatest`/`<c>_least` are stated over — one
    spelling per shape (clean fixpoint / confluence / fwdEdge / mayEdge) — so the uniform `Valid`/
    `Extremal` in `emitInterface` states each conjunct exactly as the per-ghost fact proves it. -/
def ghostPredApplied (a : AnalysisIR) (self arg : String) : String :=
  let sn := a.structN
  let sref := fun f => s!"{self}.{f}"
  if a.mode == .confluence then
    s!"Transfer {confLe a.dom a.quadrant} P {sref (a.foreigns.headD "")} {arg}"
  else if a.isFwdEdge then
    s!"{sn} P {" ".intercalate (a.foreigns.map sref)} {arg}"
  else if a.isMayEdge then
    let place := fun key =>
      match a.edgeInsts.lookup key with
      | some r => s!"({r.name} P {" ".intercalate (r.params.map sref)})"
      | none   => "_"
    s!"{sn} P {place "latN"} {place "latE"} {arg}"
  else
    s!"{sn} P {arg}"

/-- The `<c>Sol_sub` domain lemma (⊆ universe), emitted per ghost when the analysis threads foreigns
    downstream (confluence/edge kinds — lcm). Reads the within-bound conjunct of `<c>_correct.1`. -/
def emitSolSub (a : AnalysisIR) : String :=
  s!"theorem {a.carried}Sol_sub (P : Program) (wf : WellFormed P) (n : Node) : ({a.carried}Sol P n).Subset ({a.univ.name} P) :=\n  fun x hx => Std.HashSet.mem_toList.mp (({a.carried}_correct P wf){boundProj a.quadrant} n x hx)\n\n"

/-- The `Solve` rest for one confluence ghost (meet/join over a foreign; bundle mode). `<c>Sol` is the
    bundle projection; `<c>_correct` is `resMeet`/`resJoin_correct` over the **raw** bundle field
    `(solve P).<foreign>` (defeq to `decF (tMeet/tJoin) f_<foreign>`). -/
def emitConfluenceSolve (a : AnalysisIR) (needSub : Bool) : Res String := do
  let c := a.carried; let et := a.elem; let st := a.dom; let q := a.quadrant
  let f := a.foreigns.headD ""
  let field := s!"((solve P).{f})"
  let spec := if q == .meet then "MeetSpec" else "JoinSpec"
  let solver := q.solver
  let extDir := if q == .meet then s!"∀ σ, {spec} P (list{et} P) {field} σ → ∀ n, ∀ x ∈ σ n, x ∈ {c}Sol P n"
                else s!"∀ σ, {spec} P (list{et} P) {field} σ → ∀ n, ∀ x ∈ {c}Sol P n, x ∈ σ n"
  let solDef := s!"def {c}Sol (P : Program) : Node → {st} := decF{et} P (solve P).{c}\n"
  let correct := s!"theorem {c}_correct (P : Program) (wf : WellFormed P) :\n    {spec} P (list{et} P) {field} ({c}Sol P) ∧\n    {extDir} :=\n  {solver}_correct (univ := list{et} P) wf (list{et}_nodup P) {field}\n\n"
  pure (solDef ++ correct ++ (if needSub then emitSolSub a else ""))

/-- The `Solve` rest for a DOUBLY-clamped ghost (`res*C` cap-the-transfer): `Wf` + `<c>Sol` + `<c>_correct`,
    routed to the quadrant's `res*C_correct`. The floor/ceiling defs (`<c>Lo`/`<c>Hi`) come from
    `printTermDefs`. The band `lo ⊆ hi` and the two `_sub` domain facts are authored lemmas in the Defs
    module: `<lo>_sub`/`<hi>_sub` (⊆ universe) and `<lo>_sub_<hi>` (the band). In bundle mode (always on)
    `<c>Sol` is the memoized projection `decF<Et> P (solve P).<c>`; otherwise the direct `res<Q>C …` call. -/
def emitGhostSolveC (a : AnalysisIR) (bundleEt : String) : Res String := do
  let (solverC, specC) ← solveTripleC a.quadrant
  let c := a.carried; let et := a.elem; let st := a.dom
  let sd := seedApplied a.seed; let sdA := s!"({sd})"
  let loLeaf := (a.clamp.loLeaf?).getD .empty
  let hiLeaf := (a.clamp.hiLeaf?).getD .empty
  let loName := loLeaf.headName
  let hiName := hiLeaf.headName
  -- a lone forward clamp defaults its opposite bound to a sentinel (`∅` floor / universe ceiling); those
  -- carry no authored `_sub`/band lemma, so their `hlo`/`hhi`/`hlohi` proofs are emitted trivially.
  let loEmpty := match loLeaf with | .empty  => true | _ => false
  let hiUniv  := match hiLeaf with | .univ _ => true | _ => false
  let wf := printWf a
  let termAppl := s!"({c}T P)"
  let boundary := s!"({c}Lo P) ({c}Hi P) {sdA}"
  let specSig := s!"{specC} P (list{et} P) {termAppl} {boundary}"
  -- `<c>Sol` is the memoized projection `decF<Et> P (solve P).<c>` (defeq to `res<Q>C …`).
  let solDef := if bundleEt != "" then s!"def {c}Sol (P : Program) : Node → {st} := decF{bundleEt} P (solve P).{c}\n"
                else s!"def {c}Sol (P : Program) : Node → {st} := {solverC} P (list{et} P) {termAppl} {boundary}\n"
  let extDir := if isGreatest a.quadrant then s!"∀ h, {specSig} h → ∀ n, ∀ x ∈ h n, x ∈ {c}Sol P n"
                else s!"∀ h, {specSig} h → ∀ n, ∀ x ∈ {c}Sol P n, x ∈ h n"
  let hloP := if loEmpty then "(fun n x hx => absurd hx Std.HashSet.not_mem_empty)"
              else s!"(fun n x hx => Std.HashSet.mem_toList.mpr ({loName}_sub P n x hx))"
  let hhiP := if hiUniv then "(fun n x hx => Std.HashSet.mem_toList.mpr hx)"
              else s!"(fun n x hx => Std.HashSet.mem_toList.mpr ({hiName}_sub P n x hx))"
  -- band `lo ⊆ hi`: `∅ ⊆ hi` (absurd) / `lo ⊆ univ` (the lo `_sub`) / the authored `<lo>_sub_<hi>`.
  let hband := if loEmpty then "(fun n x hx => absurd hx Std.HashSet.not_mem_empty)"
               else if hiUniv then s!"(fun n x hx => {loName}_sub P n x hx)"
               else s!"({loName}_sub_{hiName} P)"
  let hsdP := match a.seed with
    | .empty => "(fun x hx => absurd hx Std.HashSet.not_mem_empty)"
    | .fam s => s!"(fun x hx => Std.HashSet.mem_toList.mpr ({s.name}_sub P x hx))"
  -- res*C_correct arg order (declaration order of the section vars): wf nodup Wf hlo hsd hhi hlohi(=band).
  let combArgs := s!"(lo := {c}Lo P) (hi := {c}Hi P) (sd := {sd}) wf (list{et}_nodup P) ({c}Wf P) {hloP} {hsdP} {hhiP} {hband}"
  let correct := s!"theorem {c}_correct (P : Program) (wf : WellFormed P) :\n    {specSig} ({c}Sol P) ∧\n    {extDir} :=\n  {solverC}_correct {combArgs}\n\n"
  pure (wf ++ solDef ++ correct)

/-- The `Solve` rest for one fixpoint ghost (`Wf` + [base: `<seed>_sub`] + [mayEdge: placement defs] +
    `<c>Sol` + `<c>_correct` + [`<c>Sol_sub`]), assuming its term defs (`printTermDefs`) precede it.
    `bundleEt = ""` ⇒ `<c>Sol := res<Q> … <boundary>`; a nonempty `bundleEt` ⇒ `<c>Sol := decF<Et> P
    (solve P).<c>` (the memoized bundle projection, defeq to `res<Q>`). Own analyses reference the authored
    `<fam>_sub`. The fwdEdge/mayEdge (lcm) variants thread foreign solutions / placement defs into the term
    and its `Wf`/`_correct`, but flow through the same quadrant selection — no per-analysis branch. -/
def emitGhostSolve (a : AnalysisIR) (needSub : Bool) (bundleEt : String) (siblings : List String) : Res String := do
  let q := a.quadrant
  -- a doubly-clamped ghost routes to the cap-the-transfer solver (`res*C`).
  if a.clamp.isBoth then return ← emitGhostSolveC a bundleEt
  -- confluence combines a FOREIGN ghost's bundle field `(solve P).<foreign>` (`tMeet`/`tJoin`), so that
  -- foreign must be a sibling in this bundle; a lone confluence ghost (foreign absent) is a located error
  -- (totality) — its `(solve P).<foreign>` would dangle.
  if a.mode == .confluence then
    if !a.foreigns.all siblings.contains then
      return ← (err {} s!"emit: confluence ghost {a.carried} reads foreign ghost {a.foreigns} not present in the analysis bundle")
    else return ← emitConfluenceSolve a needSub
  let (solver, spec) ← solveTriple q
  let c := a.carried; let et := a.elem; let st := a.dom
  let sd := seedApplied a.seed          -- `entrySeed P` / `∅`
  let sdA := s!"({sd})"                  -- parenthesized for splicing as a solver argument
  let seedS := seedShort a.seed
  let floor := a.clamp.floorName        -- bwdMay lo-clamp family (`condVars`) / mayEdge gres (`ue`)
  let fe := a.isFwdEdge; let me := a.isMayEdge
  let wf := printWf a
  let places := if me then mayEdgePlacements a else ""
  -- A named seed's `<seed>_sub` is authored in the seed's own module (`<mod>Sub`, imported via the include /
  -- own module — e.g. `liveSeed_sub`, `entrySeed_sub`); an empty `∅` seed needs none (the correctness
  -- combinator discharges it with `absurd _ not_mem_empty`). So the generator emits no seed `_sub` inline.
  let seedSub := ""
  -- the term application (`<c>T P …`) — edges thread foreign solutions / placement defs:
  let termAppl := if fe then s!"({c}T P {foreignSolArgs a})"
                  else if me then s!"({c}T P ({c}LatN P) ({c}LatE P))"
                  else s!"({c}T P)"
  -- the boundary args after the term in the `MTCSpec*` signature, by quadrant:
  let boundary := match q with
    | .bwdMust => s!"({c}Hi P) {sdA}"
    | .bwdMay  => if me then s!"({c}Lo P ({c}LatN P)) ∅" else s!"({floor} P) {sdA}"
    | _        => sdA
  let specSig := s!"{spec} P (list{et} P) {termAppl} {boundary}"
  let solRhs := if bundleEt != "" then s!"decF{bundleEt} P (solve P).{c}" else s!"{solver} P (list{et} P) {termAppl} {boundary}"  -- memoized projection
  let solDef := s!"def {c}Sol (P : Program) : Node → {st} := {solRhs}\n"
  let extDir := if isGreatest q then s!"∀ h, {specSig} h → ∀ n, ∀ x ∈ h n, x ∈ {c}Sol P n"
                else s!"∀ h, {specSig} h → ∀ n, ∀ x ∈ {c}Sol P n, x ∈ h n"
  -- the `<c>Wf` reference (edges thread foreign/placement `_sub`):
  let wfRef := if fe then s!"{c}Wf P {foreignSolArgs a} {foreignSubArgs a}"
               else if me then s!"{c}Wf P ({c}LatN P) ({c}LatE P) ({c}LatN_sub P wf) ({c}LatE_sub P wf)"
               else s!"{c}Wf P"
  let seedSubProof := match a.seed with
    | .empty  => "(fun x hx => absurd hx Std.HashSet.not_mem_empty)"
    | .fam _  => s!"(fun x hx => Std.HashSet.mem_toList.mpr ({seedS}_sub P x hx))"
  -- the `res<Q>_correct` combinator arguments by quadrant:
  let combArgs := match q with
    | .bwdMust => s!"(hi := {c}Hi P) (sd := {sd}) wf (list{et}_nodup P) ({wfRef}) {seedSubProof}"
    | .bwdMay  =>
      if me then s!"(lo := {c}Lo P ({c}LatN P)) (sd := ∅) wf (list{et}_nodup P)\n    ({wfRef})\n    (fun n x hx => Std.HashSet.mem_toList.mpr ({floor}_sub P n x ({st}.mem_sdiff.mp hx).1))\n    {seedSubProof}"
      else s!"(lo := {floor} P) (sd := {sd}) wf (list{et}_nodup P) ({wfRef})\n    (fun n x hx => Std.HashSet.mem_toList.mpr ({floor}_sub P n x hx))\n    {seedSubProof}"
    | _        => s!"wf (list{et}_nodup P) ({wfRef}) {seedSubProof}"
  let correct := s!"theorem {c}_correct (P : Program) (wf : WellFormed P) :\n    {specSig} ({c}Sol P) ∧\n    {extDir} :=\n  {solver}_correct {combArgs}\n\n"
  pure (wf ++ seedSub ++ places ++ solDef ++ correct ++ (if needSub then emitSolSub a else ""))

/-! ## Executable bundle (the memoized `solve`) -/

/-- The per-ghost `let arr_<c> … let f_<c> …` of the memoizing `solve` chain (one concrete `Array`
    fixpoint per ghost, then its `Node → BV` field closure). Confluence ghosts are a cheap `tMeet`/`tJoin`
    closure over the foreign's raw `f_<foreign>`; edge ghosts thread their foreigns as the shared `d_<f>`
    decodes bound upstream (eta-stability — see `emitBundle`). -/
def bundleGhostLet (a : AnalysisIR) : Res String := do
  let c := a.carried; let et := a.elem; let q := a.quadrant
  let sd := s!"({seedApplied a.seed})"
  let floor := a.clamp.floorName
  let topD := s!"(topV (width{et} P))"
  -- doubly-clamped ghost: memoize the cap-the-transfer solver (`solve<Q>C`, args `t lo hi sd`); out of
  -- range it reads the ceiling `hi` (must) / floor `lo` (may), matching `solve<Q>CFun` for defeq.
  if a.clamp.isBoth then
    let (solverC, elseC) ← match q with
      | .fwdMust => pure ("solveFMC", s!"({c}Hi P)")
      | .fwdMay  => pure ("solveFmC", s!"({c}Lo P)")
      | .bwdMust => pure ("solveBMC", s!"({c}Hi P)")
      | .bwdMay  => pure ("solveBmC", s!"({c}Lo P)")
      | q        => err {} s!"emit bundle: doubly-clamped quadrant {repr q} unexpected"
    return s!"  let arr_{c} := {solverC} P (list{et} P) ({c}T P) ({c}Lo P) ({c}Hi P) {sd}\n  let f_{c} : Node → BV{et} P := fun n => if n < P.size then gA (arr_{c}) n else encode (list{et} P) ({elseC} n)\n"
  if a.mode == .confluence then
    let comb := if q == .meet then "tMeet" else "tJoin"
    let f := a.foreigns.headD ""
    return s!"  let f_{c} : Node → BV{et} P := {comb} P (list{et} P) (f_{f})\n"
  match q with
  | .fwdMust =>
    let termAppl := if a.isFwdEdge then s!"{c}T P " ++ " ".intercalate (a.foreigns.map (fun f => s!"(d_{f})")) else s!"{c}T P"
    pure s!"  let arr_{c} := solveMTC P (list{et} P) ({termAppl}) {sd}\n  let f_{c} : Node → BV{et} P := fun n => (arr_{c})[n]?.getD {topD}\n"
  | .fwdMay  => pure s!"  let arr_{c} := solveMTCMF P (list{et} P) ({c}T P) {sd}\n  let f_{c} : Node → BV{et} P := fun n => if n < P.size then gA (arr_{c}) n else 0\n"
  | .bwdMust => pure s!"  let arr_{c} := solveMTCBM P (list{et} P) ({c}T P) ({c}Hi P) {sd}\n  let f_{c} : Node → BV{et} P := fun n => if n < P.size then gA (arr_{c}) n else encode (list{et} P) ({c}Hi P n)\n"
  | .bwdMay  =>
    if a.isMayEdge then
      let dplace (r : FamilyRef) : String := s!"{r.name} P " ++ " ".intercalate (r.params.map (fun p => s!"(d_{p})"))
      let ln := dplace ((a.edgeInsts.lookup "latN").getD { name := "" })
      let le := dplace ((a.edgeInsts.lookup "latE").getD { name := "" })
      pure s!"  let arr_{c} := solveMTCB P (list{et} P) ({c}T P ({ln}) ({le})) ({c}Lo P ({ln})) ∅\n  let f_{c} : Node → BV{et} P := fun n => if n < P.size then gA (arr_{c}) n else encode (list{et} P) ({c}Lo P ({ln}) n)\n"
    else pure s!"  let arr_{c} := solveMTCB P (list{et} P) ({c}T P) ({floor} P) {sd}\n  let f_{c} : Node → BV{et} P := fun n => if n < P.size then gA (arr_{c}) n else encode (list{et} P) (({floor} P) n)\n"
  | q        => err {} s!"emit bundle: quadrant {repr q} unexpected"

/-- The bundle infra (per-elemType BV decode) + the `<Bundle>` structure + the memoizing `solve`. Each
    ghost's `let`s are followed by `let d_<c> := decF<Et> P f_<c>` iff a downstream ghost reads `<c>` as a
    foreign (dep-DAG threading — the edge/confluence ghosts consume these). -/
def emitBundle (a : AnalysisIR) (irs : List AnalysisIR) : Res String := do
  let elemTys := (irs.map (·.elem)).eraseDups
  let bvInfra := String.join (elemTys.map (fun et =>
    let st := ((irs.find? (·.elem == et)).getD a).dom
    s!"def width{et} (P : Program) : Nat := (list{et} P).length\nabbrev BV{et} (P : Program) := BitVec (width{et} P)\ndef decode{et} (P : Program) (bv : BV{et} P) : {st} := decode (list{et} P) bv\n@[noinline] def decF{et} (P : Program) (f : Node → BV{et} P) : Node → {st} := fun n => decode{et} P (f n)\n\n"))
  let structDef := s!"structure {a.analysis}Bitvec (P : Program) where\n"
    ++ String.intercalate "\n" (irs.map (fun it => s!"  {it.carried} : Node → BV{it.elem} P")) ++ "\n\n"
  let lets ← (List.range irs.length).mapM (fun i => do
    let it := irs[i]!
    let base ← bundleGhostLet it
    let downstream := (irs.drop (i + 1)).foldl (fun acc x => acc ++ x.foreigns) []
    let dLet := if downstream.contains it.carried then s!"  let d_{it.carried} := decF{it.elem} P f_{it.carried}\n" else ""
    pure (base ++ dLet))
  let flds := String.intercalate ", " (irs.map (fun it => s!"{it.carried} := f_{it.carried}"))
  let solveDef := s!"def solve (P : Program) : {a.analysis}Bitvec P :=\n{String.join lets}  \{ {flds} }\n\n"
  pure ("/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/\n\n" ++ bvInfra ++ structDef ++ solveDef)

/-! ## The whole Solve file -/

/-- The whole `Solve.lean` for one analysis (all its ghosts share a namespace). Handles the four fixpoint
    quadrants (plus the doubly-clamped `res*C` variants), own-locals (the `_sub` import derived from the
    `include` directives), and bundle mode (always on — every solve, even a lone ghost, is memoized as a
    concrete `Array` in `solve` and projected per node). -/
def emitSolve (irs : List AnalysisIR) : Res String := do
  let a ← match irs.head? with
    | some a => pure a
    | none   => err {} "emit: empty analysis"
  -- Bundle mode is ALWAYS on: every analysis (even a single ghost) memoizes its fixpoint as one concrete
  -- `Array` bound once in `solve`, then projected per node — killing the per-node re-solve a direct
  -- `res<Q> … n` call incurs (its array sits under the `n` binder). Correctness is inherited unchanged:
  -- `decF<Et> P (solve P).<c>` is defeq to `res<Q> …`, so every `<c>_correct` still typechecks. (A
  -- multi-ghost analysis needs the SHARED `let`-chain of `solve` — per-ghost `def`-composition would
  -- recompute each foreign per dependency path, which compounds through the DAG; benchmarked, confirmed.)
  let bundleMode := true
  -- `needSub`: analyses that thread foreigns downstream (confluence/edge — lcm) emit `<c>Sol_sub` per ghost.
  let needSub := irs.any (fun it => it.mode == .confluence || it.isFwdEdge || it.isMayEdge)
  let hasConfl := irs.any (·.mode == .confluence)
  let ns := a.nsName
  -- All imports/opens are driven by the `.gsl` `include`s: `include Tac.Locals` (base, opened) and
  -- `include analyses.<dir>.<Name>Defs` (the analysis's own defs module + its `_sub`).
  let opens := "open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std" ++ includeOpens a
  -- confluence (`tMeet`/`tJoin`/`resMeet`/`resJoin`) is still bitvector-typed ⇒ reaches below the seam.
  let transferImp := if hasConfl then "import Solver.Impl.Transfer\n" else ""
  -- The BUNDLE path memoises at the bitvector representation (`solveMTC*`/`gA`/`encode`/`topV`), so it
  -- imports the impl directly. Plain analyses need only the seam (`import Solver` = Spec + Interface).
  let implImp := if bundleMode then "import Solver.Impl.Term\n" else ""
  let header := s!"-- Copyright (c) 2026 Martin Rinard\n-- GENERATED from {a.analysis}.gsl by `lake exe gen` — do not edit.\n{includeImports a}import Solver\n{implImp}{transferImp}/-! The `Solve` target ({irs.length} ghost(s)). -/\nnamespace {ns}\n{opens}\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  let elemTys := (irs.map (·.elem)).eraseDups
  let listDefs := String.join (elemTys.map (fun et =>
    let u := ((irs.find? (·.elem == et)).getD a).univ.name
    s!"def list{et} (P : Program) : List {et} := ({u} P).toList\ntheorem list{et}_nodup (P : Program) : (list{et} P).Nodup := ({u} P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)\n\n"))
  let terms := String.join (irs.map printTermDefs)
  let bundle ← if bundleMode then emitBundle a irs else pure ""
  let siblings := irs.map (·.carried)
  let rests ← irs.mapM (fun it => emitGhostSolve it needSub (if bundleMode then it.elem else "") siblings)
  pure (header ++ listDefs ++ terms ++ bundle ++ String.join rests ++ s!"end {ns}\n")

/-! ## ValidExtremal emission -/

/-! ## The evs-form clause printer (the emitted predicate's transfer RHS) -/

/-- The node arguments of a leaf read at the *actual* edge `(c.node, c'.node)` (vs the `Printer`'s
    lambda-binder `n`/`n'`): `src`⇒` c.node`, `tgt`⇒` c'.node`, `edge`⇒` c.node c'.node`, `whole`⇒none. -/
def cNodeOf : ReadAt → String
  | .src   => " c.node"
  | .tgt   => " c'.node"
  | .edge  => " c.node c'.node"
  | .whole => ""

/-- A leaf as a HashSet expression read at the concrete edge `(c.node, c'.node)` (evs-form; `wrap := true`
    since it appears as a bare argument). -/
def printLeafC : Leaf → String := printLeafWith cNodeOf "" true

/-- A gather `sub` leaf read at the edge with the element `z` trailing — `structSub P c.node z`,
    `(needs P c.node z).sdiff (base P c.node z)`. The gather sub is element-indexed (`α → HashSet α`), so a
    compound sub must apply each family to `z` (a bare `printLeafC` leaves `z` implicit, which composes only
    for a single family, not a `∪`/`∖`). -/
def printLeafCElem : Leaf → String := printLeafWith cNodeOf " z" true

/-- Print `evs(term, carried(<selfNode>))` as a HashSet expression — the transfer RHS of the emitted
    `<Name>` clause structure. **Defeq to the backend's `MTC.evs`** (`Solver/Spec.lean`): `∪`/`∩`/`∖` are the
    per-domain ops (defeq to `evs`'s `.filter` forms), gate is `if X.toList.any (…contains…) then res else
    ∅`, atoms are `imageS`/`gatherS` — so the clause⟺spec bridge is a definitional pass-through. `var`
    reads the incoming `carried(selfNode)` (`c.node` fwd / `c'.node` bwd); families read `c.node`. `st` is
    the domain (for the gate's `∅`). Adding a future `MTC` atom needs one case here + one in `printTransfer`. -/
partial def printEvs (carried selfNode st : String) : Transfer → String
  | .var        => s!"({carried} {selfNode})"
  | .const l    => printLeafC l
  | .union a b  => s!"(({printEvs carried selfNode st a}).union ({printEvs carried selfNode st b}))"
  -- `∩`/`∖` use `evs`'s exact `.filter` forms (NOT `.union`/`.inter`/`.sdiff`) — those are only defeq to
  -- `evs` when the left is `var` (the diamond); in a nested position (`gather ∩ gate`) the pass-through
  -- needs the literal `filter`.
  | .inter a b  => s!"(({printEvs carried selfNode st a}).filter (fun y => ({printEvs carried selfNode st b}).contains y))"
  | .diffc a l  => s!"(({printEvs carried selfNode st a}).filter (fun y => !({printLeafC l}).contains y))"
  | .gate s r   => s!"(if ({carried} {selfNode}).toList.any (fun w => ({printLeafC s}).contains w) then {printLeafC r} else (∅ : {st}))"
  | .image U R  => s!"(MTC.imageS ({printLeafC U}) ({R.name} P c.node) ({carried} {selfNode}))"
  | .gather U s => s!"(MTC.gatherS ({printLeafC U}) (fun z => {printLeafCElem s}) ({carried} {selfNode}))"

/-- The leftmost `.const (.fam name …)`'s family name (the "gen" leaf a bwdMust bridge references).
    **Total only on the diamond `gen ∪ (var ∩ transp)`** — callers guard with `isDiamond`. -/
partial def firstConstFam : Transfer → String
  | .const (.fam name _ _) => name
  | .const _        => ""
  | .var            => ""
  | .union a b      => let l := firstConstFam a; if l != "" then l else firstConstFam b
  | .inter a b      => let l := firstConstFam a; if l != "" then l else firstConstFam b
  | .diffc a _      => firstConstFam a
  | _               => ""   -- gate/image/gather: unreachable (callers guard with `isDiamond`, which has no atoms)

/-- The transp/kill family of a diamond term (`gen ∪ (var ∩ <transp>)`): the `.const` inside the `∩`. -/
partial def diamondTransp : Transfer → String
  | .union _ b => diamondTransp b
  | .inter _ b => firstConstFam b
  | _          => ""

/-- Is a transfer the canonical diamond `gen ∪ (var ∩ transp)`? A diamond gets the readable natural-form
    predicate/bridge (`flowBwdMust`); any other term gets the general evs-form + pass-through (`flowBwd`). -/
def isDiamond : Transfer → Bool
  | .union (.const _) (.inter .var (.const _)) => true
  | _                                          => false

/-- Does a transfer contain a `gate` atom? -/
partial def hasGate : Transfer → Bool
  | .gate _ _  => true
  | .union a b => hasGate a || hasGate b
  | .inter a b => hasGate a || hasGate b
  | .diffc a _ => hasGate a
  | _          => false

/-- Is a transfer EXACTLY the meets-form gate `gate ∪ (var ∖ kill)` (`live`/`gatedlive`/`pdce`)? Only this
    shape gets the readable meets-form predicate + `flowBwdMayGate` bridge (which hard-code `var ∖ kill` and
    a single gate). Any OTHER gated bwd·may term — a general carrier, multiple atoms — takes the general
    evs-form + `flowBwd` pass-through (`printEvs` renders the gate defeq to `MTC.evs`). -/
def isMeetsForm : Transfer → Bool
  | .union (.gate _ _) (.diffc .var _) => true
  | _                                  => false

/-- The clamp value read at `n` (the ceiling for bwd·must / floor for bwd·may): `gen ∪ kill`, `ceilN n`, … .
    A bwd ghost always carries the matching clamp; `.none` (unreachable for a bwd ghost) falls back to the
    universe — a benign trivial clamp, never a broken name. -/
def printClampAtN (a : AnalysisIR) : String :=
  match a.clamp with
  | .hi l => printLeafApplied l
  | .lo l => printLeafApplied l
  | .both _ hi => printLeafApplied hi        -- unused by the doubly-clamped path (separate emit); ceiling shown
  | .none => s!"{a.univ.name} P n"

/-- The DOUBLY-clamped `<Struct>` (mirrors the `MTCSpec*C` conjuncts field-by-field so the bridge is a
    trivial structural iso): `predict` (cap-the-transfer update, `evs`-form), `floor`, `check`, `seed`
    (relaxed boundary), `within`. Direction/extremal pick the update/seed spelling. -/
def emitClausesC (a : AnalysisIR) (q : Quadrant) : String :=
  let c := a.carried; let st := a.dom; let u := a.univ.name; let sn := a.structN
  -- the struct field spells the seed standalone (`x ∈ sd`), so the empty seed needs a type annotation
  -- (the spec side gets its type from the `MTCSpec*C` signature; here it would be an ambiguous `∅`).
  let sd := match a.seed with | .empty => s!"(∅ : {st})" | .fam f => s!"{f.name} P"
  let lo := s!"{c}Lo P"; let hi := s!"{c}Hi P"; let t := s!"{c}T P"
  let sig := s!"structure {sn} (P : Program) ({c} : Node → {st}) : Prop where\n"
  let flo := s!"  floor : ∀ n, ∀ x ∈ {lo} n, x ∈ {c} n\n"
  let chk := s!"  check : ∀ n, ∀ x ∈ {c} n, x ∈ {hi} n\n"
  let within := s!"  within : ∀ n, ({c} n).Subset ({u} P)\n\n"
  match q with
  | .fwdMust =>
    sig ++ s!"  predict : ∀ c c', Step P c c' → ∀ x ∈ {c} c'.node, x ∈ MTC.evs (c.node, c'.node) ({t}) ({c} c.node) ∨ x ∈ {lo} c'.node\n"
      ++ flo ++ chk ++ s!"  seed : ∀ x ∈ {c} P.entry, x ∈ {sd} ∨ x ∈ {lo} P.entry\n" ++ within
  | .fwdMay =>
    sig ++ s!"  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) ({t}) ({c} c.node), x ∈ {hi} c'.node → x ∈ {c} c'.node\n"
      ++ flo ++ chk ++ s!"  seed : ∀ x ∈ {sd}, x ∈ {hi} P.entry → x ∈ {c} P.entry\n" ++ within
  | .bwdMust =>
    sig ++ s!"  predict : ∀ c c', Step P c c' → ∀ x ∈ {c} c.node, x ∈ MTC.evs (c.node, c'.node) ({t}) ({c} c'.node) ∨ x ∈ {lo} c.node\n"
      ++ flo ++ chk ++ s!"  seed : ∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ {c} c.node, x ∈ {sd} ∨ x ∈ {lo} c.node\n" ++ within
  | .bwdMay =>
    sig ++ s!"  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) ({t}) ({c} c'.node), x ∈ {hi} c.node → x ∈ {c} c.node\n"
      ++ flo ++ chk ++ s!"  seed : ∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ {sd}, x ∈ {hi} c.node → x ∈ {c} c.node\n" ++ within
  | _ => ""

/-- The `<Name>` clause structure (named after the ghost variable, `a.name`), **emitted by GenGeneral
    itself**. A **diamond** term (`gen ∪ (var ∩ transp)`) gets the readable, role-named natural form
    (`gen`/`transp`/`ceiling` split); a **doubly-clamped** ghost gets the `MTCSpec*C`-mirroring form
    (`emitClausesC`); **any other** shape — atoms, non-diamond fixpoints — gets the general **evs-form**
    (`update`/`predict` is the spelled transfer, `printEvs`). Each is bridged by the same pass-through
    (`flowFwd`/`flowBwd`/`flowC`), since evs-form ⟺ `MTCSpec` definitionally. Emitted for every ghost;
    only confluence ghosts have no clause structure (bridged as the generic `Transfer`), so return `""`. -/
def emitClauses (a : AnalysisIR) : String :=
  if a.mode == .confluence then "" else
  if a.clamp.isBoth then emitClausesC a a.quadrant else
  let c := a.carried; let st := a.dom; let u := a.univ.name; let sn := a.structN
  let sd := seedApplied a.seed
  let sig := s!"structure {sn} (P : Program) ({c} : Node → {st}) : Prop where\n"
  let within := s!"  within : ∀ n, ({c} n).Subset ({u} P)\n\n"
  if a.isFwdEdge then
    -- fwdEdge (lcm `Postponable`): the predicate carries its foreign ghosts as params; the `update` RHS is
    -- the placement `∪ (self ∖ gres)` — spelled with `.sdiff` (defeq to the `evs` filter since the diff's
    -- left is `var`, per `printEvs`), the readable authored form. Bridged pass-through by `emitFwdEdgeVE`.
    let fparams := " ".intercalate a.foreigns
    let body := match a.transfer with
      | .union pl (.diffc .var gl) => s!"({printEvs c "c.node" st pl}).union (({c} c.node).sdiff ({printLeafC gl}))"
      | t                          => printEvs c "c.node" st t
    s!"structure {sn} (P : Program) ({fparams} : Node → {st}) ({c} : Node → {st}) : Prop where\n  update : ∀ c c', Step P c c' → ({c} c'.node).Subset ({body})\n  seed   : ({c} P.entry).Subset ({sd})\n" ++ within
  else if a.isMayEdge then
    -- mayEdge (lcm `Used`): the predicate carries the two edge placements (`latN`/`latE`) as params; the
    -- readable union-form `predict` + the `check` floor, bridged (with real steps) by `emitMayEdgeVE`.
    s!"structure {sn} (P : Program) (latN : Node → {st}) (latE : Node → Node → {st}) ({c} : Node → {st}) : Prop where\n  predict : ∀ c c', Step P c c' → ({c} c'.node).Subset (({c} c.node).union ((latN c'.node).union (latE c.node c'.node)))\n  check   : ∀ n, ({printClampAtN a}).Subset ({c} n)\n" ++ within
  else if isDiamond a.transfer && (a.quadrant == .fwdMust || a.quadrant == .fwdMay || a.quadrant == .bwdMust) then
    -- readable natural form (safe: `isDiamond` guarantees `firstConstFam`/`diamondTransp` find their leaves)
    let gen := firstConstFam a.transfer; let transp := diamondTransp a.transfer
    match a.quadrant with
    | .fwdMay => sig ++ s!"  update : ∀ c c', Step P c c' → (({gen} P c.node).union (({c} c.node).inter ({transp} P c.node))).Subset ({c} c'.node)\n  seed   : {st}.Subset ({sd}) ({c} P.entry)\n" ++ within
    | .bwdMust => sig ++ s!"  predict : ∀ c c', Step P c c' → (({c} c.node).sdiff ({gen} P c.node)).Subset ({c} c'.node)\n  check : ∀ n, ({c} n).Subset (({gen} P n).union ({transp} P n))\n  seed    : ∀ c, Final P c → ({c} c.node).Subset ({sd})\n" ++ within
    | _ => sig ++ s!"  update : ∀ c c', Step P c c' → ({c} c'.node).Subset (({gen} P c.node).union (({c} c.node).inter ({transp} P c.node)))\n  seed   : ({c} P.entry).Subset ({sd})\n" ++ within
  else
    -- general evs-form: the transfer clause is the spelled `evs(term, self)` (fwd reads `c.node`, bwd `c'.node`).
    let evsF := printEvs c "c.node" st a.transfer
    let evsB := printEvs c "c'.node" st a.transfer
    match a.quadrant with
    | .fwdMust => sig ++ s!"  update : ∀ c c', Step P c c' → ({c} c'.node).Subset ({evsF})\n  seed   : ({c} P.entry).Subset ({sd})\n" ++ within
    -- the evs is the ⊆-LHS here; use the qualified `{st}.Subset` (not dot-notation, which would resolve to
    -- the raw `Std.HashSet` when an `imageS`/`gatherS`/`filter` atom leads the union rather than the `{st}` abbrev).
    | .fwdMay  => sig ++ s!"  update : ∀ c c', Step P c c' → {st}.Subset ({evsF}) ({c} c'.node)\n  seed   : {st}.Subset ({sd}) ({c} P.entry)\n" ++ within
    | .bwdMust => sig ++ s!"  predict : ∀ c c', Step P c c' → ({c} c.node).Subset ({evsB})\n  check : ∀ n, ({c} n).Subset ({printClampAtN a})\n  seed    : ∀ c, Final P c → ({c} c.node).Subset ({sd})\n" ++ within
    | .bwdMay  =>
      if isMeetsForm a.transfer then
        -- meets-form gate (readable): the faint-liveness gate as a guarded `⟨∃ x ∈ kill, x ∈ self'⟩ → gres ⊆ self`
        -- clause. Field order (predict/floor/gate/seed/within) matches `flowBwdMayGate`.
        let kill := gateKillName a.transfer; let gres := gateResName a.transfer; let floor := a.clamp.floorName
        sig ++ s!"  predict : ∀ c c', Step P c c' → ({c} c'.node).Subset (({c} c.node).union ({kill} P c.node))\n  check   : ∀ n, ({floor} P n).Subset ({c} n)\n  gate    : ∀ c c', Step P c c' → (∃ x ∈ {kill} P c.node, x ∈ {c} c'.node) → ({gres} P c.node).Subset ({c} c.node)\n  seed    : ∀ c, Final P c → {st}.Subset ({sd}) ({c} c.node)\n" ++ within
      else
        sig ++ s!"  predict : ∀ c c', Step P c c' → {st}.Subset ({evsB}) ({c} c.node)\n  check   : ∀ n, ({printClampAtN a}).Subset ({c} n)\n  seed    : ∀ c, Final P c → {st}.Subset ({sd}) ({c} c.node)\n" ++ within
    | _ => ""

/-- The forward-quadrant clause⟺spec bridge (`fwdMust`/`fwdMay` share one body; `spec` differs). -/
def flowFwd (c st et spec sd sn : String) : String :=
  s!"theorem {c}_iff_flow (P : Program) (h : Node → {st}) :\n    {sn} P h ↔ {spec} P (list{et} P) ({c}T P) {sd} h := by\n  constructor\n  · intro hs\n    refine ⟨?_, ?_, ?_⟩\n    · intro c c' hstep x hx; exact hs.update c c' hstep x hx\n    · intro x hx; exact hs.seed x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)\n  · intro hf\n    refine ⟨?_, ?_, ?_⟩\n    · intro c c' hstep x hx; exact hf.1 c c' hstep x hx\n    · intro x hx; exact hf.2.1 x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mp (hf.2.2 n x hx)\n\n"

/-- The bwdMust clause⟺`MTCSpecBM` bridge (references the gen family + the clamp field). -/
def flowBwdMust (c st et sd sn genFam clamp : String) : String :=
  s!"theorem {c}_iff_flow (P : Program) (h : Node → {st}) :\n    {sn} P h ↔ MTCSpecBM P (list{et} P) ({c}T P) ({c}Hi P) {sd} h := by\n  constructor\n  · intro hs\n    refine ⟨?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx\n      by_cases hue : x ∈ {genFam} P c.node\n      · exact {st}.mem_union.mpr (Or.inl hue)\n      · refine {st}.mem_union.mpr (Or.inr ?_)\n        refine {st}.mem_inter.mpr ⟨hs.predict c c' hstep x ({st}.mem_sdiff.mpr ⟨hx, hue⟩), ?_⟩\n        rcases {st}.mem_union.mp (hs.{clamp} c.node x hx) with h1 | h2\n        · exact absurd h1 hue\n        · exact h2\n    · intro n x hx; exact hs.{clamp} n x hx\n    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)\n  · rintro ⟨hupd, hcheck, hseed, hbound⟩\n    refine ⟨?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx\n      obtain ⟨hxin, hxnue⟩ := {st}.mem_sdiff.mp hx\n      rcases {st}.mem_union.mp (hupd c c' hstep x hxin) with hue | hi\n      · exact absurd hue hxnue\n      · exact ({st}.mem_inter.mp hi).1\n    · intro n x hx; exact hcheck n x hx\n    · intro c hhalt x hx; exact hseed c hhalt x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)\n\n"

/-- `<c>Sol_valid` — shared by every fixpoint quadrant. -/
def solValid (c sn : String) : String :=
  s!"theorem {c}Sol_valid (P : Program) (wf : WellFormed P) : {sn} P ({c}Sol P) :=\n  ({c}_iff_flow P _).mpr ({c}_correct P wf).1\n"

/-- `<c>_greatest` (must) / `<c>_least` (may) + the two `#assert_clean_axioms` gates. -/
def extremalThm (c sn : String) (greatest : Bool) : String :=
  let nm := if greatest then "greatest" else "least"
  let concl := if greatest then s!"∀ n, (g n).Subset ({c}Sol P n)" else s!"∀ n, ({c}Sol P n).Subset (g n)"
  s!"theorem {c}_{nm} (P : Program) (wf : WellFormed P) :\n    ∀ g, {sn} P g → {concl} :=\n  fun g hg n x hx => ({c}_correct P wf).2 g (({c}_iff_flow P g).mp hg) n x hx\n\n#assert_clean_axioms {c}Sol_valid\n#assert_clean_axioms {c}_{nm}\n\n"

/-- The bwdMay·gate clause⟺`MTCSpecB` bridge in **meets-form** (the discriminant-free `.gsl` gate: the
    gate clause is `(∃ x ∈ <kill>, x ∈ h') → <gres> ⊆ h`). `floor` is the lo-clamp family (`condVars`),
    `kill` the gate singleton (`defVars`). The bwdMay·gate meets branch. -/
def flowBwdMayGate (c st et floor kill sdA sn : String) : String :=
  s!"theorem {c}_iff_flow (P : Program) (h : Node → {st}) :\n    {sn} P h ↔ MTCSpecB P (list{et} P) ({c}T P) ({floor} P) {sdA} h := by\n  constructor\n  · intro hl\n    refine ⟨?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx\n      rcases {st}.mem_union.mp hx with hg | hdf\n      · simp only [MTC.evs] at hg\n        by_cases hguard : (h c'.node).toList.any (fun y => ({kill} P c.node).contains y) = true\n        · rw [if_pos hguard] at hg\n          obtain ⟨y, hyl, hyc⟩ := List.any_eq_true.mp hguard\n          exact hl.gate c c' hstep ⟨y, Std.HashSet.contains_iff_mem.mp hyc, Std.HashSet.mem_toList.mp hyl⟩ x hg\n        · rw [if_neg hguard] at hg; simp [{st}.empty] at hg\n      · simp only [MTC.evs] at hdf\n        rw [Analysis.SetOps.mem_filter'] at hdf\n        obtain ⟨hxin, hxnd⟩ := hdf\n        rcases {st}.mem_union.mp (hl.predict c c' hstep x hxin) with hh | hd\n        · exact hh\n        · have hc : ({kill} P c.node).contains x = true := Std.HashSet.contains_iff_mem.mpr hd\n          rw [hc] at hxnd; simp at hxnd\n    · intro n x hx; exact hl.check n x hx\n    · intro c hhalt x hx; exact hl.seed c hhalt x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hl.within n x hx)\n  · rintro ⟨hupd, hcheck, hseed, hbound⟩\n    refine ⟨?_, ?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx\n      by_cases hxd : x ∈ {kill} P c.node\n      · exact {st}.mem_union.mpr (Or.inr hxd)\n      · refine {st}.mem_union.mpr (Or.inl (hupd c c' hstep x ?_))\n        refine {st}.mem_union.mpr (Or.inr ?_)\n        show x ∈ (h c'.node).filter _\n        rw [Analysis.SetOps.mem_filter']\n        refine ⟨hx, ?_⟩\n        cases hc : ({kill} P c.node).contains x with\n        | false => rfl\n        | true => exact absurd (Std.HashSet.contains_iff_mem.mp hc) hxd\n    · intro n x hx; exact hcheck n x hx\n    · intro c c' hstep hmeets x hx\n      apply hupd c c' hstep x\n      refine {st}.mem_union.mpr (Or.inl ?_)\n      obtain ⟨w, hwdef, hwlive⟩ := hmeets\n      have hguard : (h c'.node).toList.any (fun y => ({kill} P c.node).contains y) = true :=\n        List.any_eq_true.mpr ⟨w, Std.HashSet.mem_toList.mpr hwlive, Std.HashSet.contains_iff_mem.mpr hwdef⟩\n      simp only [MTC.evs]; rw [if_pos hguard]; exact hx\n    · intro c hf x hx; exact hseed c hf x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)\n\n"

/-- The confluence (meet/join) clause⟺spec bridge + valid + extremal (bundle mode). The interface is the
    raw `Transfer <st>.Subset`/`<st>.Sup P <foreign>Sol <c>Sol` schema; `<c>_iff_spec` bridges the raw
    bitvec field `(solve P).<foreign>`. -/
def emitConfluenceVE (a : AnalysisIR) : String :=
  let c := a.carried; let et := a.elem; let st := a.dom; let q := a.quadrant
  let f := a.foreigns.headD ""
  let le := confLe st q                       -- `Assignments.Subset` / `Assignments.Sup`
  let spec := if q == .meet then "MeetSpec" else "JoinSpec"
  let field := s!"((solve P).{f})"
  let iffSpec := s!"theorem {c}_iff_spec (P : Program) (X : Node → BV{et} P) (τ : Node → {st}) :\n    Transfer {le} P (decF{et} P X) τ ↔ {spec} P (list{et} P) X τ := by\n  constructor\n  · intro ht\n    exact ⟨fun c c' hs x hx => ht.predict c c' hs x hx,\n           fun n x hx => Std.HashSet.mem_toList.mpr (ht.within n x hx)⟩\n  · rintro ⟨htr, hb⟩\n    exact ⟨fun c c' hs x hx => htr c c' hs x hx,\n           fun n x hx => Std.HashSet.mem_toList.mp (hb n x hx)⟩\n"
  let valid := s!"theorem {c}Sol_valid (P : Program) (wf : WellFormed P) : Transfer {le} P ({f}Sol P) ({c}Sol P) :=\n  ({c}_iff_spec P {field} _).mpr ({c}_correct P wf).1\n"
  let (nm, concl) := if q == .meet then ("greatest", s!"(g n).Subset ({c}Sol P n)") else ("least", s!"({c}Sol P n).Subset (g n)")
  let ext := s!"theorem {c}_{nm} (P : Program) (wf : WellFormed P) :\n    ∀ g, Transfer {le} P ({f}Sol P) g → ∀ n, {concl} :=\n  fun g hg n x hx => ({c}_correct P wf).2 g (({c}_iff_spec P {field} g).mp hg) n x hx\n\n#assert_clean_axioms {c}Sol_valid\n#assert_clean_axioms {c}_{nm}\n\n"
  iffSpec ++ valid ++ ext

/-- The fwdEdge clause⟺`MTCSpec` bridge + valid + greatest (lcm `Postponable`). The predicate carries the
    foreign ghosts as parameters (`<sn> P <foreigns> h`), so the bridge is `<c>_toSpec`/`<c>_ofSpec`. -/
def emitFwdEdgeVE (a : AnalysisIR) : String :=
  let c := a.carried; let et := a.elem; let st := a.dom; let sn := a.structN
  let sdA := s!"({seedApplied a.seed})"
  let decl := " ".intercalate a.foreigns
  let sols := foreignSolArgs a
  let unders := " ".intercalate (a.foreigns.map (fun _ => "_")) ++ " _"
  s!"theorem {c}_toSpec (P : Program) ({decl} h : Node → {st}) (hs : {sn} P {decl} h) :\n    MTCSpec P (list{et} P) ({c}T P {decl}) {sdA} h :=\n  ⟨fun c c' hstep x hx => hs.update c c' hstep x hx, fun x hx => hs.seed x hx,\n   fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩\n" ++
  s!"theorem {c}_ofSpec (P : Program) ({decl} h : Node → {st}) (hf : MTCSpec P (list{et} P) ({c}T P {decl}) {sdA} h) : {sn} P {decl} h :=\n  ⟨fun c c' hstep x hx => hf.1 c c' hstep x hx, fun x hx => hf.2.1 x hx,\n   fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2 n x hx)⟩\n" ++
  s!"theorem {c}Sol_valid (P : Program) (wf : WellFormed P) : {sn} P {sols} ({c}Sol P) :=\n  {c}_ofSpec P {unders} ({c}_correct P wf).1\n" ++
  s!"theorem {c}_greatest (P : Program) (wf : WellFormed P) :\n    ∀ g, {sn} P {sols} g → ∀ n, (g n).Subset ({c}Sol P n) :=\n  fun g hg n x hx => ({c}_correct P wf).2 g ({c}_toSpec P {unders} hg) n x hx\n\n#assert_clean_axioms {c}Sol_valid\n#assert_clean_axioms {c}_greatest\n\n"

/-- The mayEdge clause⟺`MTCSpecB` bridge + valid + least (lcm `Used`). The predicate carries the two edge
    placements (`<sn> P latN latE h`); `clamp` is the floor field (`check`). The mayEdge floor branch. -/
def emitMayEdgeVE (a : AnalysisIR) (clamp : String) : String :=
  let c := a.carried; let et := a.elem; let st := a.dom; let sn := a.structN
  s!"theorem {c}_toSpec (P : Program) (latN : Node → {st}) (latE : Node → Node → {st}) (h : Node → {st}) (hs : {sn} P latN latE h) : MTCSpecB P (list{et} P) ({c}T P latN latE) ({c}Lo P latN) ∅ h := by\n  refine ⟨?_, ?_, ?_, ?_⟩\n  · intro c c' hstep x hx\n    rw [show MTC.evs (c.node, c'.node) ({c}T P latN latE) (h c'.node)\n          = (h c'.node).filter (fun y => !((latN c'.node).union (latE c.node c'.node)).contains y) from rfl] at hx\n    rw [SetOps.mem_filter'] at hx\n    obtain ⟨hxin, hxnk⟩ := hx\n    rcases {st}.mem_union.mp (hs.predict c c' hstep x hxin) with hu | hk\n    · exact hu\n    · exfalso\n      have : ((latN c'.node).union (latE c.node c'.node)).contains x = true := Std.HashSet.contains_iff_mem.mpr hk\n      rw [this] at hxnk; simp at hxnk\n  · intro n x hx; exact hs.{clamp} n x hx\n  · intro c hhalt x hx; exact absurd hx Std.HashSet.not_mem_empty\n  · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)\n" ++
  s!"theorem {c}_ofSpec (P : Program) (latN : Node → {st}) (latE : Node → Node → {st}) (h : Node → {st}) (hf : MTCSpecB P (list{et} P) ({c}T P latN latE) ({c}Lo P latN) ∅ h) : {sn} P latN latE h := by\n  obtain ⟨hupd, hcheck, hseed, hbound⟩ := hf\n  refine ⟨?_, ?_, ?_⟩\n  · intro c c' hstep x hx\n    by_cases hk : x ∈ (latN c'.node).union (latE c.node c'.node)\n    · exact {st}.mem_union.mpr (Or.inr hk)\n    · refine {st}.mem_union.mpr (Or.inl (hupd c c' hstep x ?_))\n      rw [show MTC.evs (c.node, c'.node) ({c}T P latN latE) (h c'.node)\n            = (h c'.node).filter (fun y => !((latN c'.node).union (latE c.node c'.node)).contains y) from rfl]\n      rw [SetOps.mem_filter']\n      refine ⟨hx, ?_⟩\n      cases hc : ((latN c'.node).union (latE c.node c'.node)).contains x with\n      | false => rfl\n      | true => exact absurd (Std.HashSet.contains_iff_mem.mp hc) hk\n  · intro n x hx; exact hcheck n x hx\n  · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)\n" ++
  s!"theorem {c}Sol_valid (P : Program) (wf : WellFormed P) : {sn} P ({c}LatN P) ({c}LatE P) ({c}Sol P) :=\n  {c}_ofSpec P _ _ _ ({c}_correct P wf).1\n" ++
  s!"theorem {c}_least (P : Program) (wf : WellFormed P) :\n    ∀ g, {sn} P ({c}LatN P) ({c}LatE P) g → ∀ n, ({c}Sol P n).Subset (g n) :=\n  fun g hg n x hx => ({c}_correct P wf).2 g ({c}_toSpec P _ _ _ hg) n x hx\n\n#assert_clean_axioms {c}Sol_valid\n#assert_clean_axioms {c}_least\n\n"

/-- The GENERAL backward clause⟺spec bridge (bwd·must / bwd·may): a **pass-through** — the authored
    predicate states `predict` directly as `evs(t, self') [⊇|⊆] self` (the spelled-out transfer), so no
    unfolding is needed (the backward analogue of `flowFwd`). `spec`/`clampArg`/`clampField` differ by
    must (`MTCSpecBM`/`ceiling`) vs may (`MTCSpecB`/`floor`); the seed is the halt seed. -/
def flowBwd (c st et sn spec clampArg clampField sdA : String) : String :=
  s!"theorem {c}_iff_flow (P : Program) (h : Node → {st}) :\n    {sn} P h ↔ {spec} P (list{et} P) ({c}T P) {clampArg} {sdA} h := by\n  constructor\n  · intro hs\n    refine ⟨?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx; exact hs.predict c c' hstep x hx\n    · intro n x hx; exact hs.{clampField} n x hx\n    · intro c hhalt x hx; exact hs.seed ⟨c.node, c.store⟩ (by exact hhalt) x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)\n  · rintro ⟨hp, hcl, hseed, hbound⟩\n    refine ⟨?_, ?_, ?_, ?_⟩\n    · intro c c' hstep x hx; exact hp c c' hstep x hx\n    · intro n x hx; exact hcl n x hx\n    · intro c hhalt x hx; exact hseed c hhalt x hx\n    · intro n x hx; exact Std.HashSet.mem_toList.mp (hbound n x hx)\n\n"

/-- The DOUBLY-clamped clause⟺`MTCSpec*C` bridge — a **trivial structural iso** (the `<Struct>` fields are
    the spec conjuncts verbatim; only `within` needs the `mem_toList` conversion). Quadrant-agnostic: field
    order `predict/floor/check/seed/within` matches the `MTCSpec*C` conjunct order for every quadrant. -/
def flowC (c st et sn specC sd : String) : String :=
  s!"theorem {c}_iff_flow (P : Program) (h : Node → {st}) :\n    {sn} P h ↔ {specC} P (list{et} P) ({c}T P) ({c}Lo P) ({c}Hi P) {sd} h := by\n  constructor\n  · intro hs\n    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩\n  · intro hf\n    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩\n\n"

/-- The `ValidExtremal` body for one ghost (bridge + valid + extremal). -/
def emitGhostVE (a : AnalysisIR) (q : Quadrant) : Res String := do
  let c := a.carried; let et := a.elem; let st := a.dom
  let sdA := s!"({seedApplied a.seed})"   -- parenthesized seed (`(entrySeed P)`) for the MTCSpec signature
  let sn := a.structN
  let clamp := "check"
  if a.mode == .confluence then return emitConfluenceVE a
  if a.clamp.isBoth then
    let (_, specC) ← solveTripleC q
    return (flowC c st et sn specC sdA ++ solValid c sn ++ extremalThm c sn (isGreatest q))
  if a.isFwdEdge then return emitFwdEdgeVE a
  if a.isMayEdge then return emitMayEdgeVE a clamp
  let flow ← match q with
    | .fwdMust => pure (flowFwd c st et "MTCSpec" sdA sn)
    | .fwdMay  => pure (flowFwd c st et "MTCSpecMF" sdA sn)
    | .bwdMust =>
      -- diamond ⇒ natural-form bridge; a general backward term ⇒ pass-through (evs-form predicate).
      if isDiamond a.transfer then pure (flowBwdMust c st et sdA sn (firstConstFam a.transfer) clamp)
      else pure (flowBwd c st et sn "MTCSpecBM" s!"({c}Hi P)" clamp sdA)
    | .bwdMay  =>
      -- An AUTHORED meets-form gate predicate (live/lcm) ⇒ the meets-form gate bridge. An EMITTED evs-form
      -- predicate ⇒ the pass-through, even with a gate: the gate is spelled inside the evs (the `if … then
      -- res else ∅`, defeq to `MTC.evs`), so no unfolding is needed (stress `DoubleAtom`, shipped `gatedlive`).
      if isMeetsForm a.transfer then pure (flowBwdMayGate c st et a.clamp.floorName (gateKillName a.transfer) sdA sn)
      else pure (flowBwd c st et sn "MTCSpecB" s!"({a.clamp.floorName} P)" "check" sdA)
    | q        => err {} s!"emit VE: {repr q} is a confluence quadrant (handled earlier by emitConfluenceVE)"
  pure (flow ++ solValid c sn ++ extremalThm c sn (isGreatest q))

/-- The uniform analysis interface: the result bundle `<A>Result` + `<A>Result.Valid` +
    `<A>Result.Extremal` + `<A>Solve` + its two proofs. Emitted for a multi-ghost analysis (≥2 ghosts —
    the only case where bundling distinct ghost solutions into one result is meaningful). Purely additive:
    references each ghost's already-emitted validity predicate (`ghostPredApplied`) and its
    `<c>Sol_valid`/`<c>_greatest`/`<c>_least` facts. No per-analysis branch — driven off ghost shape. -/
def emitInterface (irs : List AnalysisIR) : String :=
  match irs.head? with
  | none => ""
  | some a0 =>
    if a0.analysis == "" || irs.length < 2 then "" else
    let aN := a0.analysis
    let R := s!"{aN}Result"
    let fields := String.join (irs.map (fun a => s!"  {a.carried} : Node → {a.dom}\n"))
    let validConj := " ∧ ".intercalate (irs.map (fun a => s!"({ghostPredApplied a "S" s!"S.{a.carried}"})"))
    let extConj := " ∧ ".intercalate (irs.map (fun a =>
      let d := if isGreatest a.quadrant then s!"(g n).Subset (S.{a.carried} n)" else s!"(S.{a.carried} n).Subset (g n)"
      s!"(∀ g, {ghostPredApplied a "S" "g"} → ∀ n, {d})"))
    let solFields := String.join (irs.map (fun a => s!"  {a.carried} := {a.carried}Sol P\n"))
    let vArgs := ", ".intercalate (irs.map (fun a => s!"{a.carried}Sol_valid P wf"))
    let eArgs := ", ".intercalate (irs.map (fun a => s!"{a.carried}_{if isGreatest a.quadrant then "greatest" else "least"} P wf"))
    s!"/-! ## The uniform analysis interface: `{R}` + `Valid`/`Extremal` + `{aN}Solve`. -/\n\n" ++
    s!"structure {R} (P : Program) where\n{fields}\n" ++
    s!"def {R}.Valid (P : Program) (S : {R} P) : Prop :=\n  {validConj}\n\n" ++
    s!"def {R}.Extremal (P : Program) (S : {R} P) : Prop :=\n  {extConj}\n\n" ++
    s!"def {aN}Solve (P : Program) (wf : WellFormed P) : {R} P where\n{solFields}\n" ++
    s!"theorem {aN}Solve_valid (P : Program) (wf : WellFormed P) : ({aN}Solve P wf).Valid P :=\n  ⟨{vArgs}⟩\n\n" ++
    s!"theorem {aN}Solve_extremal (P : Program) (wf : WellFormed P) : ({aN}Solve P wf).Extremal P :=\n  ⟨{eArgs}⟩\n\n" ++
    s!"#assert_clean_axioms {aN}Solve_valid\n#assert_clean_axioms {aN}Solve_extremal\n\n"

/-! ## Augmented semantics (Preservation + Progress): per-ghost `R` + `Drives` + framework instances.

Emits `Seam/<dir>/Augmented.lean`. For each ghost we package its generated `Step`-quantified validity
fields (the ones over `Step P c c'` in `ValidExtremal.lean`) as the augmented step's per-step relation
`<c>R` — the ghost's own value abstracted to `π`/`π'`, foreign ghosts read by a step field instantiated
to their solved values `<f>Sol`, and (for a prophecy/backward ghost) its node-local `check`/`floor` clause
folded at the source as the prophecy precondition. `Drives` is then the analysis's own validity, and
`preservation`/`progress`/`bisim` are the generic §2 framework instances (`Analysis.Augmented`). -/

/-- A leaf as a HashSet expression in the Augmented `R` body: like `printLeafC`, but placement `.fam`
    params are instantiated to their solved ghosts `(<p>Sol P)`, and the mayEdge `.bound latN/latE` to the
    solved placement defs `(<c>Lat{N,E} P)`. Coincides with `printLeafC` on any leaf with no such params. -/
partial def printLeafAugE (c elemArg : String) : Leaf → String
  | .fam name params r =>
    let ps := if params.isEmpty then "" else " " ++ " ".intercalate (params.map (fun p => s!"({p}Sol P)"))
    s!"{name} P{ps}{cNodeOf r}{elemArg}"
  | .bound name r =>
    let fn := if name == "latN" then s!"{c}LatN" else s!"{c}LatE"
    s!"({fn} P{cNodeOf r}{elemArg})"
  | .union a b => s!"(({printLeafAugE c elemArg a}).union ({printLeafAugE c elemArg b}))"
  | .sdiff a b => s!"(({printLeafAugE c elemArg a}).sdiff ({printLeafAugE c elemArg b}))"
  | .empty     => "∅"
  | .univ name => s!"{name} P"

def printLeafAug (c : String) : Leaf → String := printLeafAugE c ""

/-- `evs(term, self)` in the Augmented `R` body: `printEvs` with the self value the bound `π`/`π'` (`sf`),
    and foreign leaves via `printLeafAug`. -/
partial def printEvsAug (sf st c : String) : Transfer → String
  | .var        => sf
  | .const l    => printLeafAug c l
  | .union a b  => s!"(({printEvsAug sf st c a}).union ({printEvsAug sf st c b}))"
  | .inter a b  => s!"(({printEvsAug sf st c a}).filter (fun y => ({printEvsAug sf st c b}).contains y))"
  | .diffc a l  => s!"(({printEvsAug sf st c a}).filter (fun y => !({printLeafAug c l}).contains y))"
  | .gate s r   => s!"(if ({sf}).toList.any (fun w => ({printLeafAug c s}).contains w) then {printLeafAug c r} else (∅ : {st}))"
  | .image U R  => s!"(MTC.imageS ({printLeafAug c U}) ({R.name} P c.node) ({sf}))"
  | .gather U s => s!"(MTC.gatherS ({printLeafAug c U}) (fun z => {printLeafAugE c " z" s}) ({sf}))"

/-- The clamp value read at the concrete source `c.node` — the Augmented analogue of `printClampAtN`. -/
def printClampAtCNode (a : AnalysisIR) : String :=
  match a.clamp with
  | .hi l      => printLeafAug a.carried l
  | .lo l      => printLeafAug a.carried l
  | .both _ hi => printLeafAug a.carried hi
  | .none      => s!"{a.univ.name} P c.node"

/-- The doubly-clamped ghost's `(R body, Drives term)`: the `MTC.evs` membership `predict`, plus (for a
    backward ghost) the output-side clamp folded at the source (`check`/`ceiling` for must, `floor` for may). -/
def augClampC (a : AnalysisIR) : String × String :=
  let c := a.carried; let t := s!"{c}T P"; let lo := s!"{c}Lo P"; let hi := s!"{c}Hi P"
  let vd := s!"({c}Sol_valid P wf)"
  match a.quadrant with
  | .fwdMust =>
    (s!"fun c π c' π' => ∀ x ∈ π', x ∈ MTC.evs (c.node, c'.node) ({t}) π ∨ x ∈ {lo} c'.node",
     s!"fun c c' hstep => {vd}.predict c c' hstep")
  | .fwdMay =>
    (s!"fun c π c' π' => ∀ x ∈ MTC.evs (c.node, c'.node) ({t}) π, x ∈ {hi} c'.node → x ∈ π'",
     s!"fun c c' hstep => {vd}.predict c c' hstep")
  | .bwdMust =>
    (s!"fun c π c' π' => (∀ x ∈ π, x ∈ MTC.evs (c.node, c'.node) ({t}) π' ∨ x ∈ {lo} c.node) ∧ (∀ x ∈ π, x ∈ {hi} c.node)",
     s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.check c.node⟩")
  | _ =>
    (s!"fun c π c' π' => (∀ x ∈ MTC.evs (c.node, c'.node) ({t}) π', x ∈ {hi} c.node → x ∈ π) ∧ (∀ x ∈ {lo} c.node, x ∈ π)",
     s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.floor c.node⟩")

/-- The `(R body, Drives term)` for one ghost, mirroring `emitClauses`/`emitGhostVE` shape-by-shape. -/
def augRelAndDrives (a : AnalysisIR) : Res (String × String) := do
  let c := a.carried; let st := a.dom; let q := a.quadrant
  let vd := s!"({c}Sol_valid P wf)"
  if a.mode == .confluence then
    let f := a.foreigns.headD ""
    return (s!"fun c π c' π' => {confLe st q} π (({f}Sol P) c'.node)",
            s!"fun c c' hstep => {vd}.predict c c' hstep")
  if a.clamp.isBoth then return augClampC a
  if a.isFwdEdge then
    match a.transfer with
    | .union (.const pl) (.diffc .var gl) =>
      return (s!"fun c π c' π' => π'.Subset (({printLeafAug c pl}).union (π.sdiff ({printLeafAug c gl})))",
              s!"fun c c' hstep => {vd}.update c c' hstep")
    | _ => err {} s!"emit Aug: fwdEdge {c} transfer not `place ∪ (self ∖ gres)`"
  if a.isMayEdge then
    let lo ← match a.clamp with | .lo l => pure l | _ => err {} s!"emit Aug: mayEdge {c} needs a floor clamp"
    return (s!"fun c π c' π' => (π'.Subset (π.union ((({c}LatN P) c'.node).union (({c}LatE P) c.node c'.node)))) ∧ (({printLeafAug c lo}).Subset π)",
            s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.check c.node⟩")
  match q with
  | .fwdMust =>
    if isDiamond a.transfer then
      let gen := firstConstFam a.transfer; let transp := diamondTransp a.transfer
      return (s!"fun c π c' π' => π'.Subset (({gen} P c.node).union (π.inter ({transp} P c.node)))",
              s!"fun c c' hstep => {vd}.update c c' hstep")
    let evs := printEvsAug "π" st c a.transfer
    return (s!"fun c π c' π' => π'.Subset ({evs})", s!"fun c c' hstep => {vd}.update c c' hstep")
  | .fwdMay =>
    if isDiamond a.transfer then
      let gen := firstConstFam a.transfer; let transp := diamondTransp a.transfer
      return (s!"fun c π c' π' => (({gen} P c.node).union (π.inter ({transp} P c.node))).Subset π'",
              s!"fun c c' hstep => {vd}.update c c' hstep")
    let evs := printEvsAug "π" st c a.transfer
    return (s!"fun c π c' π' => {st}.Subset ({evs}) π'", s!"fun c c' hstep => {vd}.update c c' hstep")
  | .bwdMust =>
    if isDiamond a.transfer then
      let gen := firstConstFam a.transfer; let transp := diamondTransp a.transfer
      return (s!"fun c π c' π' => ((π.sdiff ({gen} P c.node)).Subset π') ∧ (π.Subset (({gen} P c.node).union ({transp} P c.node)))",
              s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.check c.node⟩")
    let evs := printEvsAug "π'" st c a.transfer
    return (s!"fun c π c' π' => (π.Subset ({evs})) ∧ (π.Subset ({printClampAtCNode a}))",
            s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.check c.node⟩")
  | .bwdMay =>
    if isMeetsForm a.transfer then
      let kill := gateKillName a.transfer; let gres := gateResName a.transfer; let floor := a.clamp.floorName
      return (s!"fun c π c' π' => (π'.Subset (π.union ({kill} P c.node))) ∧ ((∃ x ∈ {kill} P c.node, x ∈ π') → ({gres} P c.node).Subset π) ∧ (({floor} P c.node).Subset π)",
              s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.gate c c' hstep, {vd}.check c.node⟩")
    let evs := printEvsAug "π'" st c a.transfer
    return (s!"fun c π c' π' => ({st}.Subset ({evs}) π) ∧ (({printClampAtCNode a}).Subset π)",
            s!"fun c c' hstep => ⟨{vd}.predict c c' hstep, {vd}.check c.node⟩")
  | _ => err {} s!"emit Aug: ghost {c} has confluence quadrant {repr q} (handled earlier)"

/-- One ghost's Augmented block: `<c>R` + `Drives` witness + `preservation`/`progress`/`bisim` + asserts. -/
def augBlock (a : AnalysisIR) : Res String := do
  let c := a.carried; let st := a.dom
  let (rbody, drives) ← augRelAndDrives a
  pure (
    s!"/-! ## `{c}` (`{a.structN}`). -/\n\n" ++
    s!"def {c}R (P : Program) : Config → {st} → Config → {st} → Prop :=\n  {rbody}\n\n" ++
    s!"theorem {c}_drives (P : Program) (wf : WellFormed P) : Drives P ({c}R P) ({c}Sol P) :=\n  {drives}\n\n" ++
    s!"theorem {c}_preservation (P : Program) (a a' : Aug {st}) (h : AugStep P ({c}R P) a a') :\n    Step P a.cfg a'.cfg := preservation h\n\n" ++
    s!"theorem {c}_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :\n    AugStep P ({c}R P) ⟨c, {c}Sol P c.node⟩ ⟨c', {c}Sol P c'.node⟩ := progress ({c}_drives P wf) hs\n\n" ++
    s!"theorem {c}_bisim (P : Program) (wf : WellFormed P) :\n    (∀ c c', Step P c c' → AugStep P ({c}R P) ⟨c, {c}Sol P c.node⟩ ⟨c', {c}Sol P c'.node⟩) ∧\n    (∀ a a' : Aug {st}, AugStep P ({c}R P) a a' → Step P a.cfg a'.cfg) :=\n  bisim ({c}_drives P wf)\n\n" ++
    s!"#assert_clean_axioms {c}_drives\n#assert_clean_axioms {c}_progress\n\n")

/-- The whole `Augmented.lean` for one analysis (per-ghost Preservation + Progress). -/
def emitAugmented (irs : List AnalysisIR) : Res String := do
  let a ← match irs.head? with
    | some a => pure a
    | none   => err {} "emit Aug: empty analysis"
  let ns := a.nsName
  let opens := "open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std" ++ includeOpens a
  let header := s!"-- Copyright (c) 2026 Martin Rinard\n-- GENERATED from {a.analysis}.gsl by `lake exe gen` — do not edit.\nimport Generated.Seam.{a.dir}.ValidExtremal\nimport BaseLanguage.Analysis.Augmented\nimport BaseLanguage.Meta.AxiomCheck\nnamespace {ns}\n{opens}\nset_option linter.unusedVariables false\n\n"
  let blocks ← irs.mapM augBlock
  pure (header ++ String.join blocks ++ s!"end {ns}\n")

/-- The whole `ValidExtremal.lean` for one analysis. -/
def emitValidExtremal (irs : List AnalysisIR) : Res String := do
  let a ← match irs.head? with
    | some a => pure a
    | none   => err {} "emit VE: empty analysis"
  let ns := a.nsName
  let opens := "open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std" ++ includeOpens a
  let header := s!"-- Copyright (c) 2026 Martin Rinard\n-- GENERATED from {a.analysis}.gsl by `lake exe gen` — do not edit.\n{includeImports a}import Generated.Solver.{a.dir}.Solve\nimport BaseLanguage.Meta.AxiomCheck\nnamespace {ns}\n{opens}\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\n\n"
  -- GenGeneral emits the `<Name>` clause structure itself for every ghost (no authored predicate).
  let clauses := String.join (irs.map emitClauses)
  let bodies ← irs.mapM (fun it => emitGhostVE it it.quadrant)
  pure (header ++ clauses ++ String.join bodies ++ emitInterface irs ++ s!"end {ns}\n")

end GenGeneral
