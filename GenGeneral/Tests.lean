-- Copyright (c) 2026 Martin Rinard
import GenGeneral.IR
import GenGeneral.Lower
import GenGeneral.Select
import GenGeneral.Printer
import GenGeneral.Wf
import GenGeneral.Emit

/-!
# `GenGeneral.Tests` — parser + IR compile-time tests

Kernel-level `#guard`s that the IR represents the pipeline's extremes — the compound-atom
acid test `PrimeAdd` (`gather ∩ gate`, fwd·may) and the located-error contract — and that the total
parser + `Lower` classify each surface shape into the right quadrant and canonical `Transfer`, and reject
malformed input with a **located** error. These fail the build on regression; they carry no proof
obligation (this is generator metadata, not verified output). The real-corpus re-parse checkpoint is the
`gengen-check` executable (`GenGeneralCheck.lean`).
-/

namespace GenGeneral.Tests
open GenGeneral

/-- `PrimeAdd`'s transfer (the compound-atom acid test):
    `union var (inter (gather allNums below) (gate primes allNums))`. -/
def primeAddTransfer : Transfer :=
  .union .var
    (.inter (.gather (.fam "allNums" [] .whole) (.fam "below" [] .whole))
            (.gate (.node "primes") (.node "allNums")))

-- The compound `var ∪ (gather ∩ gate)` acid test prints to the exact `MTC` constructor tree (the term
-- printer on the hardest shape: an atom nested inside `∩` inside `∪`).
#guard printTransfer primeAddTransfer ==
  ".union .var (.inter (.gather (allNums P) (fun (n, _) z => below P z)) (.gate (fun (n, _) => primes P n) (fun (n, _) => allNums P n)))"

-- Every atom constructor is reachable and distinct (mirrors the 8 `MTC` constructors).
#guard (Transfer.image (.fam "U" [] .whole) { name := "R", nodes := ["n"] }) !=
       (Transfer.gather (.fam "U" [] .whole) (.fam "sub" [] .whole))

-- The totality contract: `Res` carries a located error, not a silent sentinel.
#guard (match (err { line := 3, col := 7 } "unexpected token" : Res Nat) with
        | .error e => e.pos.line == 3 && e.pos.col == 7
        | .ok _    => false)

/-! ## parser + `Lower` classification -/

/-- Parse+lower a single-ghost source and project the one resulting `AnalysisIR`. -/
def one (src : String) : Option AnalysisIR :=
  match lowerGsl src with
  | .ok [a] => some a
  | _       => none

-- fwd·must (Available): the canonical diamond term `gen ∪ (var ∩ transp)`.
def availSrc := "analysis Available {
history Available avail : Exprs[Expr] {
  update : ∀ n→n'. avail(n') ⊆ genExprs(n) ∪ (avail(n) ∩ transpExprs(n))
  seed   : avail(entry) ⊆ ∅
  within : ∀ n. avail(n) ⊆ allExprs } }"

#guard (one availSrc).map (·.quadrant) == some Quadrant.fwdMust
#guard (one availSrc).map (·.transfer) ==
  some (.union (.const (.node "genExprs")) (.inter .var (.const (.node "transpExprs"))))

-- fwd·may (Reaching): self on the LHS of the propagation ⇒ may, same term shape.
def reachSrc := "analysis Reaching {
history Reaching reach : Defs[Node] {
  update : ∀ n→n'. genDefs(n) ∪ (reach(n) ∩ transpDefs(n)) ⊆ reach(n')
  seed   : ∅ ⊆ reach(entry)
  within : ∀ n. reach(n) ⊆ allDefs } }"

#guard (one reachSrc).map (·.quadrant) == some Quadrant.fwdMay

-- bwd·must (VeryBusy): ceiling clamp ⇒ must; term reconstructed as `gen ∪ (var ∩ kill)`, `hi = gen ∪ kill`.
def busySrc := "analysis VeryBusy {
prophecy VeryBusy busy : Exprs[Expr] {
  predict : ∀ n→n'. busy(n) ∖ genExprs(n) ⊆ busy(n')
  check   : ∀ n. busy(n) ⊆ genExprs(n) ∪ transpExprs(n)
  seed    : busy(final) ⊆ ∅
  within  : ∀ n. busy(n) ⊆ allExprs } }"

#guard (one busySrc).map (·.quadrant) == some Quadrant.bwdMust
#guard (one busySrc).map (·.transfer) ==
  some (.union (.const (.node "genExprs")) (.inter .var (.const (.node "transpExprs"))))
#guard (one busySrc).map (·.clamp) ==
  some (.hi (.union (.node "genExprs") (.node "transpExprs")))

-- bwd·may·gate (Live/Pdce): guarded `check` ⇒ gate atom; floor ⇒ may.
def liveSrc := "analysis Live {
prophecy Live live : Variables[Var] {
  predict : ∀ n→n'. live(n') ⊆ live(n) ∪ defVars(n)
  check   : ∀ n→n'. rhsVars(n) ⊆ live(n) when defVars(n) meets live(n')
  check   : ∀ n. condVars(n) ⊆ live(n)
  seed    : liveSeed ⊆ live(final)
  within  : ∀ n. live(n) ⊆ allVars } }"

#guard (one liveSrc).map (·.quadrant) == some Quadrant.bwdMay
#guard (one liveSrc).map (·.transfer) ==
  some (.union (.gate (.node "defVars") (.node "rhsVars")) (.diffc .var (.node "defVars")))

-- confluence (Meet): predict with a bare foreign RHS, no checks ⇒ meet.
def tauSrc := "analysis Meet {
prophecy Meet meet : Assignments[Expr] {
  predict : ∀ n→n'. meet(n) ⊆ anti(n')
  within  : ∀ n. meet(n) ⊆ allExprs } }"

#guard (one tauSrc).map (·.quadrant) == some Quadrant.meet
#guard (one tauSrc).map (·.foreigns) == some ["anti"]

/-! ## quadrant/mode selection + frame consistency -/

-- Every well-formed fixture selects its quadrant (consistent frame).
#guard ((one availSrc).bind (fun a => (selectQuadrant a).toOption)) == some Quadrant.fwdMust
#guard ((one busySrc).bind (fun a => (selectQuadrant a).toOption)) == some Quadrant.bwdMust
#guard ((one liveSrc).bind (fun a => (selectQuadrant a).toOption)) == some Quadrant.bwdMay
#guard ((one tauSrc).bind (fun a => (selectQuadrant a).toOption)) == some Quadrant.meet

-- An inconsistent frame is a diagnostic, not a silent default: a `must` fixpoint with a floor clamp.
#guard (selectQuadrant { (default : AnalysisIR) with
          name := "Bad", mode := .fixpoint, extremal := .must, clamp := .lo (.node "x") }).toOption.isNone
-- A confluence must read exactly one foreign ghost.
#guard (selectQuadrant { (default : AnalysisIR) with
          name := "Bad", mode := .confluence, extremal := .must, foreigns := [] }).toOption.isNone

/-! ## term printer -/

#guard (one availSrc).map (fun a => printTransfer a.transfer) ==
  some ".union (.const (fun (n, _) => genExprs P n)) (.inter .var (.const (fun (n, _) => transpExprs P n)))"

#guard (one liveSrc).map (fun a => printTransfer a.transfer) ==
  some ".union (.gate (fun (n, _) => defVars P n) (fun (n, _) => rhsVars P n)) (.diffc .var (fun (n, _) => defVars P n))"

-- a COMPOUND gather `sub(z)` (`needs(z) ∖ base(z)`) binds the element `z` and composes the `∖` at `z`
-- (element-indexed, unlike the edge-indexed const/gate leaves) — the general gather sub. BOTH the term
-- printer (`<c>T`) and the evs/clause printer (`<c>Clauses`) must bind `z`, or the compound is ill-typed.
#guard printTransfer (.gather (.fam "allNums" [] .whole) (.sdiff (.node "needs") (.node "base")))
  == ".gather (allNums P) (fun (n, _) z => (needs P n z).sdiff (base P n z))"
#guard printEvs "g" "c.node" "Nums" (.gather (.fam "allNums" [] .whole) (.sdiff (.node "needs") (.node "base")))
  == "(MTC.gatherS (allNums P) (fun z => ((needs P c.node z).sdiff (base P c.node z))) (g c.node))"

-- A diamond is recognized in EITHER operand order: `(self ∩ transp) ∪ gen` lowers to the SAME term as the
-- canonical `gen ∪ (self ∩ transp)`, so operand order can't silently change the emitted natural predicate.
#guard
  let d (u : String) := (lowerGsl s!"analysis A \{ history A a : Exprs[Expr] \{ update : ∀ n→n'. a(n') ⊆ {u}\n seed : a(entry) ⊆ ∅\n within : ∀ n. a(n) ⊆ allExprs } }").toOption.bind (·.head?) |>.map (·.transfer)
  d "genExprs(n) ∪ (a(n) ∩ transpExprs(n))" == d "(a(n) ∩ transpExprs(n)) ∪ genExprs(n)"

-- bwdMust emits its `Hi` ceiling def; the confluence ghost emits no `<c>T`.
#guard (one busySrc).map printTermDefs ==
  some "def busyT (P : Program) : MTC Expr :=\n  .union (.const (fun (n, _) => genExprs P n)) (.inter .var (.const (fun (n, _) => transpExprs P n)))\ndef busyHi (P : Program) : Node → Exprs := fun n => (genExprs P n).union (transpExprs P n)\n"
#guard (one tauSrc).map printTermDefs == some ""

/-! ## generic structural `Wf` -/

-- The structural Wf proof mirrors the term's ∧-tree exactly (nested ⟨⟩; gate is one nested ⟨sng,res⟩).
#guard (one availSrc).map printWf ==
  some "theorem availWf (P : Program) : MTC.Wf (listExpr P) (availT P) :=\n  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genExprs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpExprs_sub P n x hx)⟩⟩\n"
#guard (one liveSrc).map (fun a => wfProofTerm a.transfer) ==
  some "⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (rhsVars_sub P n x hx)⟩, ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx)⟩⟩"
-- confluence carries no Wf.
#guard (one tauSrc).map printWf == some ""

-- Malformed input ⇒ a located error, never a silent misclassify (totality).
#guard (lowerGsl "analysis Bad { prophecy Bad b : Exprs[Expr] { predict : ∀ n→n'. b(n) ⊆ anti(n') } }"
        |>.toOption |>.isNone)   -- no `within`
#guard (match parseGslBlocks "analysis T { histry Oops x : Exprs[Expr] { } }" with
        | .error e => e.pos.line == 1
        | .ok _    => false)      -- bad direction keyword, located on line 1

-- An ARBITRARY monotone `update` RHS (nested ∪/∩/∖ past the canonical diamond) lowers via the general
-- fallback (`lowerSetExpr`) — stress `DeepSet`.
#guard (lowerGsl
  "analysis D { history D d : Exprs[Expr] { update : ∀ n→n'. d(n') ⊆ (genExprs(n) ∪ (d(n) ∩ (transpExprs(n) ∖ killExprs(n)))) ∪ extraExprs(n)\n seed : d(entry) ⊆ ∅\n within : ∀ n. d(n) ⊆ allExprs } }"
  |>.toOption.isSome)
-- A SELF-REFERENTIAL confluence (`s ⊆ s'`, foreign == carried) ⇒ a located error at `selectAll`.
#guard (((lowerGsl "analysis S { prophecy S s : Exprs[Expr] { predict : ∀ n→n'. s(n) ⊆ s(n')\n within : ∀ n. s(n) ⊆ allExprs } }").bind selectAll).toOption.isNone)
-- A CYCLIC confluence (`a ⊆ b'`, `b ⊆ a'`, no topological solve order) ⇒ a located error at `selectAll`.
#guard (((lowerGsl "analysis C {\n prophecy A a : Exprs[Expr] { predict : ∀ n→n'. a(n) ⊆ b(n')\n within : ∀ n. a(n) ⊆ allExprs }\n prophecy B b : Exprs[Expr] { predict : ∀ n→n'. b(n) ⊆ a(n')\n within : ∀ n. b(n) ⊆ allExprs }\n}").bind selectAll).toOption.isNone)
-- An arbitrary monotone `predict` RHS lowers via the SAME general fallback (the backward analogue): a
-- non-diamond bwd·must (`self ⊆ <expr(self')>`) and bwd·may (`<expr(self')> ⊆ self`) each classify.
#guard ((lowerGsl "analysis B { prophecy B g : Defs[Node] { predict : ∀ n→n'. g(n) ⊆ genN(n) ∪ (g(n') ∩ transpN(n)) ∪ extraN(n)\n check : ∀ n. g(n) ⊆ ceilN(n)\n seed : g(final) ⊆ ∅\n within : ∀ n. g(n) ⊆ allU } }").toOption.map (fun irs => irs.head!.quadrant) == some .bwdMust)
#guard ((lowerGsl "analysis B { prophecy B m : Defs[Node] { predict : ∀ n→n'. genM(n) ∪ (m(n') ∩ transpM(n)) ⊆ m(n)\n check : ∀ n. floorM(n) ⊆ m(n)\n seed : ∅ ⊆ m(final)\n within : ∀ n. m(n) ⊆ allU } }").toOption.map (fun irs => irs.head!.quadrant) == some .bwdMay)

/-! ## term-generic full-file emitter

Structural guards on `GenGeneral.Emit`: the fixpoint quadrants (fwdMust/fwdMay/bwdMust) assemble a full
`Solve`+`ValidExtremal`. The corpus re-emit oracle is `gengen-check` (diffed against the committed
`generated/*`). -/

/-- Does `emitSolve`+`emitValidExtremal` succeed for a single-ghost source? -/
def emitsOk (src : String) : Bool :=
  match one src with
  | some a => (emitSolve [a]).toOption.isSome
              && (emitValidExtremal [a]).toOption.isSome
  | none   => false

#guard emitsOk availSrc    -- fwdMust
#guard emitsOk reachSrc    -- fwdMay
#guard emitsOk busySrc     -- bwdMust
-- a confluence ghost (Meet) combines a FOREIGN sibling's bundle field `(solve P).<foreign>`; emitted alone
-- (foreign `anti` absent from the bundle) it is a located error, not a partial file (totality).
#guard ((one tauSrc).map (fun a => (emitSolve [a]).toOption.isNone)) == some true

-- A base ghost's `_iff_flow` bridges the authored `<Name>Clauses`; bwdMust references the `ceiling` field.
def veContains (sub src : String) : Bool :=
  match one src with
  | some a => ((emitValidExtremal [a]).toOption.getD "").splitOn sub |>.length |> (· ≥ 2)
  | none   => false

#guard veContains "Available" availSrc
#guard veContains "hs.check" busySrc

/-! ## `always` clause coverage — the FORWARD guarded conditions (gate / image / gather).

`always` and `check` are one keyword-blind production (pooled as `checks` in `Lower`); a forward guarded
`always` lowers and emits exactly like its backward `check` dual. These pin the full guarded scope of the
`always` clause. (The unguarded forward clamp is not exercised: forward has no single-clamp solver, so an
unguarded `always` bound is not supported here.) -/

def fwdAlwaysImage := "analysis T { history Taint taint : Vars[Var] {
  update : ∀ n→n'. taint(n) ∪ source(n) ⊆ taint(n')
  always : ∀ n→n'. z ∈ taint(n') when ∃ y ∈ taint(n). flowsTo(n)(y,z)
  seed   : ∅ ⊆ taint(entry)
  within : ∀ n. taint(n) ⊆ allVars } }"
#guard (one fwdAlwaysImage).map (·.quadrant) == some Quadrant.fwdMay
#guard emitsOk fwdAlwaysImage

def fwdAlwaysGather := "analysis T { history SAvail avail : Defs[Node] {
  update : ∀ n→n'. avail(n') ⊆ localGen(n)
  always : ∀ n→n'. z ∈ avail(n') when structSub(z) ⊆ avail(n)
  seed   : avail(entry) ⊆ ∅
  within : ∀ n. avail(n) ⊆ allDefs } }"
#guard (one fwdAlwaysGather).map (·.quadrant) == some Quadrant.fwdMust
#guard emitsOk fwdAlwaysGather

def fwdAlwaysGate := "analysis T { history GHist g : Vars[Var] {
  update : ∀ n→n'. g(n') ⊆ g(n) ∪ definedVars(n)
  always : ∀ n→n'. rhsVars(n) ⊆ g(n') when definedVars(n) meets g(n)
  seed   : ∅ ⊆ g(entry)
  within : ∀ n. g(n) ⊆ allVars } }"
#guard (one fwdAlwaysGate).map (·.quadrant) == some Quadrant.fwdMust
#guard emitsOk fwdAlwaysGate

end GenGeneral.Tests
