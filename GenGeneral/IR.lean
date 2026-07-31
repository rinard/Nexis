-- Copyright (c) 2026 Martin Rinard
/-!
# `GenGeneral.IR` — the intermediate representation

The IR the general generator pipeline flows through:

```
surface → total parser → AnalysisIR → quadrant/mode selector → term printer → files
```

`Transfer` mirrors `Solver.MTC` **exactly**, with surface-resolved family references in place
of the backend's `Node × Node → HashSet` closures — so the term printer is one constructor-per-case
map with **no per-shape branch** ("One path, arbitrary term").

`AnalysisIR` is the frame around the term: the carried ghost, the domain/element/universe, and the
2-bit `mode`/`direction`/`extremal` selection plus the boundary (`seed`/`clamp`) and foreign-ghost deps.
(The `within U` universe leaf is the field `univ` — `universe` is a Lean keyword.)

**Totality contract.** Every parser/selector function returns `Res α = Except Err α` — a value or a
**located error** (`Err` carries a `Pos`), never a silent `""`/`none`. This module defines only data;
it has no dependency on the verified backend (clean isolation).
-/

namespace GenGeneral

/-- A source position (1-based line/column) for located errors. -/
structure Pos where
  line : Nat := 0
  col  : Nat := 0
deriving Inhabited, Repr, BEq

/-- A located error: a message anchored at a source position. -/
structure Err where
  pos : Pos := {}
  msg : String
deriving Inhabited, Repr

instance : ToString Err where
  toString e := s!"{e.pos.line}:{e.pos.col}: {e.msg}"

/-- The pipeline result monad: a value or a located error. The totality contract — no function in the
    new pipeline returns an `Option`/`""` sentinel that silently misclassifies. -/
abbrev Res (α : Type) := Except Err α

/-- Raise a located error. -/
def err (pos : Pos) (msg : String) : Res α := .error { pos, msg }

/-! ## Surface-resolved leaf references -/

/-- A resolved reference to a family / placement / seed leaf. `name` is the family function; `params`
    are the foreign ghosts a *derived* placement family reads (`earliest(anti,avail)`); `nodes`
    records the node-arg reading (`["n"]`, `["n'"]`, `["n","n'"]`, an element var, or a boundary node).
    The term printer turns this into `fun e => <name> P e.1 …` (node) / `… e.1 e.2 …` (edge). -/
structure FamilyRef where
  name   : String
  params : List String := []
  nodes  : List String := []
deriving Inhabited, Repr, BEq

/-- A relational leaf `R(y,z)` for the `image` atom (`flowsTo(n)(y,z)`). -/
structure RelRef where
  name  : String
  nodes : List String := []
deriving Inhabited, Repr, BEq

/-! ## Leaf set-expressions (the content of an MTC `const`/`diffc`/atom lambda) -/

/-- How an edge-local leaf reads the current edge `e = (a, b)`:
    `src` = `e.1` (`fun (n, _) => …`), `tgt` = `e.2` (successor), `edge` = both (`fun (n, n') => …`),
    `whole` = the set itself with no node index (a gather/image universe like `allNums P`). -/
inductive ReadAt where
  | src
  | tgt
  | edge
  | whole
deriving Inhabited, Repr, BEq, DecidableEq

/-- A leaf inside an MTC `const`/`diffc`/`gate`/`gather`/`image` lambda: a family/placement read at the
    edge, or a small union of such (the LCM `latestNode(n') ∪ latestEdge(n,n')` mayEdge kill). `params`
    are the foreign ghosts a *placement* family reads (each passed as its solved value at emit time). This
    is exactly the leaf grammar the backend's edge-indexed closures range over — so the term printer is one
    structural map with no per-shape branch. -/
inductive Leaf where
  | fam   (name : String) (params : List String := []) (readAt : ReadAt := .src)  -- a program family/placement: `name P params <nodes>`
  | bound (name : String) (readAt : ReadAt := .src)                               -- a def-abstracted parameter: `name <nodes>` (no `P`)
  | union (a b : Leaf)
  | sdiff (a b : Leaf)          -- a ∖ b, for the mayEdge `Lo` clamp (gres ∖ latN)
  | empty                       -- the `∅` sentinel: a defaulted floor `lo` for a lone forward ceiling (`res*C`)
  | univ  (name : String)       -- the universe `<name> P` sentinel: a defaulted ceiling `hi` for a lone forward floor
deriving Inhabited, Repr, BEq

/-- A canonical node-family leaf read at its source `n` (`fun (n, _) => name P n`); usable as `.node "x"`. -/
def Leaf.node (name : String) : Leaf := .fam name [] .src

/-! ## The transfer term — mirrors `MTC` exactly -/

/-- The IR transfer term. One constructor per `MTC` constructor (`Solver/Spec.lean:37`), with
    `Leaf`/`RelRef` in place of the backend's edge-indexed closures. A future `MTC` atom adds one
    constructor here and one printer case — **zero** other generator change. -/
inductive Transfer where
  | var
  | const  (leaf : Leaf)
  | union  (a b : Transfer)
  | inter  (a b : Transfer)
  | diffc  (a : Transfer) (leaf : Leaf)
  | gate   (sng res : Leaf)
  | image  (U : Leaf) (rel : RelRef)
  | gather (U : Leaf) (sub : Leaf)
deriving Inhabited, Repr, BEq

/-! ## The analysis frame -/

/-- Solver family: a self-referential fixpoint (`resMTC*`) vs a confluence (`tMeet`/`tJoin`) whose
    transfer reads only a foreign ghost. -/
inductive Mode where
  | fixpoint
  | confluence
deriving Inhabited, Repr, BEq, DecidableEq

/-- Direction, from the `history`/`prophecy` keyword. -/
inductive Direction where
  | fwd
  | bwd
deriving Inhabited, Repr, BEq, DecidableEq

/-- Extremality, inferred (fixpoint) from the propagation (`predict`/`update`) clause orientation —
    `must` iff the output self (`c(n')` forward / `c(n)` backward) is on the ⊆-subset side (bounded above),
    `may` iff on the superset side (bounded below) — symmetric across both directions; the clamp polarity is
    only *checked* against it (in `Select`), never used to pick the quadrant. (Confluence) from the ⊆-side
    of the foreign-RHS propagation (`self ⊆ foreign` ⇒ meet ⇒ must; `foreign ⊆ self` ⇒ join ⇒ may). -/
inductive Extremal where
  | must
  | may
deriving Inhabited, Repr, BEq, DecidableEq

/-- The boundary seed: a named family ref, or the empty set. -/
inductive Seed where
  | empty
  | fam (f : FamilyRef)
deriving Inhabited, Repr, BEq

/-- A per-node clamp bounding the solution: floor (`lo ⊆ self`, may) or ceiling (`self ⊆ hi`, must),
    both (a doubly-clamped ghost — `res*C` cap-the-transfer), or none. The clamp value is a `Leaf`
    (`bwdMust`'s `hi = gen ∪ kill`; `mayEdge`'s `lo = gres ∖ latN`). A `.both lo hi` carries BOTH bounds and
    routes to the doubly-clamped solvers (`resFMC`/`resFmC`/`resBMC`/`resBmC`) — the quadrant still comes
    from `direction`/`extremal`, not the clamp. `within` supplies the universe ceiling separately. -/
inductive Clamp where
  | none
  | lo (f : Leaf)
  | hi (f : Leaf)
  | both (lo hi : Leaf)
deriving Inhabited, Repr, BEq

/-- The full analysis IR: the frame + the printed term. Totality: every accepted parse yields a
    well-formed `AnalysisIR` or a located `Err` — never a silent sentinel. -/
structure AnalysisIR where
  /-- the ghost/structure name (`Anticipated`) -/
  name      : String
  /-- the analysis-level name (`PDCE`/`LCM`/`Available`) from the `.gsl` `analysis <Name>` wrapper;
      the prefix for the uniform emitted interface (`<analysis>Result`/`<analysis>Solve`) -/
  analysis  : String := ""
  /-- node-local source namespaces from the file-level `include <Ns>` directives (e.g. `Tac.Locals`);
      the generator imports + opens each, so an analysis can read base + its own node-locals -/
  includes  : List String := []
  /-- the carried variable (`anti`) -/
  carried   : String
  /-- the domain family head (`Assignments`) -/
  dom       : String
  /-- the element type (`Expr`/`Asgn`/`Var`/`Nums`) -/
  elem      : String
  /-- the `within U` universe leaf -/
  univ      : FamilyRef
  mode      : Mode
  direction : Direction
  extremal  : Extremal
  transfer  : Transfer
  seed      : Seed
  clamp     : Clamp
  /-- foreign ghosts this ghost's term/placements read (the dep-DAG edges); confluence combines these -/
  foreigns  : List String := []
  /-- def-abstracted edge placements (mayEdge): a bound param name ↦ the placement family it instantiates
      to at the solve site (`latN ↦ latestNode(postp,tauP)`, `latE ↦ latestEdge(anti,avail,postp)`). -/
  edgeInsts : List (String × FamilyRef) := []
deriving Inhabited, Repr

/-- Is this a doubly-clamped ghost (carries BOTH a floor and a ceiling → the `res*C` solvers)? -/
def Clamp.isBoth : Clamp → Bool
  | .both _ _ => true
  | _         => false

/-- The floor `Leaf` of a clamp (single `.lo` or the `.both` floor), if any. -/
def Clamp.loLeaf? : Clamp → Option Leaf
  | .lo l     => some l
  | .both l _ => some l
  | _         => Option.none

/-- The ceiling `Leaf` of a clamp (single `.hi` or the `.both` ceiling), if any. -/
def Clamp.hiLeaf? : Clamp → Option Leaf
  | .hi l     => some l
  | .both _ h => some h
  | _         => Option.none

/-- The emitted quadrant/confluence tag (the selector's output). A closed vocabulary so the emitter's
    boundary/solver selection stays a 2-bit lookup, not a shape match. -/
inductive Quadrant where
  | fwdMust      -- resMTC     (history · must)
  | fwdMay       -- resMTCMF   (history · may)
  | bwdMust      -- resMTCBM   (prophecy · must)
  | bwdMay       -- resMTCB    (prophecy · may)
  | meet         -- tMeet / resMeet (confluence, self ⊆ foreign)
  | join         -- tJoin / resJoin (confluence, foreign ⊆ self)
deriving Inhabited, Repr, BEq, DecidableEq

/-- The `resMTC*`/`res*` correctness combinator name for a fixpoint quadrant. -/
def Quadrant.solver : Quadrant → String
  | .fwdMust => "resMTC"
  | .fwdMay  => "resMTCMF"
  | .bwdMust => "resMTCBM"
  | .bwdMay  => "resMTCB"
  | .meet    => "resMeet"
  | .join    => "resJoin"

end GenGeneral
