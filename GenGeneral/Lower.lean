-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Parser

/-!
# `GenGeneral.Lower` — surface AST → `AnalysisIR`

Resolves a parsed `GhostBlock` into the `AnalysisIR` frame: the 2-bit `mode`/`direction`/`extremal`
choice and the canonical `Transfer` term. Returns a **located error** for any shape it cannot classify
(totality), never a silent `none`.

The emitted term is the *canonical* fixpoint term of the quadrant (the diamond: `Available`/`VeryBusy`
share `gen ∪ (var ∩ transp)`), reconstructed from the extracted families — not a transcription of the
surface clause. So the classifier extracts `(gen, transp/kill, gres, placements)` and builds the
constructor tree the term printer (`GenGeneral.Printer`) renders.
-/

namespace GenGeneral

/-! ## `SetExpr` accessors (total — a shape a position cannot accept is a *located* error) -/

def seRefOf : SetExpr → Option FamilyRef
  | .ref r => some r
  | _      => none

/-- Is this set-expr exactly the carried ghost's own ref `c(…)`? Total — a compound is never "self". -/
def isRefOf (c : String) : SetExpr → Bool
  | .ref r => r.name == c
  | _      => false

/-- Does this set-expr read the carried ghost `c` at the given node arg (`"n"` / `"n'"`), possibly nested
    inside a `∪`/`∩`/`∖` compound? Used to derive a doubly-clamped ghost's extremal from the propagation's
    orientation — `must` iff the *output* self (`c(n')` forward / `c(n)` backward) is on the subset side. -/
partial def readsSelfAt (c node : String) : SetExpr → Bool
  | .ref r     => r.name == c && r.nodes == [node]
  | .union a b => readsSelfAt c node a || readsSelfAt c node b
  | .inter a b => readsSelfAt c node a || readsSelfAt c node b
  | .diff a b  => readsSelfAt c node a || readsSelfAt c node b
  | _          => false

/-- The single-family name of a bare-ref set-expr; a **located error** (blaming `pos`, describing the
    position `ctx`) if it is a compound rather than one family. -/
def seName (pos : Pos) (ctx : String) : SetExpr → Res String
  | .ref r => .ok r.name
  | _      => err pos s!"expected a single family {ctx}, found a compound set-expression"

/-! ## Node-arg → `ReadAt` -/

/-- Read site of a family from its node args (`[n]`⇒src, `[n']`⇒tgt, `[n,n']`⇒edge, none⇒whole), or a
    **located error** on any other argument shape. -/
def readAtOf (pos : Pos) (nodes : List String) : Res ReadAt :=
  match nodes with
  | ["n"]       => .ok .src
  | ["n'"]      => .ok .tgt
  | ["n", "n'"] => .ok .edge
  | []          => .ok .whole
  | _           => err pos s!"unrecognized node arguments {nodes} (expected `n`, `n'`, `n n'`, or none)"

/-- Lower a set-expression to a `Leaf` (used for a clamp ceiling/floor, and for a gather `sub(z)` / gate
    singleton). A `Leaf` reads the **current** node `n` (`.src`) — bare (`primes`), explicit `n`, or an
    element arg (`needs(z)`, whose element the printer re-applies). A `∪`/`∖` composes leaves. **Located
    error** (never a silent default — the totality contract) on: `∅`/`∩` (not `Leaf`-shaped); a successor
    (`n'`) / edge read, which a leaf position cannot represent; or placement params, which a leaf drops. -/
partial def setExprToLeaf (pos : Pos) : SetExpr → Res Leaf
  | .ref r     =>
    if !r.params.isEmpty then
      err pos s!"a gate/gather/clamp leaf cannot carry placement params (`{r.name}`)"
    else match r.nodes with
      | ["n'"]     => err pos s!"a gate/gather/clamp leaf reads the current node, not the successor `n'` (`{r.name}`)"
      | ["n", "n'"] => err pos s!"a gate/gather/clamp leaf reads the current node, not the edge (`{r.name}`)"
      | _          => .ok (Leaf.node r.name)     -- bare / `n` / element arg (`z`): read at the current node
  | .union a b => return .union (← setExprToLeaf pos a) (← setExprToLeaf pos b)
  | .diff a b  => return .sdiff (← setExprToLeaf pos a) (← setExprToLeaf pos b)
  | _          => err pos "expected a family / union / difference here, not `∅` or `∩`"

/-- Lower a `when`-guard (`always`/`check`) to its atom `Transfer`. `∧`→`inter`, `∨`→`union`; each
    `GAtom` → its atom constructor over the analysis universe `U` (read as the whole set): `sub(z) ⊆ in`
    → `gather U sub`, `S meets in` → `gate S gateRes`, `∃ y ∈ in. R` → `image U R`. `gateRes` is the set a
    firing gate emits — the universe for a per-element clause (`z ∈ Self when …`) or the clause's own set for
    a set-level one (`Result ⊆ Self when …`); `checkToAtom` supplies it. The gather `sub(z)` and gate
    singleton may each be **any monotone set-expression** (family or `∪`/`∖` compound → `Leaf`); only `∩`
    there is a located error (not `Leaf`-shaped). -/
partial def guardToTransfer (pos : Pos) (univName : String) (gateRes : Leaf) : GuardE → Res Transfer
  | .subOf sub _  => return .gather (.fam univName [] .whole) (← setExprToLeaf pos sub)
  | .img _ _ rel  => .ok (.image (.fam univName [] .whole) rel)
  | .meets sng _  => return .gate (← setExprToLeaf pos sng) gateRes
  | .mem _ _      => .ok .var                              -- `z ∈ in` — the diagonal (incoming value)
  | .memC _ src   => return .const (Leaf.node (← seName pos "as a `z ∈ source(n)` set" src))
  | .and a b      => return .inter (← guardToTransfer pos univName gateRes a) (← guardToTransfer pos univName gateRes b)
  | .or a b       => return .union (← guardToTransfer pos univName gateRes a) (← guardToTransfer pos univName gateRes b)

/-- Lower one guarded `always`/`check` clause to its atom `Transfer`, resolving the gate result set from the
    clause form: a per-element clause (`z ∈ Self when …`, `guardElem ≠ ""`) gates the whole universe; a
    set-level clause (`Result ⊆ Self when …`) gates its own `Result` (the clause LHS — live's `rhsVars ⊆
    live when defVars meets live'`). Direction-agnostic: the atom reads the incoming value (`Self` for
    forward, `Self'` for backward), which is `.var`/the solver's `X` in either quadrant. -/
def checkToAtom (pos : Pos) (univName : String) (cc : Clause) : Res Transfer := do
  let g ← match cc.guard with
    | some g => pure g
    | none   => err cc.pos "guarded clause with no parsed guard"
  let gateRes : Leaf ← if cc.guardElem == "" then setExprToLeaf cc.pos cc.lhs
                       else pure (.fam univName [] .whole)
  guardToTransfer pos univName gateRes g

/-- The union of the atom summands from a non-empty list of guarded clauses (left-folded). -/
def atomsOf (pos : Pos) (univName : String) (ccs : List Clause) : Res Transfer := do
  match ← ccs.mapM (checkToAtom pos univName) with
  | a :: rest => rest.foldlM (fun acc t => pure (.union acc t)) a
  | []        => err pos "no guarded clauses to build an atom transfer from"

/-! ## Lowering one ghost -/

/-- Lower an **arbitrary monotone set-expression** (a propagation RHS) to a `Transfer`: `∪`→`union`, `∩`→
    `inter`, `∖`→`diffc` (its right must be a family — the `diffc` leaf), a ref to the carried ghost →
    `var`, any other family ref → `const`. The general path past the canonical `gen ∪ (var ∩ transp)`
    diamond (stress `DeepSet`; the general backward `predict`). **Enforces monotonicity** in the ghost: the
    carried ghost may occur under `∪`/`∩` or as the *minuend* of a `∖`, but never as a subtrahend (which
    would negate it) — a located error, so the precondition is checked, not assumed. Also a **located
    error** on `∅` or a non-family `∖` right (not representable as a single MTC term). -/
partial def lowerSetExpr (pos : Pos) (self : String) : SetExpr → Res Transfer
  | .ref r     => if r.name == self then .ok .var else .ok (.const (Leaf.node r.name))
  | .union a b => return .union (← lowerSetExpr pos self a) (← lowerSetExpr pos self b)
  | .inter a b => return .inter (← lowerSetExpr pos self a) (← lowerSetExpr pos self b)
  | .diff a b  =>
    match b with
    | .ref rb =>
      if rb.name == self then
        err pos s!"the ghost '{self}' may not appear on the right of a difference (`… ∖ {self}`) — the monotonicity condition requires it occur only positively (under `∪`/`∩`, or as the LEFT of `∖`)"
      else return .diffc (← lowerSetExpr pos self a) (Leaf.node rb.name)
    | _       => err pos "a `∖` (diffc) subtrahend must be a single family, not a compound"
  | .empty     => err pos "`∅` is not representable as a standalone MTC term (use it only in a seed/boundary)"

/-! ## Inversion helpers (shell-stripping for the `self ∪ kill` / `self ∖ gen` kill-shapes) -/

/-- Flatten a `∪`-tree into its operand list, so `self` can be found among the summands regardless of
    operand order or nesting (`self ∪ K₁ ∪ K₂`, `K ∪ self`, …). -/
partial def unionLeaves : SetExpr → List SetExpr
  | .union a b => unionLeaves a ++ unionLeaves b
  | e          => [e]

/-- Peel a `∖`-chain whose innermost minuend is the carried ghost `c`: `self ∖ K₁ ∖ … ∖ Kₙ ↦ [K₁,…,Kₙ]`
    (the subtrahends, outermost last), or `none` if the minuend is not exactly `self`. -/
partial def selfDiffChain (c : String) : SetExpr → Option (List SetExpr)
  | .diff a b => (selfDiffChain c a).map (· ++ [b])
  | e         => if isRefOf c e then some [] else none

/-- Fuse a non-empty list of set-expressions into one `Leaf` by `∪` (each must be leaf-shaped). -/
def fuseLeaves (pos : Pos) : List SetExpr → Res Leaf
  | []      => err pos "empty kill/gen shell — expected at least one family"
  | e :: es => do (es.foldlM (fun acc x => do pure (Leaf.union acc (← setExprToLeaf pos x))) (← setExprToLeaf pos e))

/-- Lower one parsed ghost to `AnalysisIR`. `_ghosts` (all carried names in the analysis) is currently
    unused — foreign ghosts resolve by name at emit time. The element type is read off the parsed
    `[Elem]` annotation (`g.elem`). Total: a shape it cannot classify is a located error at the ghost's
    position. -/
def lowerGhost (_ghosts : List String) (g : GhostBlock) : Res AnalysisIR := do
  let c := g.carried
  let et ← if g.elem != "" then pure g.elem
           else err g.pos s!"ghost '{g.name}': domain '{g.dom}' needs an element-type annotation — write ': {g.dom}[Elem]'"
  let cls (k : String) : List Clause := g.clauses.filter (·.kw == k)
  let cl (k : String) : Option Clause := (cls k).head?
  let isSelf (se : SetExpr) : Bool := isRefOf c se
  -- universe
  let withinCl ← match cl "within" with
    | some w => pure w
    | none   => err g.pos s!"ghost '{g.name}' has no `within` clause"
  let univName ← seName withinCl.pos "for the `within` universe" withinCl.rhs
  let univ : FamilyRef := { name := univName }
  -- seed: a NAMED family (`seed : self(bnd) ⊆ gen`) is used verbatim; a bare `∅` seed (the common case) is
  -- `Seed.empty` — the emitter emits the literal `∅` and discharges its `⊆ univ` obligation inline, so no
  -- authored `entrySeed`/`haltSeed` family or `_sub` is needed.
  let seed : Seed := match cl "seed" with
    | some sc =>
      let nonSelf := if isSelf sc.lhs then sc.rhs else sc.lhs
      match seRefOf nonSelf with
      | some r => .fam r
      | none   => .empty
    | none => .empty
  let base : AnalysisIR :=
    { name := g.name, carried := c, dom := g.dom, elem := et, univ, seed
      mode := .fixpoint, direction := .fwd, extremal := .must, transfer := .var, clamp := .none }
  let dir : Direction := if g.dir == "history" then .fwd else .bwd
  let checks := cls "check" ++ cls "always"
  -- Unguarded `check`/`always` clauses are *clamps* (a floor `lo ⊆ self` or ceiling `self ⊆ hi`); guarded
  -- ones are atom summands (handled per-branch below). A doubly-clamped ghost carries BOTH an unguarded
  -- floor and ceiling and routes to the `res*C` cap-the-transfer solvers (below); ≥2 unguarded clamps of
  -- the same polarity is a located error.
  let unguardedChecks := checks.filter (fun cc => !cc.guarded)
  let ceilings := unguardedChecks.filter (fun cc => isSelf cc.lhs)   -- `self ⊆ hi`
  let floors   := unguardedChecks.filter (fun cc => isSelf cc.rhs)   -- `lo ⊆ self`
  -- CAP-THE-TRANSFER (`res*C`, doubly-clamped): routes here when (a) there is one floor + one ceiling
  -- (a genuine `[lo, hi]` band), OR (b) a FORWARD ghost carries a lone clamp — there is no forward
  -- single-clamp solver, so the opposite bound is defaulted (a lone ceiling gets floor `∅`; a lone floor
  -- gets ceiling = the universe), recovering the single clamp as the `lo = ∅` / `hi = univ` corner of the
  -- doubly-clamped solver. (A backward lone clamp keeps its own `resMTCB*` solver — handled below.) The
  -- clamp no longer signals the quadrant, so `extremal` is read from the propagation's orientation: `must`
  -- iff the OUTPUT self (`c(n')` fwd / `c(n)` bwd) is on the subset side. The transfer is the `evs`-side of
  -- the propagation (`rhs` for must, `lhs` for may) lowered structurally.
  let noGuards := (checks.filter (·.guarded)).isEmpty
  if noGuards && ((floors.length == 1 && ceilings.length == 1)
                  || (dir == .fwd && floors.length + ceilings.length == 1)) then
    let prop ← match cl "update", cl "predict" with
      | some p, _      => pure p
      | _,      some p => pure p
      | none,   none   => err g.pos s!"ghost '{g.name}': a clamped ghost needs an `update`/`predict` propagation"
    let outNode := if dir == .fwd then "n'" else "n"
    let ex : Extremal := if readsSelfAt c outNode prop.lhs then .must else .may
    let evsSide := if ex == .must then prop.rhs else prop.lhs
    let t ← lowerSetExpr prop.pos c evsSide
    let loLeaf ← if floors.length == 1 then setExprToLeaf floors[0]!.pos floors[0]!.lhs else pure .empty
    let hiLeaf ← if ceilings.length == 1 then setExprToLeaf ceilings[0]!.pos ceilings[0]!.rhs else pure (.univ univName)
    return { base with direction := dir, extremal := ex, transfer := t, clamp := .both loLeaf hiLeaf }
  if let some second := unguardedChecks.drop 1 |>.head? then
    return ← err second.pos s!"ghost '{g.name}': {unguardedChecks.length} unguarded clamps of the same polarity — a doubly-clamped ghost carries exactly one floor (`lo ⊆ self`) and one ceiling (`self ⊆ hi`); ≥2 of a kind is unsupported"
  -- ============================================================================================
  -- The UNIFIED propagation path: history `update` (forward) and prophecy `predict` (backward) flow
  -- through ONE direction-generic lowering. `outNode` is where the OUTPUT self lives (`n'` fwd / `n` bwd);
  -- the **extremal is a function of the propagation clause** — `must` iff the output self is on the
  -- ⊆-subset side (bounded above), `may` iff on the superset side (bounded below) — SYMMETRIC across both
  -- directions (the clamp polarity is only *checked* against it, in `Select`, never used to pick the
  -- quadrant). Inversion (kill-form `self ∖ gen`, kill-carry `self ∪ kill`) is available in either
  -- direction. The one genuinely direction-specific bit is the clamp: a forward fixpoint is UNCLAMPED (its
  -- only bound is `within`); a backward fixpoint carries its boundary clamp (a ceiling `hi` for must / a
  -- floor `lo` for may) — a fact of the `resMTC*`/`resMTCB*` solver signatures, not an asymmetry to remove.
  -- ============================================================================================
  let prop ← match cl "update", cl "predict" with
    | some p, _      => pure p
    | _,      some p => pure p
    | none,   none   => err g.pos s!"ghost '{g.name}' has neither an `update` nor a `predict` propagation"
  let outNode := if dir == .fwd then "n'" else "n"
  let ex : Extremal := if readsSelfAt c outNode prop.lhs then .must else .may
  let nonSelf := if isSelf prop.lhs then prop.rhs else prop.lhs   -- the transfer side (without the output self)
  let guardedCls := g.clauses.filter (·.guarded)
  -- CONFLUENCE: no clamps/guards and the non-self side is a single bare foreign ghost ⇒ a meet
  -- (`self ⊆ foreign'`, must) / join (`foreign' ⊆ self`, may) over that one foreign (read at the successor).
  if checks.isEmpty && (seRefOf nonSelf).any (fun r => r.params.isEmpty) then
    let foreign ← seName prop.pos "as the confluence foreign ghost" nonSelf
    return { base with mode := .confluence, direction := dir, extremal := ex, transfer := .const (Leaf.node foreign), foreigns := [foreign] }
  -- A FORWARD ghost that mixes a `when`-guarded atom AND an unguarded clamp is unrepresented: the guarded
  -- path below carries no clamp (and a lone forward clamp was already handled above via `res*C`), so the
  -- clamp would be dropped — reject rather than drop it.
  if dir == .fwd then
    if let some uc := unguardedChecks.head? then
      return ← err uc.pos s!"ghost '{g.name}': a forward (`history`) ghost that combines a guarded `when` atom with an unguarded clamp is not supported (the clamp would be dropped); drop the guard, drop the clamp, or move it to a `prophecy` ghost"
  -- GUARDED ATOMS: `when`-guarded `check`/`always` clauses contribute atom summands (`gate`/`image`/
  -- `gather`, via `atomsOf`) unioned onto the non-guarded carrier.
  if !guardedCls.isEmpty then
    let atomT ← atomsOf prop.pos univName guardedCls
    if dir == .fwd then
      -- forward: `carrier ∪ atoms`, unclamped. carrier = `var` (pure carry `self ⊆ self'`) or the
      -- non-self side lowered (a bare gen `const`, or a compound like taint's `self ∪ source` ⇒ `var ∪ const`).
      let basePart : Transfer ← if isSelf prop.lhs && isSelf prop.rhs then pure .var
                                else lowerSetExpr prop.pos c nonSelf
      return { base with direction := dir, extremal := ex, transfer := .union basePart atomT }
    else
      -- backward: `atoms ∪ carrier` with a floor clamp. The carrier inverts the kill-carry `self ∪ kill` ⇒
      -- `var ∖ kill` (self on the ⊆-subset side, the meets-form live/pdce shape), or lowers a general
      -- `e(self') ⊆ self` (self on the superset side, the evs-form pass-through).
      let floor ← match unguardedChecks.head? with
        | some u => pure u
        | none   => err prop.pos s!"ghost '{g.name}': a guarded backward ghost needs a floor clamp (`lo ⊆ self`)"
      let basePart : Transfer ←
        if isSelf prop.rhs then lowerSetExpr prop.pos c prop.lhs
        else
          -- kill-carry `self ∪ kill`: `self` is one summand of the `∪`-tree (any order/nesting), the rest
          -- fuse into the kill leaf; the residuation `self' ⊆ self ∪ kill ⟺ self' ∖ kill ⊆ self` gives `var ∖ kill`.
          let ops := unionLeaves prop.rhs
          let (selfs, rest) := ops.partition (isRefOf c)
          if selfs.length == 1 && !rest.isEmpty then do
            let k ← fuseLeaves prop.pos rest
            pure (.diffc .var k)
          else err prop.pos s!"ghost '{g.name}': guarded backward carrier must be `self ∪ kill` (`self` a summand of the `∪`) or `e(self') ⊆ self`"
      let lo ← setExprToLeaf floor.pos floor.lhs
      return { base with direction := dir, extremal := ex, transfer := .union atomT basePart, clamp := .lo lo }
  -- NON-GUARDED FIXPOINT. Forward is unclamped; backward carries its boundary clamp (ceiling/floor).
  if dir == .fwd then
    -- forward: fwdEdge (`place(foreigns) ∪ (self ∖ gres)`), the diamond `gen ∪ (self ∩ transp)` in either
    -- operand order, or the general structural fallback.
    match nonSelf with
    | .union a b =>
      match seRefOf a with
      | some aref =>
        if !aref.params.isEmpty then
          -- fwdEdge: `self' ⊆ earliest(foreigns)(n,n') ∪ (self ∖ gres)`
          let gres ← match b with
            | .diff _ x => seName prop.pos "as the fwdEdge `gres`" x
            | _         => err prop.pos s!"ghost '{g.name}': fwdEdge `update` RHS must be `place ∪ (self ∖ gres)`"
          let readAt ← readAtOf prop.pos aref.nodes
          let placeLeaf : Leaf := .fam aref.name aref.params readAt
          let t : Transfer := .union (.const placeLeaf) (.diffc .var (Leaf.node gres))
          return { base with direction := dir, extremal := ex, transfer := t, foreigns := aref.params }
        else
          -- diamond `gen ∪ (self ∩ transp)` (transp a single family); ANY other monotone RHS falls to the
          -- general structural fallback (`lowerSetExpr`).
          let transpRef : Option FamilyRef := match b with
            | .inter x y => if isSelf x then seRefOf y else if isSelf y then seRefOf x else none
            | _          => none
          match transpRef with
          | some tr =>
            let t : Transfer := .union (.const (Leaf.node aref.name)) (.inter .var (.const (Leaf.node tr.name)))
            return { base with direction := dir, extremal := ex, transfer := t }
          | none =>
            let t ← lowerSetExpr prop.pos c nonSelf
            return { base with direction := dir, extremal := ex, transfer := t }
      | none =>
        -- FLIPPED diamond `(self ∩ transp) ∪ gen` (the gen is the SECOND operand) — same term as the
        -- canonical `gen ∪ (self ∩ transp)`, so operand order can't silently change the emitted predicate.
        let flipped : Option (String × SetExpr) := match seRefOf b with
          | some br => if br.params.isEmpty then some (br.name, a) else none
          | none    => none
        match flipped with
        | some (genName, .inter x y) =>
          let transp ← seName prop.pos "as the diamond `transp`" (if isSelf x then y else x)
          let t : Transfer := .union (.const (Leaf.node genName)) (.inter .var (.const (Leaf.node transp)))
          return { base with direction := dir, extremal := ex, transfer := t }
        | _ =>
          let t ← lowerSetExpr prop.pos c nonSelf
          return { base with direction := dir, extremal := ex, transfer := t }
    | _ =>
      -- general: any other monotone RHS (bare ref, `∩`, `∖`, deep nesting) — the non-diamond fallback.
      let t ← lowerSetExpr prop.pos c nonSelf
      return { base with direction := dir, extremal := ex, transfer := t }
  else
    -- backward: the boundary clamp is the single unguarded `check`/`always` (a ceiling for must, floor for may).
    let clamp ← match unguardedChecks.head? with
      | some cc => pure cc
      | none    => err prop.pos s!"ghost '{g.name}': a backward (`prophecy`) fixpoint needs a boundary clamp (a ceiling `self ⊆ hi` for must, a floor `lo ⊆ self` for may)"
    -- CONSISTENCY: the extremal is read from the `predict` clause; the clamp must AGREE in polarity — a
    -- `must` (output self bounded above) needs a ceiling `self ⊆ hi`, a `may` (bounded below) a floor
    -- `lo ⊆ self`. A mismatch is a located error (the clause and the clamp disagree on the extremal).
    if ex == .must && !isSelf clamp.lhs then
      return ← err clamp.pos s!"ghost '{g.name}': the `predict` clause makes this a `must` ghost (output self on the ⊆-subset side), so its clamp must be a ceiling `self ⊆ hi`, not the floor found here"
    if ex == .may && !isSelf clamp.rhs then
      return ← err clamp.pos s!"ghost '{g.name}': the `predict` clause makes this a `may` ghost (output self on the ⊆-superset side), so its clamp must be a floor `lo ⊆ self`, not the ceiling found here"
    if ex == .must then
      -- ceiling `self ⊆ hi`. kill-form `self ∖ gen ⊆ self'` ⇒ `gen ∪ (var ∩ kill)` (kill from the ceiling
      -- `gen ∪ kill`); any other monotone predict RHS lowers structurally with the ceiling leaf as `hi`.
      -- kill-form: `self ∖ gen ⊆ self'` (the minuend of the `∖`-chain must be exactly `self`; nested
      -- `self ∖ K₁ ∖ K₂` fuses into `gen = K₁ ∪ K₂`). Any other predict LHS lowers structurally.
      match selfDiffChain c prop.lhs with
      | some (g0 :: gs) =>
        let gen ← fuseLeaves prop.pos (g0 :: gs)
        let kill ← match clamp.rhs with
          | .union _ b => setExprToLeaf clamp.pos b
          | _          => err clamp.pos s!"ghost '{g.name}': bwd·must ceiling must be `gen ∪ kill`"
        let t : Transfer := .union (.const gen) (.inter .var (.const kill))
        return { base with direction := dir, extremal := ex, transfer := t, clamp := .hi (.union gen kill) }
      | _ =>
        let t ← lowerSetExpr prop.pos c nonSelf
        let hi ← setExprToLeaf clamp.pos clamp.rhs
        return { base with direction := dir, extremal := ex, transfer := t, clamp := .hi hi }
    else
      -- floor `lo ⊆ self`. mayEdge `self' ⊆ self ∪ (latN ∪ latE)` (edge placements); else general.
      match prop.rhs with
      | .union _ (.union n e) =>
        -- mayEdge: floor `gres ∖ latestNode(…) ⊆ self`; the placements are abstracted as bound params
        -- `latN`/`latE` (read at n'/edge in the term, at n in the Lo clamp); `edgeInsts` records each.
        let nRef ← match seRefOf n with
          | some r => pure r
          | none   => err prop.pos s!"ghost '{g.name}': mayEdge `latN` placement must be a family application"
        let eRef ← match seRefOf e with
          | some r => pure r
          | none   => err prop.pos s!"ghost '{g.name}': mayEdge `latE` placement must be a family application"
        let gres ← match clamp.lhs with
          | .diff a _ => seName clamp.pos "as the mayEdge `gres`" a
          | _         => err clamp.pos s!"ghost '{g.name}': mayEdge floor must be `gres ∖ latN`"
        let t : Transfer := .diffc .var (.union (.bound "latN" .tgt) (.bound "latE" .edge))
        let clampLo : Clamp := .lo (.sdiff (Leaf.node gres) (.bound "latN" .src))
        let fs := (nRef.params ++ eRef.params).eraseDups
        return { base with direction := dir, extremal := ex, transfer := t, clamp := clampLo, foreigns := fs, edgeInsts := [("latN", nRef), ("latE", eRef)] }
      | _ =>
        let t ← lowerSetExpr prop.pos c nonSelf
        let lo ← setExprToLeaf clamp.pos clamp.lhs
        return { base with direction := dir, extremal := ex, transfer := t, clamp := .lo lo }

/-- Lower a whole parsed program: each block via `lowerGhost` (the carried-name list threaded to each). -/
def lowerBlocks (blocks : List GhostBlock) : Res (List AnalysisIR) :=
  let ghosts := blocks.map (·.carried)
  blocks.mapM (lowerGhost ghosts)

/-- End-to-end: source `.gsl` text → `AnalysisIR` list (lex + parse + lower), or a located error. -/
def lowerGsl (src : String) : Res (List AnalysisIR) := do
  let irs ← lowerBlocks (← parseGslBlocks src)
  let aN := analysisNameOf src
  let incs := includesOf src
  pure (irs.map (fun a => { a with analysis := aN, includes := incs }))

/-- The emitted quadrant tag from the 2-bit frame (the mode/direction/extremal projection). Confluence carries its own
    meet/join; a fixpoint maps `(direction, extremal)` to the quadrant, edges folded in by the caller. -/
def AnalysisIR.quadrant (a : AnalysisIR) : Quadrant :=
  match a.mode with
  | .confluence => if a.extremal == .must then .meet else .join
  | .fixpoint =>
    match a.direction, a.extremal with
    | .fwd, .must => .fwdMust
    | .fwd, .may  => .fwdMay
    | .bwd, .must => .bwdMust
    | .bwd, .may  => .bwdMay

end GenGeneral
