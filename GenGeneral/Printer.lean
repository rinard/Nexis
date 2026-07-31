-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Lower

/-!
# `GenGeneral.Printer` — term printer: `Transfer` → the `<x>T` MTC def

Renders the IR `Transfer`/`Leaf` into an `MTC` constructor tree. One structural constructor-per-case map — **no per-shape branch**; a future
`MTC` atom needs only its `printTransfer`/`printLeaf` case.
-/

namespace GenGeneral

/-! ## Leaf rendering -/

/-- Does a leaf read the successor endpoint anywhere (so its lambda binds `(n, n')`, not `(n, _)`)? -/
def Leaf.readsEdge : Leaf → Bool
  | .fam _ _ r   => r == .tgt || r == .edge
  | .bound _ r   => r == .tgt || r == .edge
  | .union a b   => a.readsEdge || b.readsEdge
  | .sdiff a b   => a.readsEdge || b.readsEdge
  | .empty       => false
  | .univ _      => false

/-- The node-argument spelling for a read site inside a lambda binding `n`/`n'`. -/
def nodesOf : ReadAt → String
  | .src   => " n"
  | .tgt   => " n'"
  | .edge  => " n n'"
  | .whole => ""

/-- The one leaf → applied-string fold, parametrized so the four call sites are single-line instances:
    * `node : ReadAt → String` — the node spelling (`nodesOf` binds `n`/`n'` in a lambda; `Emit.cNodeOf`
      reads the concrete edge `c.node`/`c'.node`);
    * `elemArg` — the trailing gather element (`" z"` for an element-indexed sub, else `""`);
    * `wrap` — whether a `∪`/`∖` gets an extra outer paren (Emit's evs positions need it as a bare argument;
      the term lambdas don't).
    A new `Leaf` shape is one case here, not four across two files. -/
partial def printLeafWith (node : ReadAt → String) (elemArg : String) (wrap : Bool) : Leaf → String
  | .fam name params r =>
    let ps := if params.isEmpty then "" else " " ++ " ".intercalate params
    s!"{name} P{ps}{node r}{elemArg}"
  | .bound name r => s!"{name}{node r}{elemArg}"
  | .union a b => let s := s!"({printLeafWith node elemArg wrap a}).union ({printLeafWith node elemArg wrap b})"
                  if wrap then s!"({s})" else s
  | .sdiff a b => let s := s!"({printLeafWith node elemArg wrap a}).sdiff ({printLeafWith node elemArg wrap b})"
                  if wrap then s!"({s})" else s
  | .empty     => "∅"                       -- the defaulted `∅` floor (a lone forward ceiling)
  | .univ name => s!"{name} P"              -- the defaulted universe ceiling (a lone forward floor)

/-- The *applied* form of a leaf in a term lambda (`ue P n`, `(latN n').union (latE n n')`). -/
def printLeafApplied : Leaf → String := printLeafWith nodesOf "" false

/-- The *element-applied* form — like `printLeafApplied` but with the gather element `z` as the trailing
    argument (`structSub P n z`, `(needs P n z).sdiff (base P n z)`), for the element-indexed gather `sub`. -/
def printLeafAppliedElem : Leaf → String := printLeafWith nodesOf " z" false

/-- A leaf as the body of an MTC `const`/`diffc`/gate lambda: `fun (n, _) => …` / `fun (n, n') => …`.
    These leaves are edge-indexed (`Node × Node → Set`), so no element binder. -/
def printConstLambda (l : Leaf) : String :=
  let binder := if l.readsEdge then "(n, n')" else "(n, _)"
  s!"fun {binder} => {printLeafApplied l}"

/-- A gather `sub` as the body of the MTC `gather` lambda: `fun (n, _) z => …` — binds the element `z`
    (unlike `printConstLambda`, since the gather sub is `Node × Node → α → Set`). -/
def printGatherSubLambda (l : Leaf) : String :=
  let binder := if l.readsEdge then "(n, n')" else "(n, _)"
  s!"fun {binder} z => {printLeafAppliedElem l}"

/-! ## Transfer rendering -/

/-- Whether a transfer prints as an atom (`.var`) — atoms are not parenthesized as constructor args. -/
def Transfer.isAtom : Transfer → Bool
  | .var => true
  | _    => false

/-- Render a `Transfer` as an `MTC` constructor tree. -/
partial def printTransfer : Transfer → String
  | .var        => ".var"
  | .const l    => s!".const ({printConstLambda l})"
  | .union a b  => s!".union {wrap a} {wrap b}"
  | .inter a b  => s!".inter {wrap a} {wrap b}"
  | .diffc a l  => s!".diffc {wrap a} ({printConstLambda l})"
  | .gate s r   => s!".gate ({printConstLambda s}) ({printConstLambda r})"
  | .image U R  =>
    -- the relation reads the edge source `n` (and `n'` if present): `fun (n, _) => R P n` — its result
    -- `R P n : α → α → Bool` is the `R(y,z)` the backend's `imageS` applies.
    let binder := if R.nodes.contains "n'" then "(n, n')" else "(n, _)"
    let ns := if R.nodes.isEmpty then "" else " " ++ " ".intercalate R.nodes
    s!".image ({printLeafApplied U}) (fun {binder} => {R.name} P{ns})"
  | .gather U s => s!".gather ({printLeafApplied U}) ({printGatherSubLambda s})"
where
  wrap (t : Transfer) : String := if t.isAtom then printTransfer t else s!"({printTransfer t})"

/-! ## Def-parameter signature (edge kinds abstract placements as params) -/

/-- Collect the def-abstracted parameters of a transfer, in order, deduped: placement foreign params
    (arity 1) and bound leaves (arity 1 at a node, 2 across the edge). -/
partial def collectParams : Transfer → List (String × Nat) :=
  fun t => (go t).eraseDups
where
  goLeaf : Leaf → List (String × Nat)
    | .fam _ params .edge => params.map (·, 1)   -- an edge placement abstracts its foreign ghosts
    | .fam _ _ _          => []
    | .bound name r       => [(name, if r == .edge then 2 else 1)]
    | .union a b          => goLeaf a ++ goLeaf b
    | .sdiff a b          => goLeaf a ++ goLeaf b
    | .empty              => []
    | .univ _             => []
  go : Transfer → List (String × Nat)
    | .var        => []
    | .const l    => goLeaf l
    | .diffc a l  => go a ++ goLeaf l
    | .union a b  => go a ++ go b
    | .inter a b  => go a ++ go b
    | .gate s r   => goLeaf s ++ goLeaf r
    | .image U _  => goLeaf U
    | .gather U s => goLeaf U ++ goLeaf s

/-- The parameter type for a given arity over the set type `st`. -/
def arityTy (st : String) : Nat → String
  | 2 => s!"Node → Node → {st}"
  | _ => s!"Node → {st}"

/-- Group a parameter list into Lean binder groups: consecutive same-arity names share one `(… : ty)`. -/
def groupParams (st : String) (ps : List (String × Nat)) : String :=
  let groups := ps.foldl (init := ([] : List (List String × Nat))) (fun acc (nm, ar) =>
    match acc.reverse with
    | (names, a) :: rest => if a == ar then (rest.reverse ++ [(names ++ [nm], a)]) else acc ++ [([nm], ar)]
    | [] => [([nm], ar)])
  String.intercalate "" (groups.map (fun (names, ar) => s!" ({" ".intercalate names} : {arityTy st ar})"))

/-! ## The `<x>T` (+ `Hi`/`Lo`) def block -/

/-- Emit the term def block for one analysis: `def <c>T … := <term>` plus the `Hi` (bwdMust ceiling) or
    `Lo` (mayEdge floor) def when present. -/
def printTermDefs (a : AnalysisIR) : String := Id.run do
  -- confluence ghosts carry no `<c>T` term — they are `tMeet`/`tJoin` over a foreign, emitted at the solve site.
  if a.mode == .confluence then return ""
  let c := a.carried; let et := a.elem; let st := a.dom
  let sig := groupParams st (collectParams a.transfer)
  let mut s := s!"def {c}T (P : Program){sig} : MTC {et} :=\n  {printTransfer a.transfer}\n"
  match a.clamp with
  | .hi l => s := s ++ s!"def {c}Hi (P : Program) : Node → {st} := fun n => {printLeafApplied l}\n"
  | .lo l =>
    -- only the mayEdge floor is emitted as a `<c>Lo` def (bwdMay·gate's floor is a plain solver arg).
    if !a.edgeInsts.isEmpty then
      let loSig := groupParams st (collectParams (.const l))
      s := s ++ s!"def {c}Lo (P : Program){loSig} : Node → {st} := fun n => {printLeafApplied l}\n"
  | .both lo hi =>
    -- a doubly-clamped ghost emits BOTH bound families (the `res*C` cap-the-transfer floor + ceiling).
    s := s ++ s!"def {c}Lo (P : Program) : Node → {st} := fun n => {printLeafApplied lo}\n"
    s := s ++ s!"def {c}Hi (P : Program) : Node → {st} := fun n => {printLeafApplied hi}\n"
  | .none => pure ()
  return s

end GenGeneral
