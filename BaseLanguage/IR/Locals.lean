-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Cfg
import BaseLanguage.Analysis.SetOps
/-!
# `IR.Locals` — the analysis-facing IR interface

The syntactic single-instruction projections (`IR.TAC`: `instrDefVar`, `exprVars`, `isNumbered`, …)
read *one* `Cmd`/`Expr`. Every analysis and transform, though, works with the *program-lifted* view —
the instruction at a node, the sets of variables/expressions/definition-sites a node touches, the
program-wide universes, and the standard transparency/gate sets derived from them. This file is their
single home: the common node-local sets and accessors that specifications and transforms build on.

Two layers:

* **Domains** (`Exprs`/`Defs`/`Vars`) — the finite-powerset value spaces, with the Mathlib-`Finset`
  set algebra (`union`/`inter`/`sdiff`/`empty`/`singleton`/`Subset` + `mem_*` + `subset_refl`/`_trans`
  + `*_subset_*` monotonicity, and `∪`/`∩`/`\`/`⊆` sugar). The membership/monotonicity *proofs* live
  once in `Analysis.SetOps`; each domain's lemmas delegate to them. Live in `Tac` (available through
  the usual `open Tac`); their names are distinct from the `LCM`/`PDCE` domains.
* **Node-locals** (`Tac.Locals`) — the program-lifted accessors. Kept in a sub-namespace so `open Tac`
  does not shadow an analysis's own like-named helpers; specifications `open` it explicitly and the
  generator refers to them fully qualified.
-/

namespace BaseLanguage.Tac
open Std BaseLanguage.Analysis

/-! ## Domains — finite powersets, backed once by `Analysis.SetOps`. -/

-- Each domain is `HashSet <elem>` with the standard set algebra: the *operations* are thin wrappers
-- (so dot-notation `a.union b`/`a ⊆ b` resolves on the domain), the *membership/monotonicity lemmas*
-- delegate to the shared generic proofs in `Analysis.SetOps` (the operations are defeq to the raw
-- `HashSet` forms those lemmas are stated over). One block per element type; the proofs live once.

abbrev Exprs := HashSet Expr
namespace Exprs
def Subset (a b : Exprs) : Prop := ∀ x ∈ a, x ∈ b
def union (a b : Exprs) : Exprs := HashSet.union a b
def inter (a b : Exprs) : Exprs := a.filter (fun y => b.contains y)
def sdiff  (a b : Exprs) : Exprs := a.filter (fun y => !b.contains y)
def empty : Exprs := ∅
def singleton (x : Expr) : Exprs := (∅ : Exprs).insert x
def ofList (l : List Expr) : Exprs := l.foldl (fun acc y => acc.insert y) ∅
theorem mem_union {a b : Exprs} {x : Expr} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_inter {a b : Exprs} {x : Expr} : x ∈ inter a b ↔ x ∈ a ∧ x ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : Exprs} {x : Expr} : x ∈ sdiff a b ↔ x ∈ a ∧ x ∉ b := SetOps.mem_sdiff
theorem mem_filter' {m : Exprs} {f : Expr → Bool} {x : Expr} : x ∈ m.filter f ↔ x ∈ m ∧ f x = true := SetOps.mem_filter'
theorem mem_singleton {x y : Expr} : x ∈ (∅ : Exprs).insert y ↔ x = y := SetOps.mem_singleton
theorem mem_ofList {l : List Expr} {x : Expr} : x ∈ ofList l ↔ x ∈ l := SetOps.mem_ofList
@[refl] theorem subset_refl {a : Exprs} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Exprs} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Exprs} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') := SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : Exprs} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') := SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : Exprs} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) := SetOps.sdiff_subset_sdiff h
end Exprs
instance : Union    Exprs := ⟨Exprs.union⟩
instance : Inter    Exprs := ⟨Exprs.inter⟩
instance : SDiff    Exprs := ⟨Exprs.sdiff⟩
instance : HasSubset Exprs := ⟨Exprs.Subset⟩

abbrev Defs := HashSet Node
namespace Defs
def Subset (a b : Defs) : Prop := ∀ x ∈ a, x ∈ b
def union (a b : Defs) : Defs := HashSet.union a b
def inter (a b : Defs) : Defs := a.filter (fun y => b.contains y)
def sdiff  (a b : Defs) : Defs := a.filter (fun y => !b.contains y)
def empty : Defs := ∅
def singleton (x : Node) : Defs := (∅ : Defs).insert x
def ofList (l : List Node) : Defs := l.foldl (fun acc y => acc.insert y) ∅
theorem mem_union {a b : Defs} {x : Node} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_inter {a b : Defs} {x : Node} : x ∈ inter a b ↔ x ∈ a ∧ x ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : Defs} {x : Node} : x ∈ sdiff a b ↔ x ∈ a ∧ x ∉ b := SetOps.mem_sdiff
theorem mem_filter' {m : Defs} {f : Node → Bool} {x : Node} : x ∈ m.filter f ↔ x ∈ m ∧ f x = true := SetOps.mem_filter'
theorem mem_singleton {x y : Node} : x ∈ (∅ : Defs).insert y ↔ x = y := SetOps.mem_singleton
theorem mem_ofList {l : List Node} {x : Node} : x ∈ ofList l ↔ x ∈ l := SetOps.mem_ofList
@[refl] theorem subset_refl {a : Defs} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Defs} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Defs} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') := SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : Defs} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') := SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : Defs} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) := SetOps.sdiff_subset_sdiff h
end Defs
instance : Union    Defs := ⟨Defs.union⟩
instance : Inter    Defs := ⟨Defs.inter⟩
instance : SDiff    Defs := ⟨Defs.sdiff⟩
instance : HasSubset Defs := ⟨Defs.Subset⟩

/-- A `⟨var, const⟩` pair — the constant-propagation lattice element (`x = c` on this path). -/
abbrev CPair := Var × Val
/-- The constant-propagation domain: sets of `⟨var, const⟩` facts (fwd·must, so conflicting constants for
    a variable cancel at merges — the "multiple constants ⇒ ⊤" rule). -/
abbrev ConstPairs := HashSet CPair
namespace ConstPairs
def Subset (a b : ConstPairs) : Prop := ∀ x ∈ a, x ∈ b
def union (a b : ConstPairs) : ConstPairs := HashSet.union a b
def inter (a b : ConstPairs) : ConstPairs := a.filter (fun y => b.contains y)
def sdiff  (a b : ConstPairs) : ConstPairs := a.filter (fun y => !b.contains y)
def empty : ConstPairs := ∅
def singleton (x : CPair) : ConstPairs := (∅ : ConstPairs).insert x
def ofList (l : List CPair) : ConstPairs := l.foldl (fun acc y => acc.insert y) ∅
theorem mem_union {a b : ConstPairs} {x : CPair} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_inter {a b : ConstPairs} {x : CPair} : x ∈ inter a b ↔ x ∈ a ∧ x ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : ConstPairs} {x : CPair} : x ∈ sdiff a b ↔ x ∈ a ∧ x ∉ b := SetOps.mem_sdiff
theorem mem_filter' {m : ConstPairs} {f : CPair → Bool} {x : CPair} : x ∈ m.filter f ↔ x ∈ m ∧ f x = true := SetOps.mem_filter'
theorem mem_singleton {x y : CPair} : x ∈ (∅ : ConstPairs).insert y ↔ x = y := SetOps.mem_singleton
theorem mem_ofList {l : List CPair} {x : CPair} : x ∈ ofList l ↔ x ∈ l := SetOps.mem_ofList
@[refl] theorem subset_refl {a : ConstPairs} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : ConstPairs} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : ConstPairs} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') := SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : ConstPairs} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') := SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : ConstPairs} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) := SetOps.sdiff_subset_sdiff h
end ConstPairs
instance : Union    ConstPairs := ⟨ConstPairs.union⟩
instance : Inter    ConstPairs := ⟨ConstPairs.inter⟩
instance : SDiff    ConstPairs := ⟨ConstPairs.sdiff⟩
instance : HasSubset ConstPairs := ⟨ConstPairs.Subset⟩

abbrev Vars := HashSet Var
namespace Vars
def Subset (a b : Vars) : Prop := ∀ x ∈ a, x ∈ b
def union (a b : Vars) : Vars := HashSet.union a b
def inter (a b : Vars) : Vars := a.filter (fun y => b.contains y)
def sdiff  (a b : Vars) : Vars := a.filter (fun y => !b.contains y)
def empty : Vars := ∅
def singleton (x : Var) : Vars := (∅ : Vars).insert x
def ofList (l : List Var) : Vars := l.foldl (fun acc y => acc.insert y) ∅
theorem mem_union {a b : Vars} {x : Var} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_inter {a b : Vars} {x : Var} : x ∈ inter a b ↔ x ∈ a ∧ x ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : Vars} {x : Var} : x ∈ sdiff a b ↔ x ∈ a ∧ x ∉ b := SetOps.mem_sdiff
theorem mem_filter' {m : Vars} {f : Var → Bool} {x : Var} : x ∈ m.filter f ↔ x ∈ m ∧ f x = true := SetOps.mem_filter'
theorem mem_singleton {x y : Var} : x ∈ (∅ : Vars).insert y ↔ x = y := SetOps.mem_singleton
theorem mem_ofList {l : List Var} {x : Var} : x ∈ ofList l ↔ x ∈ l := SetOps.mem_ofList
/-- Membership test as a `Bool` (used inside a strong-liveness / faint gate). -/
def has (a : Vars) (x : Var) : Bool := a.contains x
theorem has_iff {a : Vars} {x : Var} : a.has x = true ↔ x ∈ a := by
  unfold has; exact Std.HashSet.contains_iff_mem
@[refl] theorem subset_refl {a : Vars} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Vars} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Vars} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') := SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : Vars} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') := SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : Vars} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) := SetOps.sdiff_subset_sdiff h
end Vars
instance : Union    Vars := ⟨Vars.union⟩
instance : Inter    Vars := ⟨Vars.inter⟩
instance : SDiff    Vars := ⟨Vars.sdiff⟩
instance : HasSubset Vars := ⟨Vars.Subset⟩

/-! ## Node-locals — the program-lifted IR interface. -/
namespace Locals

/-! ### Instruction projections (analysis-free) — one node's read-offs, lifted through `P.fetch`. -/

/-- The variable defined at `n`, if any. -/
def definedVar (P : Program) (n : Node) : Option Var := (P.fetch n).bind instrDefVar
/-- The variables read at `n`. -/
def usedVarList (P : Program) (n : Node) : List Var := (P.fetch n).elim [] instrUsedVars
/-- The right-hand side genExprs at `n`, if `n` is an assignment. -/
def rhsExpr (P : Program) (n : Node) : Option Expr :=
  match P.fetch n with | some (Cmd.assign _ e _) => some e | _ => none
/-- The right-hand side at `n` when it is a *compute* (non-atom), if any. -/
def computeExpr (P : Program) (n : Node) : Option Expr :=
  match rhsExpr P n with | some e => if isNumbered e then some e else none | none => none
/-- The variable tested at `n`, if `n` is a branch. -/
def condVar (P : Program) (n : Node) : Option Var :=
  match P.fetch n with | some (Cmd.ifz x _ _) => some x | _ => none
def isAssign (P : Program) (n : Node) : Bool :=
  match P.fetch n with | some (Cmd.assign _ _ _) => true | _ => false
def isBranch (P : Program) (n : Node) : Bool :=
  match P.fetch n with | some (Cmd.ifz _ _ _) => true | _ => false
def isHalt (P : Program) (n : Node) : Bool :=
  match P.fetch n with | some Cmd.halt => true | _ => false

/-! ### Expression sets — the numbered computes and their transparency. -/

/-- The numbered expression genExprs at `n` (empty unless `n` computes a non-atom rhs). -/
def genExprs (P : Program) (n : Node) : Exprs :=
  match P.fetch n with
  | some (Cmd.assign _ e _) => if isNumbered e then Exprs.singleton e else Exprs.empty
  | _                       => Exprs.empty
/-- Every numbered expression in the program. -/
def allExprs (P : Program) : Exprs :=
  (List.range P.size).foldl (fun acc n => Exprs.union acc (genExprs P n)) ∅
/-- `e` is disturbed at `n`: `n` redefines a variable that `e` reads. -/
def killsExpr (P : Program) (n : Node) (e : Expr) : Bool :=
  match definedVar P n with | some x => exprReadsVar e x | none => false
/-- Expressions undisturbed at `n`. -/
def transpExprs (P : Program) (n : Node) : Exprs := (allExprs P).filter (fun e => !killsExpr P n e)
/-- Expressions both genExprs at `n` and undisturbed there. -/
def exposedExprs (P : Program) (n : Node) : Exprs := Exprs.inter (genExprs P n) (transpExprs P n)

/-! ### Definition-site sets — the assignment nodes and their transparency. -/

/-- The definition site generated at `n` (its own node) when `n` is an assignment. -/
def genDefs (P : Program) (n : Node) : Defs :=
  match P.fetch n with | some (Cmd.assign _ _ _) => Defs.singleton n | _ => Defs.empty
/-- Every definition site in the program. -/
def allDefs (P : Program) : Defs :=
  (List.range P.size).foldl (fun acc n => Defs.union acc (genDefs P n)) ∅
/-- Def-site `m` is undisturbed at `n`: `n` does not redefine the variable `m` assigns. -/
def preservesDef (P : Program) (n m : Node) : Bool :=
  match definedVar P n with | none => true | some x => definedVar P m != some x
/-- Def-sites undisturbed at `n`. -/
def transpDefs (P : Program) (n : Node) : Defs := (allDefs P).filter (fun m => preservesDef P n m)

/-! ### Constant-propagation sets — the `⟨var, const⟩` facts (fwd·must).

    `genConst` fires only on a literal copy `x := imm c` (gen `⟨x,c⟩`); any assignment to `x` kills every
    `⟨x,·⟩` (`transpConst` = the pairs whose variable `n` does not redefine). A fwd·must accumulation over
    these leaves is constant propagation: `⟨x,c⟩` survives to `n` iff `x = c` on *every* path, so two
    different constants for `x` cancel at a merge (the "multiple constants ⇒ ⊤" rule). Expression
    evaluation (`x := y+1`, `y` constant) is out of scope for the transfer — it is handled by the fold
    alternation (P3 Part E). -/

/-- The `⟨var, const⟩` fact generated at a literal copy `x := imm c`; empty otherwise. -/
def genConst (P : Program) (n : Node) : ConstPairs :=
  match P.fetch n with
  | some (Cmd.assign x (Expr.atom (Atom.imm c)) _) => ConstPairs.singleton (x, c)
  | _                                              => ConstPairs.empty
/-- Every `⟨var, const⟩` a literal copy in the program produces — the constant universe. -/
def allConst (P : Program) : ConstPairs :=
  (List.range P.size).foldl (fun acc n => ConstPairs.union acc (genConst P n)) ∅
/-- Pairs `⟨y,c⟩` undisturbed at `n`: `n` does not redefine `y`. -/
def transpConst (P : Program) (n : Node) : ConstPairs :=
  (allConst P).filter (fun p => definedVar P n != some p.1)

/-! ### Node-reachability sets — every node gens *itself*, nothing is killed.

    The `Defs`-domain analogue of the `genVars`/`allGenVars`/`transpGenVars` trio, but where *every*
    in-range node contributes its own index (not just assignments). A fwd·may accumulation over these
    leaves is exactly structural reachability: the least solution at `n` is the set of `n`'s strict
    ancestors, so it is non-empty iff `n` is reached from a predecessor. Used by unreachable-code
    elimination (`Reachable.gsl`); see `IR.Cfg`'s `FReach` for the specification it decides. -/

/-- The node itself as a singleton (empty only when `n` is out of range). Unlike `genDefs`, this fires
    at *every* command kind — reachability does not care what a node computes, only that it exists. -/
def genNode (P : Program) (n : Node) : Defs :=
  match P.fetch n with | some _ => Defs.singleton n | none => Defs.empty
/-- Every in-range node — the reachability universe. Folds the same `genNode` leaf so membership routes
    cleanly (mirrors `allDefs`/`allGenVars`). -/
def allNodes (P : Program) : Defs :=
  (List.range P.size).foldl (fun acc n => Defs.union acc (genNode P n)) ∅
/-- The no-kill transparency mask over nodes: reachability never retracts, so nothing is killed. A
    `filter`-of-universe, so the generated `⊆ allNodes` proof is the one-liner (mirrors `transpGenVars`). -/
def transpAllNodes (P : Program) (n : Node) : Defs := (allNodes P).filter (fun _ => true)

/-! ### Variable sets — the used/defined variables and the observable universe. -/

def usedVars (P : Program) (n : Node) : Vars := Vars.ofList (usedVarList P n)
def definedVars (P : Program) (n : Node) : Vars :=
  match definedVar P n with | some x => Vars.singleton x | none => Vars.empty
/-- Variables read by `n`'s right-hand side (empty at a branch/terminal). -/
def rhsVars (P : Program) (n : Node) : Vars :=
  match P.fetch n with | some (Cmd.assign _ _ _) => usedVars P n | _ => Vars.empty
/-- Variables read by `n`'s branch condition (empty at an assignment/terminal). -/
def condVars (P : Program) (n : Node) : Vars :=
  match P.fetch n with | some (Cmd.ifz _ _ _) => usedVars P n | _ => Vars.empty
/-- Every variable the program mentions: the observables plus every used/defined variable. -/
def allVars (P : Program) : Vars :=
  Vars.union (Vars.ofList P.obs)
    ((List.range P.size).foldl (fun acc n => Vars.union acc (Vars.union (usedVars P n) (definedVars P n))) ∅)

/-- The definition-sites whose defined variable is a program **observable** (`P.obs`) — the def-nodes of
    the program's outputs. A reusable read-off (used as the "always relevant / always live" set by the
    backward analyses and as the gate trigger in `primeadd`). -/
def obsDefs (P : Program) : Defs :=
  (allDefs P).filter (fun m => match definedVar P m with | some v => P.obs.contains v | none => false)
/-- The **data-dependency** def-sites of node `z`: every def-site `m` whose defined variable is an operand
    of the computation at `z`. A reusable read-off (the gather precondition in `structavail`/`primeadd`). -/
def dataDeps (P : Program) (z : Node) : Defs :=
  (allDefs P).filter (fun m => match definedVar P m with | some v => (usedVars P z).has v | none => false)
/-! The assigned-variable gen/universe/transp trio — the `Vars` analogue of the `genDefs`/`allDefs`
    def-site block, matching on `P.fetch n` directly (so the generated out-of-range support proof
    reduces the same way) and folding the *same* gen leaf into the universe (so membership routes
    cleanly). Used by monotone-accumulating variable analyses (e.g. definite assignment). -/

/-- The variable assigned at `n` as a singleton (empty unless `n` is an assignment). -/
def genVars (P : Program) (n : Node) : Vars :=
  match P.fetch n with
  | some (Cmd.assign x _ _) => Vars.singleton x
  | _                       => Vars.empty
/-- Every variable assigned anywhere in the program. -/
def allGenVars (P : Program) : Vars :=
  (List.range P.size).foldl (fun acc n => Vars.union acc (genVars P n)) ∅
/-- The no-kill (accumulate) transparency mask over assigned variables: once assigned, a variable stays
    assigned, so nothing is killed. A `filter`-of-universe so the generated `⊆ allGenVars` proof is the
    standard one-liner. -/
def transpGenVars (P : Program) (n : Node) : Vars := (allGenVars P).filter (fun _ => true)

/-- The variables `n`'s right-hand side reads *when* `n`'s definition survives into `postset`
    (otherwise none) — the guarded contribution a node makes to a downstream variable set. -/
def needed (P : Program) (n : Node) (postset : Vars) : Vars :=
  match definedVar P n with
  | some x => if postset.contains x then rhsVars P n else Vars.empty
  | none   => Vars.empty

end Locals
end BaseLanguage.Tac
