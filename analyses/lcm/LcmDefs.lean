-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Domain
import BaseLanguage.IR.Cfg

/-!
# `LCM.LcmDefs` — the edge-precise LCM/PRE analysis spec (pure Lean).

The **single canonical spec** for LCM/PRE: node-local sets, the KRS placement quantities, the four ghost
predicates (`Anticipated`, `Available`, `Postponable`, `Used`) + the `Transfer` variable schema, and the
`LcmSpec` validity bundle + staged `Extremal` predicate. Authored directly as plain `def`/`structure` —
**no** GhostSpec DSL.

`gen` (`GenGeneral`) parses `Lcm.gsl` and emits the `Solve` and `ValidExtremal` modules from these defs. Every emitted theorem is axiom-clean (`[propext, Classical.choice, Quot.sound]`),
enforced by the `#assert_clean_axioms` build gate. Unlike PDCE, LCM `transform` *correctness* depends on
`Extremal` (the staged cascade), threaded through the field order below.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Semantics Std

/-! ## §2  Node-local sets -/

set_option linter.unusedVariables false in
def ue (P : Program) (n : Node) : Assignments :=
  match P.fetch n with
  | some (Cmd.assign x e _) => (if isNumbered e then Assignments.singleton e else ∅)
  | _                       => ∅

def transpB (P : Program) (n : Node) (e : Expr) : Bool :=
  match P.fetch n with
  | some instr => match instrDefVar instr with
      | some y => !exprReadsVar e y
      | none   => true
  | none => true

def allExprs (P : Program) : Assignments :=
  (List.range P.size).foldl (fun acc n => acc.union (ue P n)) ∅

def pass (P : Program) (n : Node) : Assignments := (allExprs P).filter (transpB P n)
def de (P : Program) (n : Node) : Assignments := Assignments.inter (ue P n) (pass P n)

def entrySeed (P : Program) : Assignments := Assignments.empty
def haltSeed (P : Program) : Assignments := Assignments.empty

/-! ## §6  Placement quantities -/

def availableOut (P : Program) (ηₐ : Node → Assignments) : Node → Assignments :=
  fun n => Assignments.union (de P n) (Assignments.inter (ηₐ n) (pass P n))
def compl (P : Program) (X : Assignments) : Assignments := Assignments.sdiff (allExprs P) X
def earliest (P : Program) (πₐ ηₐ : Node → Assignments) (tail head : Node) : Assignments :=
  Assignments.inter
    (Assignments.inter (πₐ head) (compl P (availableOut P ηₐ tail)))
    (if tail = P.entry then allExprs P
     else compl P (πₐ tail))
def latestNode (P : Program) (ηₚ τₚ : Node → Assignments) : Node → Assignments :=
  fun s => Assignments.inter (ηₚ s) (Assignments.union (ue P s) (compl P (τₚ s)))
def latestEdge (P : Program) (πₐ ηₐ ηₚ : Node → Assignments) (i j : Node) : Assignments :=
  Assignments.sdiff (Assignments.union (earliest P πₐ ηₐ i j) (Assignments.sdiff (ηₚ i) (ue P i))) (ηₚ j)

/-! ## Executable memoization of `allExprs` (compiled-only, proven equal by `rfl`)

`pass`/`de`/`earliest`/`latestNode`/`latestEdge` each rebuild `allExprs P` (the whole expression
universe) inside their per-node body. The generated solver passes them to the worklist as
`gen`/`transp`/`lo`/`kill`, so `allExprs P` is recomputed on every node — the dominant `O(n²)` cost of a
single LCM solve. These `*F` variants take the universe `ae` as a parameter; the `*Fast` wrappers hoist
`allExprs P` **out** of the per-node lambda (so a partial application evaluates it once and every node
reuses it) and `@[csimp]` swaps them into the compiled solver. Each `*F P (allExprs P) … = x P …`
holds by `rfl`, so the spec `def`s and every proof are untouched. **No new analysis** — universe
caching only. -/

def passF (P : Program) (ae : Assignments) (n : Node) : Assignments := ae.filter (transpB P n)
def deF (P : Program) (ae : Assignments) (n : Node) : Assignments := Assignments.inter (ue P n) (passF P ae n)
def complF (ae X : Assignments) : Assignments := Assignments.sdiff ae X
def availableOutF (P : Program) (ae : Assignments) (ηₐ : Node → Assignments) : Node → Assignments :=
  fun n => Assignments.union (deF P ae n) (Assignments.inter (ηₐ n) (passF P ae n))
def earliestF (P : Program) (ae : Assignments) (πₐ ηₐ : Node → Assignments) (tail head : Node) :
    Assignments :=
  Assignments.inter
    (Assignments.inter (πₐ head) (complF ae (availableOutF P ae ηₐ tail)))
    (if tail = P.entry then ae
     else complF ae (πₐ tail))
def latestNodeF (P : Program) (ae : Assignments) (ηₚ τₚ : Node → Assignments) : Node → Assignments :=
  fun s => Assignments.inter (ηₚ s) (Assignments.union (ue P s) (complF ae (τₚ s)))
def latestEdgeF (P : Program) (ae : Assignments) (πₐ ηₐ ηₚ : Node → Assignments) (i j : Node) :
    Assignments :=
  Assignments.sdiff
    (Assignments.union (earliestF P ae πₐ ηₐ i j) (Assignments.sdiff (ηₚ i) (ue P i))) (ηₚ j)

def passFast (P : Program) : Node → Assignments := let ae := allExprs P; passF P ae
@[csimp] theorem pass_eq_passFast : @pass = @passFast := by funext P n; rfl

def deFast (P : Program) : Node → Assignments := let ae := allExprs P; deF P ae
@[csimp] theorem de_eq_deFast : @de = @deFast := by funext P n; rfl

def earliestFast (P : Program) (πₐ ηₐ : Node → Assignments) : Node → Node → Assignments :=
  let ae := allExprs P; earliestF P ae πₐ ηₐ
@[csimp] theorem earliest_eq_earliestFast : @earliest = @earliestFast := by
  funext P πₐ ηₐ t h; rfl

def latestNodeFast (P : Program) (ηₚ τₚ : Node → Assignments) : Node → Assignments :=
  let ae := allExprs P; latestNodeF P ae ηₚ τₚ
@[csimp] theorem latestNode_eq_latestNodeFast : @latestNode = @latestNodeFast := by
  funext P ηₚ τₚ s; rfl

def latestEdgeFast (P : Program) (πₐ ηₐ ηₚ : Node → Assignments) : Node → Node → Assignments :=
  let ae := allExprs P; latestEdgeF P ae πₐ ηₐ ηₚ
@[csimp] theorem latestEdge_eq_latestEdgeFast : @latestEdge = @latestEdgeFast := by
  funext P πₐ ηₐ ηₚ i j; rfl

/-! ## Generic confluence predicate — the `le`-parameterized transfer relation shared by the τ ghosts.
    Library-level infra (like `MTCSpec`), not a per-ghost clause predicate: the four per-ghost predicates
    Anticipated / Available / Postponable / Used are GENERATED into `Seam/lcm/ValidExtremal.lean`. -/

structure Transfer (le : Assignments → Assignments → Prop) (P : Program) (X τ : Node → Assignments) : Prop where
  predict  : ∀ c c', Step P c c' → le (τ c.node) (X c'.node)
  within    : ∀ n, (τ n).Subset (allExprs P)

/-! ## Extremality helpers (used by the optimality developments). -/

def Greatest {γ : Type} (sub : γ → γ → Prop) (S : (Node → γ) → Prop) (g : Node → γ) : Prop :=
  S g ∧ ∀ g', S g' → ∀ n, sub (g' n) (g n)
def Least {γ : Type} (sub : γ → γ → Prop) (S : (Node → γ) → Prop) (g : Node → γ) : Prop :=
  S g ∧ ∀ g', S g' → ∀ n, sub (g n) (g' n)

end BaseLanguage.Analyses.LCM
