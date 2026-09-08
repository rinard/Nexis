-- Copyright (c) 2026 Martin Rinard
import Std.Data.HashSet
import BaseLanguage.IR.TAC
import BaseLanguage.IR.Hashable
import BaseLanguage.IR.Cfg
import BaseLanguage.Analysis.SetOps
/-! # `PDCE.Domain` — the analysis domains (`Asgn`/`Assignments`/`Variables`) and their operations. -/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
open BaseLanguage.Analysis

/-! ## §1  Analysis domains — executable sets

`Assignments` = a set of assignment candidates (the `Sink` domain). `Variables` = a set of variables (the `Live`
domain). -/

/-- A candidate assignment `x := e` (lhs + rhs), the unit of delayability/sinking. -/
structure Asgn where
  lhs : Var
  rhs : Expr
deriving DecidableEq, Hashable, Repr, Inhabited

/-- The assignment-granular domain (the `Sink` ghost's value space). -/
abbrev Assignments := HashSet Asgn

namespace Assignments
def Subset (a b : Assignments) : Prop := ∀ x ∈ a, x ∈ b
def subset (a b : Assignments) : Bool := a.toList.all (fun x => b.contains x)
def union (a b : Assignments) : Assignments := HashSet.union a b
def inter (a b : Assignments) : Assignments := a.filter (fun x => b.contains x)
def sdiff  (a b : Assignments) : Assignments := a.filter (fun x => !b.contains x)
def empty : Assignments := ∅
def singleton (x : Asgn) : Assignments := (∅ : Assignments).insert x
def ofList (l : List Asgn) : Assignments := l.foldl (fun acc x => acc.insert x) ∅

-- Membership/monotonicity lemmas delegate to the generic `Analysis.SetOps` proofs.
theorem mem_union {a b : Assignments} {x : Asgn} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_filter' {m : Assignments} {f : Asgn → Bool} {x : Asgn} : x ∈ m.filter f ↔ x ∈ m ∧ f x = true :=
  SetOps.mem_filter'
theorem mem_inter {a b : Assignments} {x : Asgn} : x ∈ inter a b ↔ x ∈ a ∧ x ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : Assignments} {x : Asgn} : x ∈ sdiff a b ↔ x ∈ a ∧ x ∉ b := SetOps.mem_sdiff
@[refl] theorem subset_refl {a : Assignments} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Assignments} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Assignments} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') :=
  SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : Assignments} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') :=
  SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : Assignments} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) :=
  SetOps.sdiff_subset_sdiff h
end Assignments

/-! ## Surface sugar — `∪`/`∩`/`\`/`⊆` on `Assignments` (defeq to the `Assignments.*` ops). -/
instance : Union    Assignments := ⟨Assignments.union⟩
instance : Inter    Assignments := ⟨Assignments.inter⟩
instance : SDiff    Assignments := ⟨Assignments.sdiff⟩
instance : HasSubset Assignments := ⟨Assignments.Subset⟩

/-- The variable-granular domain (the `Live` ghost's value space). -/
abbrev Variables := HashSet Var

namespace Variables
def Subset (a b : Variables) : Prop := ∀ x ∈ a, x ∈ b
def union (a b : Variables) : Variables := HashSet.union a b
def empty : Variables := ∅
def singleton (x : Var) : Variables := (∅ : Variables).insert x
def ofList (l : List Var) : Variables := l.foldl (fun acc x => acc.insert x) ∅

-- Membership/monotonicity lemmas delegate to the generic `Analysis.SetOps` proofs.
theorem mem_union {a b : Variables} {x : Var} : x ∈ union a b ↔ x ∈ a ∨ x ∈ b := SetOps.mem_union
theorem mem_singleton {x y : Var} : x ∈ singleton y ↔ x = y := SetOps.mem_singleton
theorem mem_ofList {l : List Var} {x : Var} : x ∈ ofList l ↔ x ∈ l := SetOps.mem_ofList
@[refl] theorem subset_refl {a : Variables} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Variables} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Variables} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') :=
  SetOps.union_subset_union h1 h2
/-- Membership test as a `Bool` (used inside the strong-liveness gate). -/
def has (a : Variables) (x : Var) : Bool := a.contains x
theorem has_iff {a : Variables} {x : Var} : a.has x = true ↔ x ∈ a := by
  unfold has; exact Std.HashSet.contains_iff_mem
end Variables

/-! ## Surface sugar for `Variables` — `∪`/`⊆` (the only ops its ghost clauses use). -/
instance : Union    Variables := ⟨Variables.union⟩
instance : HasSubset Variables := ⟨Variables.Subset⟩

/-- Keep the candidates of `F` whose lhs is in the variable set `L` — the variable-granular `live` used
    as an lhs gate, i.e. the assignment-granular analogue of intersecting against a `Variables`. (Plumbing:
    a `Assignments.filter` by a projection of `S.π`, not a new analysis.) -/
def liveFilter (F : Assignments) (L : Variables) : Assignments := F.filter (fun a => L.contains a.lhs)
theorem mem_liveFilter {F : Assignments} {L : Variables} {a : Asgn} : a ∈ liveFilter F L ↔ a ∈ F ∧ a.lhs ∈ L := by
  unfold liveFilter; rw [Assignments.mem_filter', Std.HashSet.contains_iff_mem]

/-- **The liveness gate, with an escape for non-sinkable assignments.** Dropping a dead computation is the
    *second* way PDCE loses a fault (the first is sinking it past a branch), so an assignment outside
    `keep` passes the gate whether or not its left-hand side is live. Sound only alongside
    `PdceSpec.keepLive`, which keeps such an assignment's operands live. -/
def liveFilterK (F : Assignments) (L : Variables) (keep : Asgn → Bool) : Assignments :=
  F.filter (fun a => L.contains a.lhs || !keep a)

theorem mem_liveFilterK {F : Assignments} {L : Variables} {keep : Asgn → Bool} {a : Asgn} :
    a ∈ liveFilterK F L keep ↔ a ∈ F ∧ (a.lhs ∈ L ∨ keep a = false) := by
  unfold liveFilterK
  rw [Assignments.mem_filter', Bool.or_eq_true, Std.HashSet.contains_iff_mem, Bool.not_eq_true']

end BaseLanguage.Analyses.PDCE
