-- Copyright (c) 2026 Martin Rinard
import Std.Data.HashSet
import BaseLanguage.IR.TAC
import BaseLanguage.IR.Hashable
import BaseLanguage.IR.Cfg
import BaseLanguage.Analysis.SetOps
/-! # `LCM.Domain` — the analysis domain `Assignments` (a set of program expressions) and its operations. -/

namespace BaseLanguage.Analyses.LCM
open Tac Semantics Std
open BaseLanguage.Analysis

/-! ## §1  Analysis domain — an executable set of program expressions -/

abbrev Assignments := HashSet Expr

namespace Assignments
def Subset (a b : Assignments) : Prop := ∀ e ∈ a, e ∈ b
/-- Reverse containment `⊇` (flipped `Subset`) — the `le` a *join* transfer variable is stated against. -/
abbrev Sup (a b : Assignments) : Prop := Subset b a
def subset (a b : Assignments) : Bool := a.toList.all (fun e => b.contains e)
def union (a b : Assignments) : Assignments := HashSet.union a b
def inter (a b : Assignments) : Assignments := a.filter (fun e => b.contains e)
def sdiff  (a b : Assignments) : Assignments := a.filter (fun e => !b.contains e)
def empty : Assignments := ∅
def singleton (e : Expr) : Assignments := (∅ : Assignments).insert e

-- The membership/monotonicity lemmas delegate to the generic `Analysis.SetOps` proofs (the ops above are
-- defeq to the raw `HashSet` operations those lemmas are stated over).
theorem mem_union {a b : Assignments} {e : Expr} : e ∈ union a b ↔ e ∈ a ∨ e ∈ b := SetOps.mem_union
theorem mem_filter' {m : Assignments} {f : Expr → Bool} {e : Expr} : e ∈ m.filter f ↔ e ∈ m ∧ f e = true :=
  SetOps.mem_filter'
theorem mem_inter {a b : Assignments} {e : Expr} : e ∈ inter a b ↔ e ∈ a ∧ e ∈ b := SetOps.mem_inter
theorem mem_sdiff {a b : Assignments} {e : Expr} : e ∈ sdiff a b ↔ e ∈ a ∧ e ∉ b := SetOps.mem_sdiff
@[refl] theorem subset_refl {a : Assignments} : Subset a a := SetOps.subset_refl
theorem subset_trans {a b c : Assignments} (h1 : Subset a b) (h2 : Subset b c) : Subset a c := SetOps.subset_trans h1 h2
theorem union_subset_union {a a' b b' : Assignments} (h1 : Subset a a') (h2 : Subset b b') : Subset (union a b) (union a' b') :=
  SetOps.union_subset_union h1 h2
theorem inter_subset_inter {a a' b b' : Assignments} (h1 : Subset a a') (h2 : Subset b b') : Subset (inter a b) (inter a' b') :=
  SetOps.inter_subset_inter h1 h2
theorem sdiff_subset_sdiff {a a' b : Assignments} (h : Subset a a') : Subset (sdiff a b) (sdiff a' b) :=
  SetOps.sdiff_subset_sdiff h
end Assignments

/-! ## Surface sugar — `∪`/`∩`/`\`/`⊆` on the domain (defeq to the `Assignments.*` ops, so every
    proof, `rfl`, and the compiler are unaffected; this only lets `LcmDefs` read like the equations). -/
instance : Union    Assignments := ⟨Assignments.union⟩
instance : Inter    Assignments := ⟨Assignments.inter⟩
instance : SDiff    Assignments := ⟨Assignments.sdiff⟩
instance : HasSubset Assignments := ⟨Assignments.Subset⟩

end BaseLanguage.Analyses.LCM
