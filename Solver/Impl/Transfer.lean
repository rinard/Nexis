-- Copyright (c) 2026 Martin Rinard
import Solver.Impl.Worklist
import Solver.Impl.Graph
import Solver.Impl.Lattice

/-!
# `Solver.Impl.Transfer` — the transfer-variable vertical

A **transfer variable** `τ` carries no node-local set and never reads itself: it is just the meet
(`Greatest`/`Transfer`) or join (`Least`/`JoinTransfer`) of an *already-solved* earlier ghost `X` over
the realizable successors. So `τ(n) = ⨅/⨆_{m ∈ realizableSucc n} X(m)` — a one-shot closed form, no
fixpoint iteration. This covers LCM's two transfer variables `τₚ`/`usedOut` (PDCE has none).

`X` arrives as the earlier ghost's *bitvector* field (`Node → ESet univ.length`); the conclusions are
stated against its decode `X̂ = decode ∘ X`, which is exactly the staged `Transfer P X̂ τ` the generator
needs. All under `WellFormed P` + `univ.Nodup`.
-/

namespace Solver

open BaseLanguage Tac Semantics Std

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
variable {P : Program} {univ : List α}

/-- Below the join from every summand ⇒ the join is below (dual of `incl_meetList`). -/
theorem joinList_incl {n : Nat} {t : ESet n} {f : Node → ESet n} :
    ∀ (xs : List Node), (∀ x ∈ xs, Incl (f x) t) → Incl (joinList f xs) t
  | [], _ => incl_zero
  | x :: xs, h => incl_or_elim (h x (by simp)) (joinList_incl xs (fun y hy => h y (by simp [hy])))

/-- The join-list is monotone in its summand function. -/
theorem joinList_mono {n : Nat} {f g : Node → ESet n} :
    ∀ (xs : List Node), (∀ x ∈ xs, Incl (f x) (g x)) → Incl (joinList f xs) (joinList g xs)
  | [], _ => incl_zero
  | x :: xs, h => incl_or_mono (h x (by simp)) (joinList_mono xs (fun y hy => h y (by simp [hy])))

/-! ## The meet/join transfers and their decodes -/

def tMeet (P : Program) (univ : List α) (X : Node → ESet univ.length) (n : Node) :
    ESet univ.length := meetList X (realizableSucc P n)

def tJoin (P : Program) (univ : List α) (X : Node → ESet univ.length) (n : Node) :
    ESet univ.length := joinList X (realizableSucc P n)

def resMeet (P : Program) (univ : List α) (X : Node → ESet univ.length) (n : Node) : Std.HashSet α :=
  decode univ (tMeet P univ X n)

def resJoin (P : Program) (univ : List α) (X : Node → ESet univ.length) (n : Node) : Std.HashSet α :=
  decode univ (tJoin P univ X n)

/-! ## Generic specs (clean membership form; defeq to `Transfer`/`JoinTransfer`). -/

/-- Greatest meet-transfer spec: `τ(c) ⊆ X̂(c')` across every step, bounded by the universe. -/
def MeetSpec (P : Program) (univ : List α) (X : Node → ESet univ.length)
    (τ : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ τ c.node, x ∈ decode univ (X c'.node)) ∧
  (∀ n, ∀ x ∈ τ n, x ∈ univ)

/-- Least join-transfer spec: `X̂(c') ⊆ τ(c)` across every step, bounded by the universe. -/
def JoinSpec (P : Program) (univ : List α) (X : Node → ESet univ.length)
    (τ : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ decode univ (X c'.node), x ∈ τ c.node) ∧
  (∀ n, ∀ x ∈ τ n, x ∈ univ)

variable (hwf : WellFormed P) (hnd : univ.Nodup)

include hwf hnd in
/-- The meet transfer is the greatest `MeetSpec` solution. -/
theorem resMeet_correct (X : Node → ESet univ.length) :
    MeetSpec P univ X (resMeet P univ X) ∧
    ∀ σ, MeetSpec P univ X σ → ∀ n, ∀ x ∈ σ n, x ∈ resMeet P univ X n := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- transfer
    intro c c' hs x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hs⟩
    have hincl : Incl (meetList X (realizableSucc P c.node)) (X c'.node) := meetList_sub_mem X hpm
    exact (incl_iff_sub (α := α) hnd).mp hincl x hx
  · -- bound
    intro n x hx
    rw [resMeet, tMeet, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩
  · -- greatest
    intro σ hσ n x hx
    have hpost : Incl (encode univ (σ n)) (meetList X (realizableSucc P n)) := by
      apply incl_meetList
      intro m hm
      obtain ⟨sg, sg', hstep⟩ := realizable_iff_step.mpr hm
      exact encode_incl_decode hnd (fun y hy => hσ.1 ⟨n, sg⟩ ⟨m, sg'⟩ hstep y hy)
    have hxe : x ∈ decode univ (encode univ (σ n)) :=
      (mem_decode_encode_of_sub (fun y hy => hσ.2 n y hy)).mpr hx
    exact (incl_iff_sub (α := α) hnd).mp hpost x hxe

include hwf hnd in
/-- The join transfer is the least `JoinSpec` solution. -/
theorem resJoin_correct (X : Node → ESet univ.length) :
    JoinSpec P univ X (resJoin P univ X) ∧
    ∀ σ, JoinSpec P univ X σ → ∀ n, ∀ x ∈ resJoin P univ X n, x ∈ σ n := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- transfer
    intro c c' hs x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hs⟩
    have hincl : Incl (X c'.node) (joinList X (realizableSucc P c.node)) := joinList_mem_sub X hpm
    exact (incl_iff_sub (α := α) hnd).mp hincl x hx
  · -- bound
    intro n x hx
    rw [resJoin, tJoin, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩
  · -- least
    intro σ hσ n x hx
    have hpre : Incl (joinList X (realizableSucc P n)) (encode univ (σ n)) := by
      apply joinList_incl
      intro m hm
      obtain ⟨sg, sg', hstep⟩ := realizable_iff_step.mpr hm
      exact incl_decode_encode (fun y hy => hσ.1 ⟨n, sg⟩ ⟨m, sg'⟩ hstep y hy)
    have hxr : x ∈ decode univ (joinList X (realizableSucc P n)) := by
      rw [resJoin, tJoin] at hx; exact hx
    have := (incl_iff_sub (α := α) hnd).mp hpre x hxr
    exact (mem_decode_encode_of_sub (fun y hy => hσ.2 n y hy)).mp this

end Solver
