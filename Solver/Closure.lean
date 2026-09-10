-- Copyright (c) 2026 Martin Rinard
import Solver.Spec
import BaseLanguage.Meta.AxiomCheck

/-!
# `Solver.Closure` — from **extremality** to the transfer **equation**

Every `MTCSpec*` predicate is a *one-sided* condition: the ghost is bounded by its transfer image, never
equal to it. Validity therefore says only that the solution is a post-fixpoint (must) or a pre-fixpoint
(may) — the degenerate valuations `∅` / `univ` satisfy the clauses of many analyses.

The solver additionally proves **extremality**, and that is enough to recover the missing direction. For a
monotone operator `F` on a complete lattice, the greatest post-fixpoint is a *fixpoint*: from `h ⊑ F h`,
monotonicity gives `F h ⊑ F (F h)`, so `F h` is itself a solution, so `F h ⊑ h` by greatestness. The `MTC`
grammar is negation-free, so `MTC.evs_mono` supplies the monotonicity (`Solver/Spec.lean`).

This file runs that argument once per quadrant, in the concrete, membership-level form the generated ghost
predicates consume. Rather than an abstract `h = F h`, each theorem is stated as the *closure* (must) or
*unfold* (may) principle that a client actually uses:

* `MTCSpec.closed` / `MTCSpecBM.closed` — if `x` satisfies every clause a solution imposes at `n`
  (transfer at each edge, boundary, universe, clamp), then `x` is **already in** `h n`;
* `MTCSpecB.unfold` / `MTCSpecMF.unfold` — conversely, an `x ∈ h n` is **justified**: it comes from the
  floor, the boundary, or one concrete step.

The competitor valuations are single-point perturbations (`addAt` / `delAt`), which is what makes these
first-order facts about one solution rather than statements over the whole solution space. Note the limit
this exposes: a client needing an *induction* over the solution (a global competitor) is not served here
and genuinely requires extremality — see `BaseLanguage/LCM/Correctness/Coverage.lean`.

Nothing here mentions bitvectors, the worklist, or any representation; it is pure `Spec`-level reasoning.
-/

namespace Solver

open BaseLanguage Tac Semantics Analysis

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-! ## Single-point competitors -/

omit [LawfulHashable α] in
/-- `h` with `x` added at node `n` only. -/
def addAt (h : Node → Std.HashSet α) (n : Node) (x : α) : Node → Std.HashSet α :=
  fun m => if m = n then Std.HashSet.union (h m) ((∅ : Std.HashSet α).insert x) else h m

/-- `h` with `x` removed at node `n` only. -/
def delAt (h : Node → Std.HashSet α) (n : Node) (x : α) : Node → Std.HashSet α :=
  fun m => if m = n then (h m).filter (fun y => !(y == x)) else h m

omit [LawfulHashable α] in
theorem mem_addAt {h : Node → Std.HashSet α} {n m : Node} {x y : α} :
    y ∈ addAt h n x m ↔ y ∈ h m ∨ (m = n ∧ y = x) := by
  unfold addAt
  by_cases hm : m = n
  · rw [if_pos hm, SetOps.mem_union, SetOps.mem_singleton]
    exact ⟨fun hy => hy.imp id (fun he => ⟨hm, he⟩), fun hy => hy.imp id (fun he => he.2)⟩
  · rw [if_neg hm]
    exact ⟨Or.inl, fun hy => hy.elim id (fun he => absurd he.1 hm)⟩

omit [LawfulHashable α] in
theorem self_sub_addAt {h : Node → Std.HashSet α} {n m : Node} {x : α} :
    SetOps.Subset (h m) (addAt h n x m) := fun _ hy => mem_addAt.mpr (Or.inl hy)

omit [LawfulHashable α] in
theorem mem_addAt_self {h : Node → Std.HashSet α} {n : Node} {x : α} : x ∈ addAt h n x n :=
  mem_addAt.mpr (Or.inr ⟨rfl, rfl⟩)

omit [LawfulHashable α] in
theorem mem_delAt {h : Node → Std.HashSet α} {n m : Node} {x y : α} :
    y ∈ delAt h n x m ↔ y ∈ h m ∧ ¬(m = n ∧ y = x) := by
  unfold delAt
  by_cases hm : m = n
  · rw [if_pos hm, SetOps.mem_filter']
    constructor
    · rintro ⟨hy, hne⟩
      exact ⟨hy, fun hc => by simp [hc.2] at hne⟩
    · rintro ⟨hy, hne⟩
      refine ⟨hy, ?_⟩
      by_cases he : y = x
      · exact absurd ⟨hm, he⟩ hne
      · simp [he]
  · rw [if_neg hm]
    exact ⟨fun hy => ⟨hy, fun hc => absurd hc.1 hm⟩, fun hy => hy.1⟩

omit [LawfulHashable α] in
theorem delAt_sub_self {h : Node → Std.HashSet α} {n m : Node} {x : α} :
    SetOps.Subset (delAt h n x m) (h m) := fun _ hy => (mem_delAt.mp hy).1

/-! ## Forward · must — the closure principle -/

omit [LawfulHashable α] in
/-- **A greatest `MTCSpec` solution is closed.** If `x` lies in the universe, satisfies the entry boundary
    when `n` is the entry, and is delivered by the transfer along *every* incoming edge of `n`, then `x` is
    already in `h n`. This is the `⊇` direction of the transfer equation, in the form a client uses. -/
theorem MTCSpec.closed {P : Program} {univ : List α} {t : MTC α} {sd : Std.HashSet α}
    {h : Node → Std.HashSet α} (hv : MTCSpec P univ t sd h)
    (hg : ∀ g, MTCSpec P univ t sd g → ∀ n, ∀ x ∈ g n, x ∈ h n)
    {n : Node} {x : α} (hu : x ∈ univ) (hsd : n = P.entry → x ∈ sd)
    (hs : ∀ c c' : Config, Step P c c' → c'.node = n →
        x ∈ MTC.evs (c.node, c'.node) t (h c.node)) :
    x ∈ h n := by
  refine hg (addAt h n x) ⟨?_, ?_, ?_⟩ n x mem_addAt_self
  · intro c c' hstep y hy
    refine MTC.evs_mono (c.node, c'.node) t (self_sub_addAt) y ?_
    rcases mem_addAt.mp hy with hy' | ⟨hn, he⟩
    · exact hv.1 c c' hstep y hy'
    · subst he; exact hs c c' hstep hn
  · intro y hy
    rcases mem_addAt.mp hy with hy' | ⟨hn, he⟩
    · exact hv.2.1 y hy'
    · subst he; exact hsd hn.symm
  · intro m y hy
    rcases mem_addAt.mp hy with hy' | ⟨_, he⟩
    · exact hv.2.2 m y hy'
    · subst he; exact hu

/-! ## Backward · must — the closure principle -/

omit [LawfulHashable α] in
/-- **A greatest `MTCSpecBM` solution is closed.** Same principle read backwards: `x` inside the ceiling
    and the halt boundary, and delivered by the transfer from *every* successor of `n`, is in `h n`. -/
theorem MTCSpecBM.closed {P : Program} {univ : List α} {t : MTC α} {hi : Node → Std.HashSet α}
    {sd : Std.HashSet α} {h : Node → Std.HashSet α} (hv : MTCSpecBM P univ t hi sd h)
    (hg : ∀ g, MTCSpecBM P univ t hi sd g → ∀ n, ∀ x ∈ g n, x ∈ h n)
    {n : Node} {x : α} (hu : x ∈ univ) (hhi : x ∈ hi n)
    (hsd : P.fetch n = some .halt → x ∈ sd)
    (hs : ∀ c c' : Config, Step P c c' → c.node = n →
        x ∈ MTC.evs (c.node, c'.node) t (h c'.node)) :
    x ∈ h n := by
  refine hg (addAt h n x) ⟨?_, ?_, ?_, ?_⟩ n x mem_addAt_self
  · intro c c' hstep y hy
    refine MTC.evs_mono (c.node, c'.node) t (self_sub_addAt) y ?_
    rcases mem_addAt.mp hy with hy' | ⟨hn, he⟩
    · exact hv.1 c c' hstep y hy'
    · subst he; exact hs c c' hstep hn
  · intro m y hy
    rcases mem_addAt.mp hy with hy' | ⟨hm, he⟩
    · exact hv.2.1 m y hy'
    · subst he; subst hm; exact hhi
  · intro c hhalt y hy
    rcases mem_addAt.mp hy with hy' | ⟨hm, he⟩
    · exact hv.2.2.1 c hhalt y hy'
    · subst he; exact hsd (hm ▸ hhalt)
  · intro m y hy
    rcases mem_addAt.mp hy with hy' | ⟨_, he⟩
    · exact hv.2.2.2 m y hy'
    · subst he; exact hu

/-! ## Backward · may — the unfold principle -/

omit [LawfulHashable α] in
/-- **A least `MTCSpecB` solution is justified.** Every `x ∈ h n` is there for a reason: the floor, the halt
    boundary, or one concrete step whose transfer delivers it. The `⊆` direction of the equation. -/
theorem MTCSpecB.unfold {P : Program} {univ : List α} {t : MTC α} {lo : Node → Std.HashSet α}
    {sd : Std.HashSet α} {h : Node → Std.HashSet α} (hv : MTCSpecB P univ t lo sd h)
    (hl : ∀ g, MTCSpecB P univ t lo sd g → ∀ n, ∀ x ∈ h n, x ∈ g n)
    {n : Node} {x : α} (hx : x ∈ h n) :
    x ∈ lo n ∨ (P.fetch n = some .halt ∧ x ∈ sd) ∨
    ∃ c c' : Config, Step P c c' ∧ c.node = n ∧ x ∈ MTC.evs (c.node, c'.node) t (h c'.node) := by
  apply Classical.byContradiction
  intro hcon
  have hlo : x ∉ lo n := fun hm => hcon (Or.inl hm)
  have hhalt : P.fetch n = some .halt → x ∉ sd := fun hf hm => hcon (Or.inr (Or.inl ⟨hf, hm⟩))
  have hstep : ∀ c c' : Config, Step P c c' → c.node = n →
      x ∉ MTC.evs (c.node, c'.node) t (h c'.node) :=
    fun c c' hst hn hm => hcon (Or.inr (Or.inr ⟨c, c', hst, hn, hm⟩))
  have hspec : MTCSpecB P univ t lo sd (delAt h n x) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hst y hy
      have hy' : y ∈ MTC.evs (c.node, c'.node) t (h c'.node) :=
        MTC.evs_mono (c.node, c'.node) t (delAt_sub_self) y hy
      refine mem_delAt.mpr ⟨hv.1 c c' hst y hy', ?_⟩
      rintro ⟨hn, he⟩
      subst he
      exact hstep c c' hst hn hy'
    · intro m y hy
      refine mem_delAt.mpr ⟨hv.2.1 m y hy, ?_⟩
      rintro ⟨hm, he⟩
      subst he; subst hm
      exact hlo hy
    · intro c hh y hy
      refine mem_delAt.mpr ⟨hv.2.2.1 c hh y hy, ?_⟩
      rintro ⟨hn, he⟩
      subst he
      exact hhalt (hn ▸ hh) hy
    · intro m y hy
      exact hv.2.2.2 m y (delAt_sub_self y hy)
  exact (mem_delAt.mp (hl (delAt h n x) hspec n x hx)).2 ⟨rfl, rfl⟩

/-! ## Forward · may — the unfold principle -/

omit [LawfulHashable α] in
/-- **A least `MTCSpecMF` solution is justified** (the forward dual; unused by LCM, stated for symmetry). -/
theorem MTCSpecMF.unfold {P : Program} {univ : List α} {t : MTC α} {sd : Std.HashSet α}
    {h : Node → Std.HashSet α} (hv : MTCSpecMF P univ t sd h)
    (hl : ∀ g, MTCSpecMF P univ t sd g → ∀ n, ∀ x ∈ h n, x ∈ g n)
    {n : Node} {x : α} (hx : x ∈ h n) :
    (n = P.entry ∧ x ∈ sd) ∨
    ∃ c c' : Config, Step P c c' ∧ c'.node = n ∧ x ∈ MTC.evs (c.node, c'.node) t (h c.node) := by
  apply Classical.byContradiction
  intro hcon
  have hent : n = P.entry → x ∉ sd := fun he hm => hcon (Or.inl ⟨he, hm⟩)
  have hstep : ∀ c c' : Config, Step P c c' → c'.node = n →
      x ∉ MTC.evs (c.node, c'.node) t (h c.node) :=
    fun c c' hst hn hm => hcon (Or.inr ⟨c, c', hst, hn, hm⟩)
  have hspec : MTCSpecMF P univ t sd (delAt h n x) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hst y hy
      have hy' : y ∈ MTC.evs (c.node, c'.node) t (h c.node) :=
        MTC.evs_mono (c.node, c'.node) t (delAt_sub_self) y hy
      refine mem_delAt.mpr ⟨hv.1 c c' hst y hy', ?_⟩
      rintro ⟨hn, he⟩
      subst he
      exact hstep c c' hst hn hy'
    · intro y hy
      refine mem_delAt.mpr ⟨hv.2.1 y hy, ?_⟩
      rintro ⟨hn, he⟩
      subst he
      exact hent hn.symm hy
    · intro m y hy
      exact hv.2.2 m y (delAt_sub_self y hy)
  exact (mem_delAt.mp (hl (delAt h n x) hspec n x hx)).2 ⟨rfl, rfl⟩

/-! ## Confluence transfers — no monotonicity needed (the ghost does not occur in its own term) -/

omit [LawfulHashable α] in
/-- **A greatest `MeetSpecS` transfer is closed**: `τ(n)` contains everything present at every successor. -/
theorem MeetSpecS.closed {P : Program} {univ : List α} {Y τ : Node → Std.HashSet α}
    (hv : MeetSpecS P univ Y τ) (hg : ∀ σ, MeetSpecS P univ Y σ → ∀ n, ∀ x ∈ σ n, x ∈ τ n)
    {n : Node} {x : α} (hu : x ∈ univ)
    (hs : ∀ c c' : Config, Step P c c' → c.node = n → x ∈ Y c'.node) :
    x ∈ τ n := by
  refine hg (addAt τ n x) ⟨?_, ?_⟩ n x mem_addAt_self
  · intro c c' hstep y hy
    rcases mem_addAt.mp hy with hy' | ⟨hn, he⟩
    · exact hv.1 c c' hstep y hy'
    · subst he; exact hs c c' hstep hn
  · intro m y hy
    rcases mem_addAt.mp hy with hy' | ⟨_, he⟩
    · exact hv.2 m y hy'
    · subst he; exact hu

omit [LawfulHashable α] in
/-- **A least `JoinSpecS` transfer is justified**: every `x ∈ τ(n)` comes from a concrete successor. -/
theorem JoinSpecS.unfold {P : Program} {univ : List α} {Y τ : Node → Std.HashSet α}
    (hv : JoinSpecS P univ Y τ) (hl : ∀ σ, JoinSpecS P univ Y σ → ∀ n, ∀ x ∈ τ n, x ∈ σ n)
    {n : Node} {x : α} (hx : x ∈ τ n) :
    ∃ c c' : Config, Step P c c' ∧ c.node = n ∧ x ∈ Y c'.node := by
  apply Classical.byContradiction
  intro hcon0
  have hcon : ∀ c c' : Config, Step P c c' → c.node = n → x ∉ Y c'.node :=
    fun c c' hst hn hm => hcon0 ⟨c, c', hst, hn, hm⟩
  have hspec : JoinSpecS P univ Y (delAt τ n x) := by
    refine ⟨?_, ?_⟩
    · intro c c' hst y hy
      refine mem_delAt.mpr ⟨hv.1 c c' hst y hy, ?_⟩
      rintro ⟨hn, he⟩
      subst he
      exact hcon c c' hst hn hy
    · intro m y hy
      exact hv.2 m y (delAt_sub_self y hy)
  exact (mem_delAt.mp (hl (delAt τ n x) hspec n x hx)).2 ⟨rfl, rfl⟩

#assert_clean_axioms MTC.evs_mono
#assert_clean_axioms MTCSpec.closed
#assert_clean_axioms MTCSpecBM.closed
#assert_clean_axioms MTCSpecB.unfold
#assert_clean_axioms MTCSpecMF.unfold
#assert_clean_axioms MeetSpecS.closed
#assert_clean_axioms JoinSpecS.unfold

end Solver
