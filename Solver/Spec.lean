-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.Analysis.SetOps
import Std.Data.HashSet

/-!
# `Solver.Spec` — the MTC **specification vocabulary** (ABOVE the solver interface)

This file defines *what a valid dataflow solution is*; it says nothing about how to compute one. It has
**no dependency on the fixpoint engine** (no `ESet`/bitvectors, no worklist, no `Array`) — only the term
syntax, its set-level semantics, and the four validity predicates:

* `MTC`        — the reified, negation-free (⇒ monotone) transfer term;
* `MTC.evs`    — its **set-level** semantics (the meaning a spec is written against);
* `MTC.Wf`     — every edge-local constant stays inside the universe;
* `MTCSpec` / `MTCSpecMF` / `MTCSpecBM` / `MTCSpecB` — the validity predicate for each of the four
  quadrants (forward/backward × must/may), phrased purely over `Step` and `MTC.evs`.

A *solution* is any `h : Node → HashSet α` satisfying the quadrant's predicate; an *extremal* solution is
the greatest (must) / least (may) such `h`. `Solver.Quadrant` exposes exactly one solution per quadrant
together with that valid+extremal contract — and `Solver.Impl.*` is the only thing that computes one.
Substituting a different solution mechanism means re-implementing `Solver.Quadrant` against **this**
vocabulary; nothing here changes.
-/

namespace Solver

open BaseLanguage BaseLanguage.Analysis Tac Semantics Std

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- A **Monotone Transfer Calculus** term (`MTC`): a reified, positive (negation-free ⇒ monotone in
    the incoming value `𝕩`) set-transfer function. `var` is the incoming ghost value; every leaf carries
    **edge-indexed** data `Node × Node → …` read at the current edge `e = (a, b)`. A *node* transfer is
    the sublanguage whose leaves ignore `e.2` (e.g. `fun e => gen e.1`); an *edge* transfer (LCM
    `earliest`/`latest`) reads both endpoints (`fun e => gen e.1 e.2`) — one calculus, no separate edge
    vertical. With `∪`/`∩` the gather atoms give every monotone transfer on every edge. -/
inductive MTC (α : Type) [BEq α] [Hashable α] where
  | var
  | const (f : Node × Node → Std.HashSet α)
  | union (a b : MTC α)
  | inter (a b : MTC α)
  | diffc (a : MTC α) (f : Node × Node → Std.HashSet α)
  | gate  (sng res : Node × Node → Std.HashSet α)   -- cross-element: if X overlaps `sng` then `res` else ∅
  | image (U : Std.HashSet α) (R : Node × Node → α → α → Bool)          -- OR-gather: { y ∈ U : ∃ x ∈ X, R x y }
  | gather (U : Std.HashSet α) (sub : Node × Node → α → Std.HashSet α)  -- AND-gather: { z ∈ U : sub z ⊆ X }

namespace MTC

/-! ## Cross-element gather set-ops + their lemmas (the atom's set-level content, proved once). -/

/-- OR-gather (relational image): `{ y ∈ U : ∃ x ∈ X, R x y }`. -/
def imageS (U : Std.HashSet α) (R : α → α → Bool) (X : Std.HashSet α) : Std.HashSet α :=
  U.filter (fun y => X.toList.any (fun x => R x y))

/-- AND-gather (universal preimage): `{ e ∈ U : ∀ z ∈ sub e, z ∈ X }`. -/
def gatherS (U : Std.HashSet α) (sub : α → Std.HashSet α) (X : Std.HashSet α) : Std.HashSet α :=
  U.filter (fun e => (sub e).toList.all (fun z => X.contains z))

omit [LawfulHashable α] in
theorem mem_imageS {U : Std.HashSet α} {R : α → α → Bool} {X : Std.HashSet α} {y : α} :
    y ∈ imageS U R X ↔ y ∈ U ∧ ∃ x ∈ X, R x y = true := by
  rw [imageS, SetOps.mem_filter', List.any_eq_true]
  exact and_congr Iff.rfl ⟨fun ⟨x, hx, hr⟩ => ⟨x, Std.HashSet.mem_toList.mp hx, hr⟩,
    fun ⟨x, hx, hr⟩ => ⟨x, Std.HashSet.mem_toList.mpr hx, hr⟩⟩

omit [LawfulHashable α] in
theorem mem_gatherS {U : Std.HashSet α} {sub : α → Std.HashSet α} {X : Std.HashSet α} {e : α} :
    e ∈ gatherS U sub X ↔ e ∈ U ∧ ∀ z ∈ sub e, z ∈ X := by
  rw [gatherS, SetOps.mem_filter', List.all_eq_true]
  refine and_congr Iff.rfl ⟨fun h z hz => Std.HashSet.contains_iff_mem.mp (h z (Std.HashSet.mem_toList.mpr hz)),
    fun h z hz => Std.HashSet.contains_iff_mem.mpr (h z (Std.HashSet.mem_toList.mp hz))⟩

omit [LawfulHashable α] in
theorem imageS_mono {U : Std.HashSet α} {R} {X Y : Std.HashSet α} (h : SetOps.Subset X Y) :
    SetOps.Subset (imageS U R X) (imageS U R Y) := by
  intro y hy; rw [mem_imageS] at hy ⊢; obtain ⟨hyU, x, hx, hr⟩ := hy; exact ⟨hyU, x, h x hx, hr⟩

omit [LawfulHashable α] in
theorem gatherS_mono {U : Std.HashSet α} {sub} {X Y : Std.HashSet α} (h : SetOps.Subset X Y) :
    SetOps.Subset (gatherS U sub X) (gatherS U sub Y) := by
  intro e he; rw [mem_gatherS] at he ⊢; obtain ⟨heU, hall⟩ := he; exact ⟨heU, fun z hz => h z (hall z hz)⟩

omit [LawfulHashable α] in
theorem imageS_sub {U : Std.HashSet α} {R} {X : Std.HashSet α} : SetOps.Subset (imageS U R X) U := by
  intro y hy; rw [mem_imageS] at hy; exact hy.1

omit [LawfulHashable α] in
theorem gatherS_sub {U : Std.HashSet α} {sub} {X : Std.HashSet α} : SetOps.Subset (gatherS U sub X) U := by
  intro e he; rw [mem_gatherS] at he; exact he.1

omit [LawfulHashable α] in
theorem imageS_congr {U : Std.HashSet α} {R} {X Y : Std.HashSet α} (h : ∀ z, z ∈ X ↔ z ∈ Y) :
    ∀ y, y ∈ imageS U R X ↔ y ∈ imageS U R Y := by
  intro y; rw [mem_imageS, mem_imageS]
  exact and_congr Iff.rfl ⟨fun ⟨x, hx, hr⟩ => ⟨x, (h x).mp hx, hr⟩, fun ⟨x, hx, hr⟩ => ⟨x, (h x).mpr hx, hr⟩⟩

omit [LawfulHashable α] in
theorem gatherS_congr {U : Std.HashSet α} {sub} {X Y : Std.HashSet α} (h : ∀ z, z ∈ X ↔ z ∈ Y) :
    ∀ e, e ∈ gatherS U sub X ↔ e ∈ gatherS U sub Y := by
  intro e; rw [mem_gatherS, mem_gatherS]
  exact and_congr Iff.rfl ⟨fun hz z hz2 => (h z).mp (hz z hz2), fun hz z hz2 => (h z).mpr (hz z hz2)⟩

/-- Set denotation at edge `e = (a, b)`: `⟦t⟧set e X`. What the ghost predicate reads (raw `HashSet` ops so
    the `SetOps` membership lemmas apply; these are defeq to the per-domain `union`/`inter`/`diff`). -/
def evs (e : Node × Node) : MTC α → Std.HashSet α → Std.HashSet α
  | var,       X => X
  | const f,   _ => f e
  | union a b, X => Std.HashSet.union (evs e a X) (evs e b X)
  | inter a b, X => (evs e a X).filter (fun y => (evs e b X).contains y)
  | diffc a f, X => (evs e a X).filter (fun y => !(f e).contains y)
  | gate sng res, X => if X.toList.any (fun y => (sng e).contains y) then res e else (∅ : Std.HashSet α)
  | image U R, X   => imageS U (R e) X
  | gather U sub, X => gatherS U (sub e) X

/-- Well-formedness: every edge-local constant stays within the universe (needed for the decode bridge). -/
def Wf (univ : List α) : MTC α → Prop
  | var       => True
  | const f   => ∀ e, ∀ x ∈ f e, x ∈ univ
  | union a b => Wf univ a ∧ Wf univ b
  | inter a b => Wf univ a ∧ Wf univ b
  | diffc a f => Wf univ a ∧ ∀ e, ∀ x ∈ f e, x ∈ univ
  | gate sng res => (∀ e, ∀ x ∈ sng e, x ∈ univ) ∧ (∀ e, ∀ x ∈ res e, x ∈ univ)
  | image U R => ∀ x ∈ U, x ∈ univ
  | gather U sub => ∀ x ∈ U, x ∈ univ

/-- **Universe preservation** — if the incoming set is inside `univ`, so is the transfer's result. -/
theorem evs_sub (univ : List α) (e : Node × Node) (t : MTC α) (hw : Wf univ t) (X : Std.HashSet α)
    (hX : ∀ x ∈ X, x ∈ univ) : ∀ x ∈ evs e t X, x ∈ univ := by
  induction t with
  | var => exact hX
  | const f => intro x hx; exact hw e x hx
  | union a b iha ihb =>
      intro x hx
      rcases SetOps.mem_union.mp hx with h | h
      · exact iha hw.1 x h
      · exact ihb hw.2 x h
  | inter a b iha _ =>
      intro x hx; exact iha hw.1 x (SetOps.mem_inter.mp hx).1
  | diffc a f iha =>
      intro x hx; exact iha hw.1 x (SetOps.mem_sdiff.mp hx).1
  | gate sng res =>
      intro x hx
      by_cases hg : X.toList.any (fun y => (sng e).contains y) = true
      · rw [evs, if_pos hg] at hx; exact hw.2 e x hx
      · rw [evs, if_neg hg] at hx; exact absurd hx Std.HashSet.not_mem_empty
  | image U R => intro x hx; exact hw x (imageS_sub x hx)
  | gather U sub => intro x hx; exact hw x (gatherS_sub x hx)

omit [LawfulHashable α] in
/-- Membership-congruence of the set denotation: `evs` depends only on the argument's membership. -/
theorem evs_mem_congr (e : Node × Node) (t : MTC α) {X Y : Std.HashSet α} (h : ∀ z, z ∈ X ↔ z ∈ Y) :
    ∀ z, z ∈ evs e t X ↔ z ∈ evs e t Y := by
  induction t with
  | var => exact h
  | const f => intro z; exact Iff.rfl
  | union a b iha ihb =>
      intro z
      exact ⟨fun hz => SetOps.mem_union.mpr ((SetOps.mem_union.mp hz).imp (iha z).mp (ihb z).mp),
             fun hz => SetOps.mem_union.mpr ((SetOps.mem_union.mp hz).imp (iha z).mpr (ihb z).mpr)⟩
  | inter a b iha ihb =>
      intro z
      exact ⟨fun hz => SetOps.mem_inter.mpr (⟨(iha z).mp (SetOps.mem_inter.mp hz).1,
                (ihb z).mp (SetOps.mem_inter.mp hz).2⟩),
             fun hz => SetOps.mem_inter.mpr (⟨(iha z).mpr (SetOps.mem_inter.mp hz).1,
                (ihb z).mpr (SetOps.mem_inter.mp hz).2⟩)⟩
  | diffc a f iha =>
      intro z
      exact ⟨fun hz => SetOps.mem_sdiff.mpr ⟨(iha z).mp (SetOps.mem_sdiff.mp hz).1, (SetOps.mem_sdiff.mp hz).2⟩,
             fun hz => SetOps.mem_sdiff.mpr ⟨(iha z).mpr (SetOps.mem_sdiff.mp hz).1, (SetOps.mem_sdiff.mp hz).2⟩⟩
  | gate sng res =>
      intro z
      have hguard : X.toList.any (fun y => (sng e).contains y)
          = Y.toList.any (fun y => (sng e).contains y) := by
        rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
        exact ⟨fun ⟨y, hy, hc⟩ => ⟨y, Std.HashSet.mem_toList.mpr ((h y).mp (Std.HashSet.mem_toList.mp hy)), hc⟩,
               fun ⟨y, hy, hc⟩ => ⟨y, Std.HashSet.mem_toList.mpr ((h y).mpr (Std.HashSet.mem_toList.mp hy)), hc⟩⟩
      simp only [evs, hguard]
  | image U R => exact imageS_congr h
  | gather U sub => exact gatherS_congr h


end MTC

/-! ## The four quadrant validity predicates.

Each says: the ghost `h` is consistent with the term `t` across every semantic `Step`, respects its
boundary seed, and stays inside the universe. Nothing about fixpoints, nothing about representation. -/

variable {P : Program} {univ : List α} {t : MTC α} {sd : Std.HashSet α}

/-- Valid forward-must solution of the term `t`: it shrinks across every step by `evs t`, lies under the
    seed `sd` at the entry (the boundary ceiling), and stays within the universe. Any history ghost's
    `update`/`seed`/`bound` is (defeq to) this. -/
def MTCSpec (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ h c'.node, x ∈ MTC.evs (c.node, c'.node) t (h c.node)) ∧
  (∀ x ∈ h P.entry, x ∈ sd) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid forward-may solution: it grows across every step by `evs t` read at the edge source, contains
    `sd` at the `entry`, and stays within the universe. -/
def MTCSpecMF (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α)
    (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) t (h c.node), x ∈ h c'.node) ∧
  (∀ x ∈ sd, x ∈ h P.entry) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid backward-must solution: it shrinks into `evs t` read from every successor, stays under the
    per-node ceiling `hi` (the `check`), lies under the seed `sd` at every `halt`, and stays within the
    universe. -/
def MTCSpecBM (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ h c.node, x ∈ MTC.evs (c.node, c'.node) t (h c'.node)) ∧
  (∀ n, ∀ x ∈ h n, x ∈ hi n) ∧
  (∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ h c.node, x ∈ sd) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid backward-may solution of `t`: it grows across every step by `evs t` read at the tail from the
    successor's value, contains `lo` at every node (the `check` floor) and `sd` at every `halt`, and
    stays within the universe. -/
def MTCSpecB (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α) (sd : Std.HashSet α)
    (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) t (h c'.node), x ∈ h c.node) ∧
  (∀ n, ∀ x ∈ lo n, x ∈ h n) ∧
  (∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ sd, x ∈ h c.node) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid **doubly-clamped forward-must** solution of `t` (**cap-the-transfer**): the transfer that
    shrinks it across every step is relaxed *below* by the floor `lo` (so `h c'.node ⊆ evs t (h c.node) ∪
    lo c'.node`); it stays above the floor `lo` and under the ceiling `hi` at every node; the boundary
    ceiling `sd` at the entry is likewise relaxed by `lo`; and it stays within the universe. `lo = ∅` /
    `hi = univ` recover `MTCSpec`. Well-formed only under a non-empty band `lo ⊆ hi`. -/
def MTCSpecC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ h c'.node, x ∈ MTC.evs (c.node, c'.node) t (h c.node) ∨ x ∈ lo c'.node) ∧
  (∀ n, ∀ x ∈ lo n, x ∈ h n) ∧
  (∀ n, ∀ x ∈ h n, x ∈ hi n) ∧
  (∀ x ∈ h P.entry, x ∈ sd ∨ x ∈ lo P.entry) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid **doubly-clamped forward-may** solution of `t` (**cap-the-transfer**, the may dual of
    `MTCSpecC`): the transfer that grows it is capped *above* by the ceiling `hi` (only `evs ∩ hi` need
    land in `h`); it stays above the floor `lo` and under the ceiling `hi`; the boundary floor `sd` at the
    entry is likewise capped by `hi`; and it stays within the universe. `lo = ∅` / `hi = univ` recover
    `MTCSpecMF`. Well-formed only under a non-empty band `lo ⊆ hi`. -/
def MTCSpecMFC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) t (h c.node), x ∈ hi c'.node → x ∈ h c'.node) ∧
  (∀ n, ∀ x ∈ lo n, x ∈ h n) ∧
  (∀ n, ∀ x ∈ h n, x ∈ hi n) ∧
  (∀ x ∈ sd, x ∈ hi P.entry → x ∈ h P.entry) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid **doubly-clamped backward-must** solution of `t` (**cap-the-transfer**, the backward `MTCSpecC`
    with the boundary at `halt`): the transfer that shrinks it into `evs` read from every successor is
    relaxed *below* by the floor `lo`; it stays above `lo` and under the ceiling `hi`; the `halt`-boundary
    ceiling `sd` is likewise relaxed by `lo`; and it stays within the universe. `lo = ∅` recovers
    `MTCSpecBM`. Well-formed only under a non-empty band `lo ⊆ hi`. -/
def MTCSpecBMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ h c.node, x ∈ MTC.evs (c.node, c'.node) t (h c'.node) ∨ x ∈ lo c.node) ∧
  (∀ n, ∀ x ∈ lo n, x ∈ h n) ∧
  (∀ n, ∀ x ∈ h n, x ∈ hi n) ∧
  (∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ h c.node, x ∈ sd ∨ x ∈ lo c.node) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-- Valid **doubly-clamped backward-may** solution of `t` (**cap-the-transfer**, the backward `MTCSpecMFC`
    with the boundary at `halt`): the transfer that grows it (read at the tail from the successor) is
    capped *above* by the ceiling `hi`; it stays above the floor `lo` and under `hi`; the `halt`-boundary
    floor `sd` is likewise capped by `hi`; and it stays within the universe. `hi = univ` recovers
    `MTCSpecB`. Well-formed only under a non-empty band `lo ⊆ hi`. -/
def MTCSpecBC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (h : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) t (h c'.node), x ∈ hi c.node → x ∈ h c.node) ∧
  (∀ n, ∀ x ∈ lo n, x ∈ h n) ∧
  (∀ n, ∀ x ∈ h n, x ∈ hi n) ∧
  (∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ sd, x ∈ hi c.node → x ∈ h c.node) ∧
  (∀ n, ∀ x ∈ h n, x ∈ univ)

/-! ## Confluence vocabulary (set-level).

A **transfer variable** carries no node-local set and never reads itself: it is the meet / join of an
already-solved ghost `Y` over the realizable successors — a one-shot closed form, no fixpoint. (LCM's
`tauP`/`usedOut`.) Stated here over `Node → HashSet α`, with no reference to any representation:
`Solver.Impl`'s `MeetSpec`/`JoinSpec` are the same predicates with `Y` supplied as a bitvector field. -/

/-- Greatest meet-transfer: `τ(c) ⊆ Y(c')` across every step, bounded by the universe. -/
def MeetSpecS (P : Program) (univ : List α) (Y : Node → Std.HashSet α)
    (τ : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ τ c.node, x ∈ Y c'.node) ∧
  (∀ n, ∀ x ∈ τ n, x ∈ univ)

/-- Least join-transfer: `Y(c') ⊆ τ(c)` across every step, bounded by the universe. -/
def JoinSpecS (P : Program) (univ : List α) (Y : Node → Std.HashSet α)
    (τ : Node → Std.HashSet α) : Prop :=
  (∀ c c', Step P c c' → ∀ x ∈ Y c'.node, x ∈ τ c.node) ∧
  (∀ n, ∀ x ∈ τ n, x ∈ univ)

end Solver
