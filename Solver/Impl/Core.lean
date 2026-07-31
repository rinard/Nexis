-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.IR.Cfg

/-!
# `Solver.Impl.Core` — generic fixpoint dataflow primitives

Built on this repo's `BaseLanguage.Tac` IR and `IR.Cfg` graph helpers. Spec-agnostic: parameterized by a
transfer `g : Array (ESet n) → Node → ESet n`, so one engine serves every ghost the generator emits.

## Contents
- **Termination core.** `iterToFix` + `iterToFix_fixed`/`iterToFix_invariant`/`iterToFix_fixed'`:
  a strictly-decreasing measure on non-fixed points ⇒ enough fuel reaches a genuine fixpoint.
- **Bitvector subset toolkit.** `ESet n = BitVec n`, `Incl s t := s &&& ~~~t = 0`, with pointwise
  (`getLsbD`) reasoning, transitivity, and meet/join-membership lemmas.
- **Round operators.** `mustStep` (intersect-with-old, monotone *down* from ⊤) and `mayStep`
  (union-with-old, monotone *up* from ∅), with their total-`toNat` measures (`measM`/`measV`) and
  the strict-decrease lemmas (`measM_lt`/`measV_lt`).

Everything here is `sorry`-free, pure Lean 4 core (no Mathlib).
-/

namespace Solver

open BaseLanguage Tac Semantics

/-- The dataflow value: a bitvector over a fixed-width universe (subset lattice). -/
abbrev ESet (n : Nat) := BitVec n

/-- Subset inclusion as a bitvector identity: `s ⊆ t ↔ s ∖ t = ∅`. -/
def Incl {n : Nat} (s t : ESet n) : Prop := s &&& ~~~t = 0

/-! ## Generic fixpoint iteration with a decreasing measure -/

/-- Iterate `F` until it reaches a fixpoint or `fuel` runs out. Equality is tested directly
    (decidable), so on a fixpoint it returns immediately. -/
def iterToFix {S : Type} [DecidableEq S] (F : S → S) : Nat → S → S
  | 0,    x => x
  | k+1,  x => if F x = x then x else iterToFix F k (F x)

/-- If `F` strictly decreases a `Nat`-valued measure on every non-fixed point, then iterating
    from `x` with fuel exceeding `meas x` reaches an actual fixpoint of `F`. -/
theorem iterToFix_fixed {S : Type} [DecidableEq S] (F : S → S) (meas : S → Nat)
    (hdec : ∀ x, F x ≠ x → meas (F x) < meas x) :
    ∀ (fuel : Nat) (x : S), meas x < fuel → F (iterToFix F fuel x) = iterToFix F fuel x := by
  intro fuel
  induction fuel with
  | zero =>
      intro x hx
      exact absurd hx (Nat.not_lt_zero _)
  | succ k ih =>
      intro x hx
      unfold iterToFix
      by_cases hfix : F x = x
      · simp [hfix]
      · simp only [hfix, if_false]
        apply ih (F x)
        have hd := hdec x hfix
        omega

/-- Once `iterToFix` returns a fixpoint, applying `F` again is the identity. -/
theorem iterToFix_isFixedPoint {S : Type} [DecidableEq S] (F : S → S) (meas : S → Nat)
    (hdec : ∀ x, F x ≠ x → meas (F x) < meas x) (x : S) :
    F (iterToFix F (meas x + 1) x) = iterToFix F (meas x + 1) x :=
  iterToFix_fixed F meas hdec (meas x + 1) x (Nat.lt_succ_self _)

/-- Sanity: counting down to the fixpoint `0`. -/
example : iterToFix (fun n : Nat => n - 1) 10 5 = 0 := by native_decide

variable {n : Nat}

/-! ## Bitvector subset toolkit (pointwise `getLsbD`) -/

theorem incl_iff {s t : ESet n} : Incl s t ↔ ∀ i, s.getLsbD i = true → t.getLsbD i = true := by
  unfold Incl
  constructor
  · intro h i hs
    have hz : (s &&& ~~~t).getLsbD i = false := by
      rw [h]
      simp
    have hi : i < n := BitVec.lt_of_getLsbD hs
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hs, hi, decide_true,
      Bool.true_and] at hz
    simpa using hz
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, hi, decide_true,
      Bool.true_and]
    by_cases hs : s.getLsbD i = true
    · simp [h i hs]
    · have hsf : s.getLsbD i = false := by
        cases hh : s.getLsbD i
        · rfl
        · exact absurd hh hs
      simp [hsf]

theorem incl_refl (s : ESet n) : Incl s s := incl_iff.mpr (fun _ h => h)

theorem incl_trans {s t u : ESet n} (h1 : Incl s t) (h2 : Incl t u) : Incl s u :=
  incl_iff.mpr (fun i hi => incl_iff.mp h2 i (incl_iff.mp h1 i hi))

theorem incl_zero {t : ESet n} : Incl (0 : ESet n) t :=
  incl_iff.mpr (by intro i hi; simp [BitVec.getLsbD_zero] at hi)

/-! ## State, getters, meet/join over node lists -/

/-- Array getter with default ∅ (so it is total in the node). -/
def gA (a : Array (ESet n)) (nd : Node) : ESet n := a[nd]?.getD 0

/-- All-ones (⊤ of the subset lattice). -/
def topV (n : Nat) : ESet n := ~~~(0 : BitVec n)

/-- Meet (∩) of `f` over a list of nodes; empty meet = ⊤. -/
def meetList (f : Node → ESet n) : List Node → ESet n
  | []      => topV n
  | x :: xs => f x &&& meetList f xs

/-- Join (∪) of `f` over a list of nodes; empty join = ∅. -/
def joinList (f : Node → ESet n) : List Node → ESet n
  | []      => 0
  | x :: xs => f x ||| joinList f xs

/-- The meet is below every member. -/
theorem meetList_sub_mem (f : Node → ESet n) {x : Node} {xs : List Node}
    (hx : x ∈ xs) : Incl (meetList f xs) (f x) := by
  induction xs with
  | nil => exact absurd hx (by simp)
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst h
        apply incl_iff.mpr
        intro i hi
        simp only [meetList, BitVec.getLsbD_and, Bool.and_eq_true] at hi
        exact hi.1
      · apply incl_iff.mpr
        intro i hi
        simp only [meetList, BitVec.getLsbD_and, Bool.and_eq_true] at hi
        exact incl_iff.mp (ih h) i hi.2

/-- Every member is below the join. -/
theorem joinList_mem_sub (f : Node → ESet n) {x : Node} {xs : List Node}
    (hx : x ∈ xs) : Incl (f x) (joinList f xs) := by
  induction xs with
  | nil => exact absurd hx (by simp)
  | cons y ys ih =>
      rcases List.mem_cons.mp hx with h | h
      · subst h
        apply incl_iff.mpr
        intro i hi
        simp only [joinList, BitVec.getLsbD_or, Bool.or_eq_true]
        exact Or.inl hi
      · apply incl_iff.mpr
        intro i hi
        simp only [joinList, BitVec.getLsbD_or, Bool.or_eq_true]
        exact Or.inr (incl_iff.mp (ih h) i hi)

/-- Union distributes over intersection. -/
theorem or_and_distrib (a b c : ESet n) : a ||| (b &&& c) = (a ||| b) &&& (a ||| c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- `⊤` absorbs union. -/
theorem or_topV (a : ESet n) : a ||| topV n = topV n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp [BitVec.getLsbD_or, topV, BitVec.getLsbD_not, hi]

/-- Union distributes over a meet-list (de Morgan-style factoring). -/
theorem or_meetList (a : ESet n) (f : Node → ESet n) :
    ∀ xs, a ||| meetList f xs = meetList (fun m => a ||| f m) xs
  | [] => or_topV a
  | x :: xs => by
    simp only [meetList]
    rw [or_and_distrib, or_meetList a f xs]

/-- Intersection distributes over union (the `&&&`-over-`|||` dual of `or_and_distrib`). -/
theorem and_or_distrib (a b c : ESet n) : a &&& (b ||| c) = (a &&& b) ||| (a &&& c) := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.getLsbD i <;> rfl

/-- `∅` absorbs intersection. -/
theorem and_zero (a : ESet n) : a &&& (0 : ESet n) = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i _; simp

/-- Intersection distributes over a join-list (the `&&&`-over-`|||` dual of `or_meetList`). -/
theorem and_joinList (a : ESet n) (f : Node → ESet n) :
    ∀ xs, a &&& joinList f xs = joinList (fun m => a &&& f m) xs
  | [] => and_zero a
  | x :: xs => by
    simp only [joinList]
    rw [and_or_distrib, and_joinList a f xs]

theorem incl_or_inl (a b : ESet n) : Incl a (a ||| b) := by
  apply incl_iff.mpr; intro i hi; rw [BitVec.getLsbD_or, hi, Bool.true_or]

theorem incl_or_inr (a b : ESet n) : Incl b (a ||| b) := by
  apply incl_iff.mpr; intro i hi; rw [BitVec.getLsbD_or, hi, Bool.or_true]

/-- A fixpoint of an intersect step `R = R ∩ M` is below the constraint `M`. -/
theorem incl_of_and_eq {R M : ESet n} (h : R = R &&& M) : Incl R M := by
  apply incl_iff.mpr
  intro i hi
  rw [h] at hi
  simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hi
  exact hi.2

/-- A fixpoint of a union step `R = R ∪ M` is above the contribution `M`. -/
theorem incl_of_or_eq {R M : ESet n} (h : R = R ||| M) : Incl M R := by
  apply incl_iff.mpr
  intro i hi
  rw [h]
  simp only [BitVec.getLsbD_or, Bool.or_eq_true]
  exact Or.inr hi

/-! ## Generic must/may round operators (intersect/union-with-old → monotone) -/

/-- One must round: `arr[nd] ↦ arr[nd] ∩ g arr nd` (so the result is pointwise ⊆ `arr`). -/
def mustStep (P : Program) (g : Array (ESet n) → Node → ESet n) (arr : Array (ESet n)) :
    Array (ESet n) :=
  Array.ofFn (n := P.size) (fun i => gA arr i.val &&& g arr i.val)

/-- One may round: `arr[nd] ↦ arr[nd] ∪ g arr nd` (so the result is pointwise ⊇ `arr`). -/
def mayStep (P : Program) (g : Array (ESet n) → Node → ESet n) (arr : Array (ESet n)) :
    Array (ESet n) :=
  Array.ofFn (n := P.size) (fun i => gA arr i.val ||| g arr i.val)

/-! ## Invariant-aware fixpoint combinator -/

/-- Any invariant preserved by `F` survives the iteration. -/
theorem iterToFix_invariant {S : Type} [DecidableEq S] (F : S → S) (Inv : S → Prop)
    (hInv : ∀ x, Inv x → Inv (F x)) :
    ∀ (fuel : Nat) (x : S), Inv x → Inv (iterToFix F fuel x) := by
  intro fuel
  induction fuel with
  | zero => intro x hx; exact hx
  | succ k ih =>
      intro x hx
      unfold iterToFix
      by_cases h : F x = x
      · simpa [h] using hx
      · simp only [h, if_false]
        exact ih (F x) (hInv x hx)

/-- Like `iterToFix_fixed`, but the decreasing-measure hypothesis only needs to hold on states
    satisfying an `F`-stable invariant `Inv`. -/
theorem iterToFix_fixed' {S : Type} [DecidableEq S] (F : S → S) (Inv : S → Prop) (meas : S → Nat)
    (hInv : ∀ x, Inv x → Inv (F x))
    (hdec : ∀ x, Inv x → F x ≠ x → meas (F x) < meas x) :
    ∀ (fuel : Nat) (x : S), Inv x → meas x < fuel →
      F (iterToFix F fuel x) = iterToFix F fuel x := by
  intro fuel
  induction fuel with
  | zero => intro x _ hx; exact absurd hx (Nat.not_lt_zero _)
  | succ k ih =>
      intro x hInvx hx
      unfold iterToFix
      by_cases hfix : F x = x
      · simp [hfix]
      · simp only [hfix, if_false]
        apply ih (F x) (hInv x hInvx)
        have hd := hdec x hInvx hfix
        omega

/-! ## Measures (over the fixed node range, so both sides map the same list) -/

def sumN : List Nat → Nat := List.foldr (· + ·) 0

theorem sumN_map_le {α} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    sumN (xs.map f) ≤ sumN (xs.map g) := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons y ys ih =>
      simp only [List.map_cons, sumN, List.foldr_cons]
      exact Nat.add_le_add (h y (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem sumN_map_lt {α} (xs : List α) (f g : α → Nat) (h : ∀ x ∈ xs, f x ≤ g x)
    {x0 : α} (hx0 : x0 ∈ xs) (hlt : f x0 < g x0) :
    sumN (xs.map f) < sumN (xs.map g) := by
  induction xs with
  | nil => exact absurd hx0 (by simp)
  | cons y ys ih =>
      simp only [List.map_cons, sumN, List.foldr_cons]
      rcases List.mem_cons.mp hx0 with hxy | hxys
      · subst hxy
        exact Nat.add_lt_add_of_lt_of_le hlt (sumN_map_le ys f g (fun x hx => h x (by simp [hx])))
      · exact Nat.add_lt_add_of_le_of_lt (h y (by simp))
          (ih (fun x hx => h x (by simp [hx])) hxys)

/-- Must measure: total `toNat` over the node range (decreases as bits clear). -/
def measM (P : Program) (arr : Array (ESet n)) : Nat :=
  sumN ((List.range P.size).map (fun nd => (gA arr nd).toNat))

/-- May measure: total complement `toNat` (decreases as bits set). -/
def measV (P : Program) (arr : Array (ESet n)) : Nat :=
  sumN ((List.range P.size).map (fun nd => (~~~ gA arr nd).toNat))

/-! ## Getter / step algebra -/

theorem gA_lt {arr : Array (ESet n)} {nd : Node} (h : nd < arr.size) : gA arr nd = arr[nd] := by
  unfold gA
  rw [Array.getElem?_eq_getElem h]
  rfl

/-- Out of range, the getter is the empty set (its default). -/
theorem gA_ge {arr : Array (ESet n)} {nd : Node} (h : ¬ nd < arr.size) : gA arr nd = 0 := by
  unfold gA
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)]
  rfl

theorem gA_ofFn {P : Program} (f : Fin P.size → ESet n) {nd : Node} (h : nd < P.size) :
    gA (Array.ofFn f) nd = f ⟨nd, h⟩ := by
  have hsz : nd < (Array.ofFn f).size := by
    rw [Array.size_ofFn]
    exact h
  rw [gA_lt hsz, Array.getElem_ofFn]

theorem mustStep_size (P : Program) (g) (arr : Array (ESet n)) :
    (mustStep P g arr).size = P.size := by
  unfold mustStep
  exact Array.size_ofFn

theorem mayStep_size (P : Program) (g) (arr : Array (ESet n)) :
    (mayStep P g arr).size = P.size := by
  unfold mayStep
  exact Array.size_ofFn

theorem gA_step_must {P : Program} {g} {arr : Array (ESet n)} {nd : Node} (h : nd < P.size) :
    gA (mustStep P g arr) nd = gA arr nd &&& g arr nd := by
  unfold mustStep
  exact gA_ofFn _ h

theorem gA_step_may {P : Program} {g} {arr : Array (ESet n)} {nd : Node} (h : nd < P.size) :
    gA (mayStep P g arr) nd = gA arr nd ||| g arr nd := by
  unfold mayStep
  exact gA_ofFn _ h

theorem toNat_and_le (a b : ESet n) : (a &&& b).toNat ≤ a.toNat := by
  rw [BitVec.toNat_and]
  exact Nat.and_le_left

theorem toNat_lt_of_le_ne {a b : ESet n} (hle : a.toNat ≤ b.toNat) (hne : a ≠ b) :
    a.toNat < b.toNat := by
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · exact absurd (BitVec.toNat_inj.mp h) hne

/-- Two equal-size, distinct arrays differ at some in-range index. -/
theorem array_ne_exists {α} {arr1 arr2 : Array α} (hsz : arr1.size = arr2.size)
    (hne : arr1 ≠ arr2) :
    ∃ nd, ∃ (_ : nd < arr1.size) (_ : nd < arr2.size), arr1[nd] ≠ arr2[nd] :=
  Classical.byContradiction (fun hcon =>
    hne (by
      rw [Array.ext_iff]
      refine ⟨hsz, ?_⟩
      intro i h1 h2
      exact Classical.byContradiction (fun hd => hcon ⟨i, h1, h2, hd⟩)))

/-! ## Measure strictly decreases on a genuine change -/

theorem measM_lt {P : Program} {g} {arr : Array (ESet n)} (hInv : arr.size = P.size)
    (hne : mustStep P g arr ≠ arr) : measM P (mustStep P g arr) < measM P arr := by
  have hle : ∀ nd ∈ List.range P.size,
      (gA (mustStep P g arr) nd).toNat ≤ (gA arr nd).toNat := by
    intro nd hnd
    rw [List.mem_range] at hnd
    rw [gA_step_must hnd]
    exact toNat_and_le _ _
  obtain ⟨nd, h1, h2, hdiff⟩ :=
    array_ne_exists (by rw [mustStep_size, hInv]) hne
  have hndlt : nd < P.size := by
    rw [← hInv]
    exact h2
  have hstrict : (gA (mustStep P g arr) nd).toNat < (gA arr nd).toNat := by
    apply toNat_lt_of_le_ne (hle nd (List.mem_range.mpr hndlt))
    rw [gA_lt h1, gA_lt h2]
    exact hdiff
  exact sumN_map_lt _ _ _ hle (List.mem_range.mpr hndlt) hstrict

theorem measV_lt {P : Program} {g} {arr : Array (ESet n)} (hInv : arr.size = P.size)
    (hne : mayStep P g arr ≠ arr) : measV P (mayStep P g arr) < measV P arr := by
  have hle : ∀ nd ∈ List.range P.size,
      (~~~ gA (mayStep P g arr) nd).toNat ≤ (~~~ gA arr nd).toNat := by
    intro nd hnd
    rw [List.mem_range] at hnd
    rw [gA_step_may hnd, BitVec.not_or]
    exact toNat_and_le _ _
  obtain ⟨nd, h1, h2, hdiff⟩ :=
    array_ne_exists (by rw [mayStep_size, hInv]) hne
  have hndlt : nd < P.size := by
    rw [← hInv]
    exact h2
  have hstrict : (~~~ gA (mayStep P g arr) nd).toNat < (~~~ gA arr nd).toNat := by
    apply toNat_lt_of_le_ne (hle nd (List.mem_range.mpr hndlt))
    intro hcon
    apply hdiff
    have : gA (mayStep P g arr) nd = gA arr nd := by
      have := congrArg (~~~ ·) hcon
      simpa [BitVec.not_not] using this
    rw [gA_lt h1, gA_lt h2] at this
    exact this
  exact sumN_map_lt _ _ _ hle (List.mem_range.mpr hndlt) hstrict

/-! ## `Incl` monotonicity under `&&&`/`|||` (shared worklist-step helpers). -/

theorem incl_and_mono {n : Nat} {a a' b b' : ESet n} (ha : Incl a a') (hb : Incl b b') :
    Incl (a &&& b) (a' &&& b') := by
  apply incl_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_and, Bool.and_eq_true] at hi ⊢
  exact ⟨incl_iff.mp ha i hi.1, incl_iff.mp hb i hi.2⟩

theorem incl_or_mono {n : Nat} {a a' b b' : ESet n} (ha : Incl a a') (hb : Incl b b') :
    Incl (a ||| b) (a' ||| b') := by
  apply incl_iff.mpr
  intro i hi
  simp only [BitVec.getLsbD_or, Bool.or_eq_true] at hi ⊢
  exact hi.imp (incl_iff.mp ha i) (incl_iff.mp hb i)

end Solver
