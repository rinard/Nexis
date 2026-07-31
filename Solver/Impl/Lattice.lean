-- Copyright (c) 2026 Martin Rinard
import Solver.Impl.Core
import Std.Data.HashSet

/-!
# `Solver.Impl.Lattice` — the `ESet ↔ HashSet` decode bridge

The solver works on bitvectors (`ESet n = BitVec n`); the ghost predicates are stated over
`HashSet` sets (`Assignments`/`Variables`) via membership (`Assignments.Subset`, `Assignments.union`, …). This module decodes a
bitvector to the `HashSet` it represents over a universe list, and proves the **membership
homomorphism**: `decode` turns `|||`/`&&&`/`&&& ~~~` into set union/inter/diff (at the membership
level — never `HashSet` equality, which is representation-sensitive), and `Incl` into `⊆`.

The `&&&`/`&&& ~~~` (inter/diff) homomorphisms and the `Subset ⇒ Incl` direction need the universe to be
duplicate-free (`Nodup`) — true for `(allExprs P).toList` etc., since the universes are `HashSet`s.
Everything is generic over the element type, instantiated per analysis by the generator.
-/

namespace Solver

open BaseLanguage Std

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-- Decode a bitvector to the set of universe elements whose bit is set. Bit `i` ↔ `univ[i]`. -/
def decode (univ : List α) {w : Nat} (bv : BitVec w) : Std.HashSet α :=
  Std.HashSet.ofList (univ.zipIdx.filterMap (fun p => if bv.getLsbD p.2 then some p.1 else none))

/-- Membership in a decoded set: `a` is present iff some universe slot holding `a` has its bit set. -/
theorem mem_decode {univ : List α} {w : Nat} {bv : BitVec w} {a : α} :
    a ∈ decode univ bv ↔ ∃ p ∈ univ.zipIdx, bv.getLsbD p.2 = true ∧ p.1 = a := by
  unfold decode
  rw [Std.HashSet.mem_ofList, List.contains_iff_mem, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, hg⟩
    by_cases hb : bv.getLsbD p.2 = true
    · rw [if_pos hb] at hg; exact ⟨p, hp, hb, Option.some.inj hg⟩
    · rw [if_neg hb] at hg; exact absurd hg (by simp)
  · rintro ⟨p, hp, hb, ha⟩
    exact ⟨p, hp, by rw [if_pos hb, ha]⟩

omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] in
/-- In a `Nodup` universe, a zipIdx pair's element pins down its index. -/
theorem zipIdx_fst_inj {univ : List α} (hnd : univ.Nodup) {p q : α × Nat}
    (hp : p ∈ univ.zipIdx) (hq : q ∈ univ.zipIdx) (h : p.1 = q.1) : p = q := by
  obtain ⟨hpge, hpe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hp)
  obtain ⟨hqge, hqe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
  -- hpe : univ[p.2] = p.1, hqe : univ[q.2] = q.1 ⇒ equal elements ⇒ equal indices (Nodup)
  have hidx : p.2 = q.2 := (List.getElem_inj hnd).mp (by rw [hpe, hqe, h])
  exact Prod.ext h hidx

/-! ## Encoding (the inverse, for lifting a valid set family to a bitvector post-fixpoint) -/

/-- Encode a set to the bitvector marking which universe slots hold its elements. -/
def encode (univ : List α) (S : Std.HashSet α) : BitVec univ.length :=
  BitVec.cast (List.length_map _) (BitVec.ofBoolListLE (univ.map (fun x => decide (x ∈ S))))

omit [LawfulBEq α] [LawfulHashable α] in
theorem getLsbD_encode {univ : List α} {S : Std.HashSet α} {i : Nat} (hi : i < univ.length) :
    (encode univ S).getLsbD i = decide (univ[i] ∈ S) := by
  unfold encode
  rw [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE]
  have hbs : i < (univ.map (fun x => decide (x ∈ S))).length := by rw [List.length_map]; exact hi
  rw [show (univ.map (fun x => decide (x ∈ S))).getD i false
        = (univ.map (fun x => decide (x ∈ S)))[i] from (List.getElem_eq_getD false).symm,
     List.getElem_map]

omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] in
/-- `x ∈ univ` iff some zipIdx slot holds it. -/
theorem mem_iff_exists_zipIdx {univ : List α} {x : α} :
    x ∈ univ ↔ ∃ p ∈ univ.zipIdx, p.1 = x := by
  constructor
  · intro hx
    obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hx
    exact ⟨(univ[i], i), List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), hgi⟩
  · rintro ⟨p, hp, hpx⟩
    obtain ⟨hplt, hpe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hp)
    rw [← hpx, ← hpe]; exact List.getElem_mem hplt

/-- Everything a `decode` yields lies in the universe (the decode is always a subset of `univ`). -/
theorem mem_decode_mem_univ {univ : List α} {w : Nat} {bv : BitVec w} {x : α}
    (hx : x ∈ decode univ bv) : x ∈ univ := by
  rw [mem_decode] at hx
  obtain ⟨q, hq, _, hqx⟩ := hx
  exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

/-- **Round trip.** Decoding an encoded set recovers exactly its universe-elements. -/
theorem mem_decode_encode {univ : List α} {S : Std.HashSet α} {x : α} :
    x ∈ decode univ (encode univ S) ↔ x ∈ S ∧ x ∈ univ := by
  rw [mem_decode]
  constructor
  · rintro ⟨p, hp, hbit, hpx⟩
    obtain ⟨hplt, hpe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hp)
    rw [getLsbD_encode hplt, decide_eq_true_eq] at hbit
    rw [hpe] at hbit
    exact ⟨hpx ▸ hbit, hpx ▸ (hpe ▸ List.getElem_mem hplt)⟩
  · rintro ⟨hxS, hxu⟩
    obtain ⟨p, hp, hpx⟩ := mem_iff_exists_zipIdx.mp hxu
    obtain ⟨hplt, hpe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hp)
    refine ⟨p, hp, ?_, hpx⟩
    rw [getLsbD_encode hplt, decide_eq_true_eq, hpe, hpx]; exact hxS

/-- With `S ⊆ univ`, decode∘encode is the identity (membership-wise). -/
theorem mem_decode_encode_of_sub {univ : List α} {S : Std.HashSet α}
    (hsub : ∀ y ∈ S, y ∈ univ) {x : α} : x ∈ decode univ (encode univ S) ↔ x ∈ S := by
  rw [mem_decode_encode]
  exact ⟨fun h => h.1, fun h => ⟨h, hsub x h⟩⟩

/-! ## Membership homomorphisms -/

/-- `decode (a ||| b)` is the union (membership-wise). No `Nodup` needed. -/
theorem mem_decode_or {univ : List α} {w : Nat} {a b : BitVec w} {x : α} :
    x ∈ decode univ (a ||| b) ↔ x ∈ decode univ a ∨ x ∈ decode univ b := by
  rw [mem_decode, mem_decode, mem_decode]
  constructor
  · rintro ⟨p, hp, hbit, hx⟩
    rw [BitVec.getLsbD_or, Bool.or_eq_true] at hbit
    rcases hbit with h | h
    · exact Or.inl ⟨p, hp, h, hx⟩
    · exact Or.inr ⟨p, hp, h, hx⟩
  · rintro (⟨p, hp, h, hx⟩ | ⟨p, hp, h, hx⟩)
    · exact ⟨p, hp, by rw [BitVec.getLsbD_or, h, Bool.true_or], hx⟩
    · exact ⟨p, hp, by rw [BitVec.getLsbD_or, h, Bool.or_true], hx⟩

/-- `decode (a &&& b)` is the intersection (membership-wise). Needs a `Nodup` universe. -/
theorem mem_decode_and {univ : List α} (hnd : univ.Nodup) {w : Nat} {a b : BitVec w} {x : α} :
    x ∈ decode univ (a &&& b) ↔ x ∈ decode univ a ∧ x ∈ decode univ b := by
  rw [mem_decode, mem_decode, mem_decode]
  constructor
  · rintro ⟨p, hp, hbit, hx⟩
    rw [BitVec.getLsbD_and, Bool.and_eq_true] at hbit
    exact ⟨⟨p, hp, hbit.1, hx⟩, ⟨p, hp, hbit.2, hx⟩⟩
  · rintro ⟨⟨p, hp, ha, hxp⟩, ⟨q, hq, hb, hxq⟩⟩
    have hpq : p = q := zipIdx_fst_inj hnd hp hq (by rw [hxp, hxq])
    refine ⟨q, hq, ?_, hxq⟩
    have ha' : a.getLsbD q.snd = true := hpq ▸ ha
    simp [BitVec.getLsbD_and, ha', hb]

/-- `decode (a &&& ~~~b)` is the difference (membership-wise). Needs a `Nodup` universe. -/
theorem mem_decode_diff {univ : List α} (hnd : univ.Nodup) {w : Nat} {a b : BitVec w} {x : α} :
    x ∈ decode univ (a &&& ~~~b) ↔ x ∈ decode univ a ∧ x ∉ decode univ b := by
  rw [mem_decode, mem_decode, mem_decode]
  constructor
  · rintro ⟨p, hp, hbit, hx⟩
    rw [BitVec.getLsbD_and, Bool.and_eq_true, BitVec.getLsbD_not, Bool.and_eq_true] at hbit
    obtain ⟨ha, _, hnb⟩ := hbit
    refine ⟨⟨p, hp, ha, hx⟩, ?_⟩
    rintro ⟨q, hq, hb, hxq⟩
    have hpq : p = q := zipIdx_fst_inj hnd hp hq (by rw [hx, hxq])
    rw [hpq, hb] at hnb; simp at hnb
  · rintro ⟨⟨p, hp, ha, hx⟩, hnotb⟩
    have hpw : p.2 < w := BitVec.lt_of_getLsbD ha
    have hnb : b.getLsbD p.2 = false := by
      cases hbb : b.getLsbD p.2 with
      | false => rfl
      | true => exact absurd ⟨p, hp, hbb, hx⟩ hnotb
    refine ⟨p, hp, ?_, hx⟩
    rw [BitVec.getLsbD_and, ha, BitVec.getLsbD_not, hnb]
    simp [hpw]

/-! ## `Incl ↔ Subset` (membership inclusion) -/

/-- A universe slot's element is decoded exactly when its bit is set. -/
theorem getElem_mem_decode {univ : List α} {w : Nat} {bv : BitVec w} {i : Nat}
    (hi : i < univ.length) (hb : bv.getLsbD i = true) : univ[i] ∈ decode univ bv := by
  rw [mem_decode]
  exact ⟨(univ[i], i), List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi), hb, rfl⟩

/-- If a set's elements are all decoded by `X`, its encoding is `⊆ X`. (For lifting a valid family to a
    bitvector pre/post-fixpoint in the transfer-variable extremality argument.) -/
theorem encode_incl_decode {univ : List α} (hnd : univ.Nodup) {S : Std.HashSet α}
    {X : BitVec univ.length} (h : ∀ y ∈ S, y ∈ decode univ X) : Incl (encode univ S) X := by
  apply incl_iff.mpr
  intro i hi
  have hilt : i < univ.length := BitVec.lt_of_getLsbD hi
  rw [getLsbD_encode hilt, decide_eq_true_eq] at hi
  obtain ⟨q, hq, hb, hqx⟩ := mem_decode.mp (h univ[i] hi)
  obtain ⟨_, hqe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
  have hidx : q.2 = i := (List.getElem_inj hnd).mp (hqe.trans hqx)
  rw [← hidx]; exact hb

/-- Dual: if everything `X` decodes is in `S`, then `X ⊆ encode S`. -/
theorem incl_decode_encode {univ : List α} {S : Std.HashSet α} {X : BitVec univ.length}
    (h : ∀ y ∈ decode univ X, y ∈ S) : Incl X (encode univ S) := by
  apply incl_iff.mpr
  intro i hi
  have hilt : i < univ.length := BitVec.lt_of_getLsbD hi
  rw [getLsbD_encode hilt, decide_eq_true_eq]
  exact h univ[i] (getElem_mem_decode hilt hi)

/-- `Incl` on bitvectors corresponds to membership-inclusion of their decodes. The `⇐` direction needs
    the bitvector width to match the universe and the universe to be `Nodup`. -/
theorem incl_iff_sub {univ : List α} {a b : BitVec univ.length} (hnd : univ.Nodup) :
    Incl a b ↔ ∀ x ∈ decode univ a, x ∈ decode univ b := by
  constructor
  · intro hincl x hx
    rw [mem_decode] at hx ⊢
    obtain ⟨p, hp, hbit, hxp⟩ := hx
    exact ⟨p, hp, incl_iff.mp hincl p.2 hbit, hxp⟩
  · intro hsub
    rw [incl_iff]
    intro i hai
    have hilt : i < univ.length := BitVec.lt_of_getLsbD hai
    have hmem : univ[i] ∈ decode univ a := getElem_mem_decode hilt hai
    obtain ⟨q, hq, hbit, hxq⟩ := mem_decode.mp (hsub univ[i] hmem)
    obtain ⟨hqlt, hqe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
    have hidx : q.2 = i := (List.getElem_inj hnd).mp (hqe.trans hxq)
    rw [← hidx]; exact hbit

/-! ## The membership gate (`gatedRhs`): a monotone, non-pure-set transfer -/

theorem eq_zero_iff {w : Nat} (B : BitVec w) : B = 0 ↔ ∀ i, B.getLsbD i = false := by
  constructor
  · intro h i; simp [h]
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro i _; simp [h i]

theorem ne_zero_iff {w : Nat} (B : BitVec w) : B ≠ 0 ↔ ∃ i, B.getLsbD i = true := by
  constructor
  · intro h
    rcases Classical.em (∃ i, B.getLsbD i = true) with hex | hnex
    · exact hex
    · exact absurd ((eq_zero_iff B).mpr (fun i => by
        cases hb : B.getLsbD i
        · rfl
        · exact absurd ⟨i, hb⟩ hnex)) h
  · rintro ⟨i, hi⟩ heq; simp [heq] at hi

/-- A decode is nonempty iff its bitvector is nonzero. -/
theorem decode_nonempty_iff {univ : List α} {B : BitVec univ.length} :
    (∃ y, y ∈ decode univ B) ↔ B ≠ 0 := by
  rw [ne_zero_iff]
  constructor
  · rintro ⟨y, hy⟩; rw [mem_decode] at hy; obtain ⟨p, _, hb, _⟩ := hy; exact ⟨p.2, hb⟩
  · rintro ⟨i, hi⟩
    have hilt := BitVec.lt_of_getLsbD hi
    exact ⟨univ[i], getElem_mem_decode hilt hi⟩

/-- Two decodes overlap iff their bitvectors share a bit. -/
theorem overlap_iff_and_ne_zero {univ : List α} (hnd : univ.Nodup) {L sng : BitVec univ.length} :
    (∃ y, y ∈ decode univ L ∧ y ∈ decode univ sng) ↔ L &&& sng ≠ 0 := by
  rw [← decode_nonempty_iff]
  constructor
  · rintro ⟨y, hyL, hyS⟩; exact ⟨y, (mem_decode_and hnd).mpr ⟨hyL, hyS⟩⟩
  · rintro ⟨y, hy⟩; obtain ⟨hyL, hyS⟩ := (mem_decode_and hnd).mp hy; exact ⟨y, hyL, hyS⟩

/-- The **gate**: `res` when `L` overlaps `sng` (the gate fires), else `∅`. Monotone in `L`. -/
def gate {w : Nat} (sng res L : BitVec w) : BitVec w := if L &&& sng = 0 then 0 else res

omit [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α] in
theorem gate_mono {w : Nat} {sng res L L' : BitVec w} (h : Incl L L') :
    Incl (gate sng res L) (gate sng res L') := by
  unfold gate
  by_cases hL : L &&& sng = 0
  · rw [if_pos hL]; exact incl_zero
  · have hL' : L' &&& sng ≠ 0 := by
      obtain ⟨i, hi⟩ := (ne_zero_iff _).mp hL
      rw [BitVec.getLsbD_and, Bool.and_eq_true] at hi
      exact (ne_zero_iff _).mpr ⟨i, by simp [BitVec.getLsbD_and, incl_iff.mp h i hi.1, hi.2]⟩
    rw [if_neg hL, if_neg hL']; exact incl_refl _

/-- The gate's decode is exactly `gatedRhs`'s shape: `res` if the gate-element is present, else `∅`. -/
theorem mem_decode_gate {univ : List α} (hnd : univ.Nodup) {sng res L : BitVec univ.length} {x : α} :
    x ∈ decode univ (gate sng res L) ↔
      (∃ y, y ∈ decode univ L ∧ y ∈ decode univ sng) ∧ x ∈ decode univ res := by
  unfold gate
  by_cases hL : L &&& sng = 0
  · rw [if_pos hL]
    constructor
    · intro hx; rw [mem_decode] at hx; obtain ⟨p, _, hb, _⟩ := hx; simp at hb
    · rintro ⟨hov, _⟩; exact absurd hL ((overlap_iff_and_ne_zero hnd).mp hov)
  · rw [if_neg hL]
    have hov : ∃ y, y ∈ decode univ L ∧ y ∈ decode univ sng := (overlap_iff_and_ne_zero hnd).mpr hL
    exact ⟨fun hx => ⟨hov, hx⟩, fun h => h.2⟩

end Solver
