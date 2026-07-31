-- Copyright (c) 2026 Martin Rinard
import Solver.Spec
import Solver.Impl.Worklist
import Solver.Impl.Graph
import Solver.Impl.Lattice
import Solver.Impl.Transfer
import BaseLanguage.Analysis.SetOps

/-!
# `Solver.Impl.Term` — the **Monotone Transfer Calculus** (MTC)

A first-class datatype `MTC` for the per-edge transfer function of a ghost variable, denoted at **both**
the bitvector level (`evb`, what the solver runs) and the set level (`evs`, what the ghost
predicate reads), with the three structural lemmas proved **once by induction**:

* `evb_mono`   — every term is monotone in the incoming value (⇒ the engine's `GMono` for free);
* `evb_decode` — `decode (evb t bv) = evs t (decode bv)` (the spec bridge, `_iff_spec`, structurally);
* `evs_sub`    — the set transfer stays inside the universe (the `bound`/`_sub` obligation).

Constructors: the pointwise core (`var`/`const`/`∪`/`∩`/`∖const`) plus three cross-element atoms —
`gate` (guarded, faint-liveness shape), `image` (OR-gather / relational image), and `gather`
(AND-gather / universal preimage). With `∪`/`∩` these reach **every monotone transfer over a finite
universe** (monotone DNF/CNF). Each atom cost exactly one case in each induction (the extension
contract). Direction (pred/succ) and extremality (may/must) are solver parameters, not part of the term.

All **four quadrants** are provided as generic verticals over the same `MTC` and the same four structural
lemmas — each a packaged `res*_correct` (valid ∧ extremal), instantiated per analysis with that ghost's
transfer term and *no* per-analysis proof:

| quadrant        | vertical    | engine  | neighbors | boundary  | example              |
|-----------------|-------------|---------|-----------|-----------|----------------------|
| forward-must    | `resMTC`     | meet ⊤  | pred      | sd @entry | available exprs      |
| backward-may    | `resMTCB`    | join ∅  | succ      | sd @halt  | liveness             |
| backward-must   | `resMTCBM`   | meet ⊤  | succ      | sd @halt  | very-busy/anticipated|
| forward-may     | `resMTCMF`   | join ∅  | pred      | sd @entry | reaching definitions |
-/

namespace Solver

open BaseLanguage BaseLanguage.Analysis Tac Semantics Std

/-! ## Reader-range lemmas (the worklist's realizable neighbors stay in `[0, P.size)` — the sole
    dependency the MTC verticals have on the concrete `realizableSucc`/`realizablePred` graph). -/

theorem realizableSucc_readers_in_range {P : Program} (hwf : WellFormed P) (nd : Node) :
    ∀ m ∈ (readersOf P realizableSucc)[nd]?.getD ([] : List Node), m < P.size := by
  by_cases h : nd < P.size
  · rw [readersOf_get h]; intro m hm; exact realizableSucc_lt hwf hm
  · rw [readersOf_get_oob h]; simp

theorem realizablePred_readers_in_range {P : Program} (nd : Node) :
    ∀ m ∈ (readersOf P realizablePred)[nd]?.getD ([] : List Node), m < P.size := by
  by_cases h : nd < P.size
  · rw [readersOf_get h]; intro m hm; exact (mem_realizablePred.mp hm).1
  · rw [readersOf_get_oob h]; simp

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]


namespace MTC


/-! Bitvector helpers: `decode`/`encode` are monotone (no `Nodup` needed). -/
omit [LawfulHashable α] in
theorem decode_mono {univ : List α} {a b : ESet univ.length} (h : Incl a b) :
    SetOps.Subset (decode univ a) (decode univ b) := by
  intro x hx; rw [mem_decode] at hx ⊢; obtain ⟨q, hq, hbit, hqx⟩ := hx
  exact ⟨q, hq, incl_iff.mp h q.2 hbit, hqx⟩

omit [LawfulHashable α] in
theorem encode_mono {univ : List α} {S T : Std.HashSet α} (h : SetOps.Subset S T) :
    Incl (encode univ S) (encode univ T) := by
  apply incl_iff.mpr; intro i hi
  have hilt : i < univ.length := BitVec.lt_of_getLsbD hi
  rw [getLsbD_encode hilt, decide_eq_true_eq] at hi ⊢; exact h univ[i] hi

/-- Bitvector denotation at edge `e = (a, b)`: `⟦t⟧ e X`. This is what the solver iterates. -/
def evb (univ : List α) (e : Node × Node) : MTC α → ESet univ.length → ESet univ.length
  | var,       X => X
  | const f,   _ => encode univ (f e)
  | union a b, X => evb univ e a X ||| evb univ e b X
  | inter a b, X => evb univ e a X &&& evb univ e b X
  | diffc a f, X => evb univ e a X &&& ~~~ encode univ (f e)
  | gate sng res, X => Solver.gate (encode univ (sng e)) (encode univ (res e)) X
  | image U R, X   => encode univ (imageS U (R e) (decode univ X))
  | gather U sub, X => encode univ (gatherS U (sub e) (decode univ X))


/-! ## The three structural lemmas (proved once, by induction on the term) -/

omit [LawfulHashable α] in
/-- **Monotonicity** — every term is monotone in the incoming value. Gives the engine's `GMono` for free. -/
theorem evb_mono (univ : List α) (e : Node × Node) (t : MTC α) {X Y : ESet univ.length} (h : Incl X Y) :
    Incl (evb univ e t X) (evb univ e t Y) := by
  induction t with
  | var => exact h
  | const f => exact incl_refl _
  | union a b iha ihb => exact incl_or_mono iha ihb
  | inter a b iha ihb => exact incl_and_mono iha ihb
  | diffc a f iha => exact incl_and_mono iha (incl_refl _)
  | gate sng res => exact gate_mono h
  | image U R => exact encode_mono (imageS_mono (decode_mono h))
  | gather U sub => exact encode_mono (gatherS_mono (decode_mono h))

/-- **Decode homomorphism** — `decode (evb t bv) = evs t (decode bv)`, membership-wise. The spec bridge. -/
theorem evb_decode (univ : List α) (hnd : univ.Nodup) (e : Node × Node) (t : MTC α) (bv : ESet univ.length)
    (x : α) : Wf univ t →
    (x ∈ decode univ (evb univ e t bv) ↔ x ∈ evs e t (decode univ bv)) := by
  induction t with
  | var => intro _; exact Iff.rfl
  | const f => intro hf; simp only [evb, evs]; exact mem_decode_encode_of_sub (fun y hy => hf e y hy)
  | union a b iha ihb =>
      intro hw; simp only [evb, evs]
      rw [mem_decode_or, SetOps.mem_union]
      exact or_congr (iha hw.1) (ihb hw.2)
  | inter a b iha ihb =>
      intro hw; simp only [evb, evs]
      rw [mem_decode_and hnd, SetOps.mem_inter]
      exact and_congr (iha hw.1) (ihb hw.2)
  | diffc a f iha =>
      intro hw; simp only [evb, evs]
      rw [mem_decode_diff hnd, SetOps.mem_sdiff]
      refine and_congr (iha hw.1) ?_
      constructor
      · intro hx hmem; exact hx ((mem_decode_encode_of_sub (fun y hy => hw.2 e y hy)).mpr hmem)
      · intro hx hmem; exact hx ((mem_decode_encode_of_sub (fun y hy => hw.2 e y hy)).mp hmem)
  | gate sng res =>
      intro hw; simp only [evb, evs]
      rw [mem_decode_gate hnd]
      constructor
      · rintro ⟨⟨y, hy, hys⟩, hxr⟩
        have hys' : y ∈ sng e := (mem_decode_encode_of_sub (fun z hz => hw.1 e z hz)).mp hys
        have hguard : (decode univ bv).toList.any (fun y => (sng e).contains y) = true :=
          List.any_eq_true.mpr ⟨y, Std.HashSet.mem_toList.mpr hy, by
            rw [Std.HashSet.contains_iff_mem]; exact hys'⟩
        rw [if_pos hguard]
        exact (mem_decode_encode_of_sub (fun z hz => hw.2 e z hz)).mp hxr
      · intro hx
        by_cases hg : (decode univ bv).toList.any (fun y => (sng e).contains y) = true
        · rw [if_pos hg] at hx
          obtain ⟨y, hyl, hyc⟩ := List.any_eq_true.mp hg
          refine ⟨⟨y, Std.HashSet.mem_toList.mp hyl,
            (mem_decode_encode_of_sub (fun z hz => hw.1 e z hz)).mpr (Std.HashSet.contains_iff_mem.mp hyc)⟩,
            (mem_decode_encode_of_sub (fun z hz => hw.2 e z hz)).mpr hx⟩
        · rw [if_neg hg] at hx; exact absurd hx Std.HashSet.not_mem_empty
  | image U R =>
      intro hw; simp only [evb, evs]
      exact mem_decode_encode_of_sub (fun y hy => hw y (imageS_sub y hy))
  | gather U sub =>
      intro hw; simp only [evb, evs]
      exact mem_decode_encode_of_sub (fun y hy => hw y (gatherS_sub y hy))

end MTC

/-! ## A single generic forward-must solver, parameterized by a term `t`.

This generalizes a fixed forward-must transfer by replacing it with the reified `MTC.evb t`, and the
fixed membership lemma with the structural `MTC.evb_decode`. Every history ghost whose transfer is a
term instantiates `resMTC_correct` — no per-analysis proof. -/

variable {P : Program} {univ : List α} {t : MTC α} {sd : Std.HashSet α}

/-! Two `&&&`-projection lemmas for the must-quadrants' `sd`/`hi` caps (proved once via the bit view). -/
omit [LawfulHashable α] in
theorem incl_and_left {m : Nat} (a b : ESet m) : Incl (a &&& b) a := by
  apply incl_iff.mpr; intro i hi; rw [BitVec.getLsbD_and, Bool.and_eq_true] at hi; exact hi.1
omit [LawfulHashable α] in
theorem incl_and_right {m : Nat} (a b : ESet m) : Incl (a &&& b) b := by
  apply incl_iff.mpr; intro i hi; rw [BitVec.getLsbD_and, Bool.and_eq_true] at hi; exact hi.2

/-- The forward-must node transfer for term `t`: the entry value is capped by the seed `sd` (a boundary
    *ceiling*, mirroring the may-quadrants' `sd` floor), then meet-over-realizable-predecessors of
    `evb t` at each edge source. Capping (rather than pinning) keeps the back-edge case sound when a
    predecessor targets the entry; at `sd = ∅` the cap forces `0`, recovering the seedless boundary. The
    exact `⊓`/`⊤` dual of the forward-may `(if entry then encode sd else 0) ⊔ join`. -/
def gMTC (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) (arr : Array (ESet univ.length))
    (m : Node) : ESet univ.length :=
  (if m = P.entry then encode univ sd else topV univ.length) &&&
    meetList (fun p => MTC.evb univ (p, m) t (gA arr p)) (realizablePred P m)

omit [LawfulHashable α] in
theorem gMTC_mono : GMono P (gMTC P univ t sd) := by
  intro a b _ _ hab m _
  unfold gMTC
  refine incl_and_mono (incl_refl _) ?_
  apply meetList_mono
  intro p hp
  exact MTC.evb_mono univ (p, m) t (hab p (mem_realizablePred.mp hp).1)

omit [LawfulHashable α] in
theorem gMTC_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (m : Node)
    (hm : m ∉ realizableSucc P nd) :
    gMTC P univ t sd (arr.set! nd v) m = gMTC P univ t sd arr m := by
  unfold gMTC
  congr 1
  apply meetList_congr
  intro p hp
  have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
  have hpnd : p ≠ nd := fun hpe => hm (hpe ▸ hpm)
  rw [gA_set_ne hpnd]

/-- The executable forward-must term solver. -/
def solveMTC (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMust P (gMTC P univ t sd) realizableSucc

omit [LawfulHashable α] in
theorem solveMTC_eq (hwf : WellFormed P) : solveMTC P univ t sd = solveMust P (gMTC P univ t sd) :=
  solveWL_eq_must gMTC_mono (realizableSucc_readers_in_range hwf)
    (fun arr nd v m hm => gMTC_hloc arr nd v m hm)

omit [LawfulHashable α] in
theorem solveMTC_size (hwf : WellFormed P) : (solveMTC P univ t sd).size = P.size := by
  rw [solveMTC_eq hwf]; exact solveMust_size P (gMTC P univ t sd)

omit [LawfulHashable α] in
theorem solveMTC_settled (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    Incl (gA (solveMTC P univ t sd) m) (gMTC P univ t sd (solveMTC P univ t sd) m) := by
  have heq := solveMust_eq P (gMTC P univ t sd) hm
  rw [← solveMTC_eq hwf] at heq
  exact incl_of_and_eq heq

/-- Result as a total function; out of range reads the ceiling `⊤` (a must-analysis needs the greatest). -/
def solveMTCFun (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveMTC P univ t sd
  fun n => arr[n]?.getD (topV univ.length)

omit [LawfulHashable α] in
theorem solveMTCFun_in_range (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    solveMTCFun P univ t sd m = gA (solveMTC P univ t sd) m := by
  have hmsz : m < (solveMTC P univ t sd).size := by rw [solveMTC_size hwf]; exact hm
  show (solveMTC P univ t sd)[m]?.getD (topV univ.length) = gA (solveMTC P univ t sd) m
  unfold gA; rw [Array.getElem?_eq_getElem hmsz, Option.getD_some, Option.getD_some]

/-- The decoded forward-must term solution. -/
def resMTC (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveMTCFun P univ t sd n)


variable (hwf : WellFormed P) (hnd : univ.Nodup) (hw : MTC.Wf univ t)

include hwf in
theorem resMTC_edge (p m : Node) (hpm : m ∈ realizableSucc P p) :
    Incl (gA (solveMTC P univ t sd) m) (MTC.evb univ (p, m) t (gA (solveMTC P univ t sd) p)) := by
  have hmlt : m < P.size := realizableSucc_lt hwf hpm
  apply incl_trans (solveMTC_settled hwf hmlt)
  unfold gMTC
  refine incl_trans (incl_and_right _ _) ?_
  have hp_pred : p ∈ realizablePred P m :=
    mem_realizablePred.mpr ⟨succList_mem_lt (realizableSucc_subset_succList hpm), hpm⟩
  exact meetList_sub_mem _ hp_pred

include hwf hnd hw in
theorem resMTC_valid (hsd : ∀ x ∈ sd, x ∈ univ) : MTCSpec P univ t sd (resMTC P univ t sd) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hcnlt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hcn'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    rw [resMTC, solveMTCFun_in_range hwf hcn'lt] at hx
    have hedge : Incl (gA (solveMTC P univ t sd) c'.node)
        (MTC.evb univ (c.node, c'.node) t (gA (solveMTC P univ t sd) c.node)) := resMTC_edge hwf c.node c'.node hpm
    have hx' : x ∈ decode univ (MTC.evb univ (c.node, c'.node) t (gA (solveMTC P univ t sd) c.node)) :=
      (incl_iff_sub (α := α) hnd).mp hedge x hx
    rw [resMTC, solveMTCFun_in_range hwf hcnlt]
    exact (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mp hx'
  · intro x hx
    rw [resMTC, solveMTCFun_in_range hwf hwf.entry_lt] at hx
    have hs : Incl (gA (solveMTC P univ t sd) P.entry) (gMTC P univ t sd (solveMTC P univ t sd) P.entry) :=
      solveMTC_settled hwf hwf.entry_lt
    have hcap : Incl (gMTC P univ t sd (solveMTC P univ t sd) P.entry) (encode univ sd) := by
      unfold gMTC; rw [if_pos rfl]; exact incl_and_left _ _
    have : x ∈ decode univ (encode univ sd) := (incl_iff_sub (α := α) hnd).mp (incl_trans hs hcap) x hx
    exact (mem_decode_encode_of_sub (fun y hy => hsd y hy)).mp this
  · intro n x hx
    rw [resMTC, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw in
theorem resMTC_greatest (h : Node → Std.HashSet α) (hh : MTCSpec P univ t sd h) :
    ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ t sd n := by
  obtain ⟨hupd, hseed, hbound⟩ := hh
  have hpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (h k)) m)
        (gMTC P univ t sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m) := by
    intro m hm
    unfold gMTC
    apply incl_and_intro
    · by_cases he : m = P.entry
      · rw [if_pos he]; exact MTC.encode_mono (fun y hy => hseed y (he ▸ hy))
      · rw [if_neg he]; exact incl_topV _
    · apply incl_meetList; intro p hp
      have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
      have hplt : p < P.size := (mem_realizablePred.mp hp).1
      obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hpm
      rw [gA_ofFn _ hplt]
      apply incl_iff.mpr; intro i hi
      have hilt : i < univ.length := BitVec.lt_of_getLsbD hi
      rw [getLsbD_encode hilt, decide_eq_true_eq] at hi          -- hi : univ[i] ∈ h m
      have hstepmem : univ[i] ∈ MTC.evs (p, m) t (h p) := hupd ⟨p, σ⟩ ⟨m, σ'⟩ hstep univ[i] hi
      -- transport to `decode (evb …)` via the homomorphism + membership-congruence of `evs`
      have hcong : univ[i] ∈ MTC.evs (p, m) t (decode univ (encode univ (h p))) :=
        (MTC.evs_mem_congr (p, m) t (fun z => (mem_decode_encode_of_sub (fun y hy => hbound p y hy)).symm) univ[i]).mp
          hstepmem
      have hmem : univ[i] ∈ decode univ (MTC.evb univ (p, m) t (encode univ (h p))) :=
        (MTC.evb_decode univ hnd (p, m) t _ univ[i] hw).mpr hcong
      rw [mem_decode] at hmem
      obtain ⟨q, hq, hb, hqx⟩ := hmem
      obtain ⟨hqlt, hqe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
      have : q.2 = i := (List.getElem_inj hnd).mp (hqe.trans (by rw [hqx]))
      rw [← this]; exact hb
  have hdom := solveMust_extremal_of_postfix (g := gMTC P univ t sd) gMTC_mono
    (A := fun k => encode univ (h k)) hpost
  intro n x hxn
  have hxu : x ∈ univ := hbound n x hxn
  by_cases hnlt : n < P.size
  · have hdn : Incl (encode univ (h n)) (gA (solveMTC P univ t sd) n) := by
      have := hdom n hnlt; rwa [← solveMTC_eq hwf] at this
    have hxe : x ∈ decode univ (encode univ (h n)) :=
      (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mpr hxn
    rw [resMTC, solveMTCFun_in_range hwf hnlt]
    exact (incl_iff_sub (α := α) hnd).mp hdn x hxe
  · rw [resMTC]
    show x ∈ decode univ ((solveMTC P univ t sd)[n]?.getD (topV univ.length))
    have hns : ¬ n < (solveMTC P univ t sd).size := by rw [solveMTC_size hwf]; exact hnlt
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hns), Option.getD_none, mem_decode]
    obtain ⟨q, hq, hqx⟩ := mem_iff_exists_zipIdx.mp hxu
    obtain ⟨hqlt, _⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
    exact ⟨q, hq, by simp [topV, hqlt], hqx⟩

include hwf hnd hw in
/-- **Packaged generic forward-must correctness for a term.** The decoded solution is a valid `MTCSpec`
    solution and the greatest one — instantiated per analysis with that ghost's transfer term. -/
theorem resMTC_correct (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpec P univ t sd (resMTC P univ t sd) ∧
    ∀ h, MTCSpec P univ t sd h → ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ t sd n :=
  ⟨resMTC_valid hwf hnd hw hsd, fun h hh => resMTC_greatest hwf hnd hw h hh⟩

/-! ## The backward-**may** generic vertical (least, join over realizable successors) — liveness quadrant.

The *same* term `t` and the *same* four structural lemmas (`evb_mono`/`evb_decode`/`evs_sub`/
`evs_mem_congr`), driven by the join engine over successors with a `sd` seed at every `halt`. This
is the opposite corner of `resMTC` (forward-must): both the direction axis (pred→succ) and the
extremality axis (must/meet/greatest → may/join/least) are flipped, yet nothing about the transfer
language changes — direction and extremality are solver parameters, not part of `MTC`. Because the
clauses are *lower* bounds, `sd ⊆ univ` is required to round-trip. -/

variable {lo : Node → Std.HashSet α}

/-- The backward-may node transfer for term `t`: a per-node lower bound `lo`, a `sd` seed at `halt`, and
    the join-over-realizable-successors of `evb t` evaluated at the current (tail) node. `lo` is the
    always-present floor (the `check`/`floor` clause); it folds no monotonicity concern since it is
    constant in the incoming value. -/
def gMTCB (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  encode univ (lo n) ||| (if isHalt P n then encode univ sd else 0) |||
    joinList (fun m => MTC.evb univ (n, m) t (gA arr m)) (realizableSucc P n)

omit [LawfulHashable α] in
theorem gMTCB_mono : GMono P (gMTCB P univ t lo sd) := by
  intro a b hasz hbsz hab n _
  unfold gMTCB
  refine incl_or_mono (incl_refl _) ?_
  apply joinList_mono
  intro m _
  apply MTC.evb_mono
  by_cases hm : m < P.size
  · exact hab m hm
  · rw [gA_ge (by rw [hasz]; exact hm), gA_ge (by rw [hbsz]; exact hm)]; exact incl_zero

omit [LawfulHashable α] in
theorem gMTCB_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (n : Node)
    (hn : n ∉ realizablePred P nd) :
    gMTCB P univ t lo sd (arr.set! nd v) n = gMTCB P univ t lo sd arr n := by
  unfold gMTCB
  congr 1
  apply joinList_congr
  intro s hs
  have hsnd : s ≠ nd := fun hse => hn (mem_realizablePred.mpr
    ⟨succList_mem_lt (realizableSucc_subset_succList (hse ▸ hs)), hse ▸ hs⟩)
  rw [gA_set_ne hsnd]

/-- The executable backward-may term solver (join engine, `realizablePred` as the reader relation). -/
def solveMTCB (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α) (sd : Std.HashSet α) :
    Array (ESet univ.length) :=
  solveWLMay P (gMTCB P univ t lo sd) realizablePred

omit [LawfulHashable α] in
theorem solveMTCB_eq (hwf : WellFormed P) : solveMTCB P univ t lo sd = solveMay P (gMTCB P univ t lo sd) :=
  solveWL_eq_may gMTCB_mono (fun nd => realizablePred_readers_in_range nd)
    (fun arr nd v n hn => gMTCB_hloc arr nd v n hn)

omit [LawfulHashable α] in
theorem solveMTCB_size (hwf : WellFormed P) : (solveMTCB P univ t lo sd).size = P.size :=
  solveWL_size (botSeed_size P) (fun nd => realizablePred_readers_in_range nd)

omit [LawfulHashable α] in
/-- The may fixpoint: each `gMTCB` lower bound lands inside the solution. -/
theorem solveMTCB_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gMTCB P univ t lo sd (solveMTCB P univ t lo sd) n) (gA (solveMTCB P univ t lo sd) n) := by
  have heq := solveMay_eq P (gMTCB P univ t lo sd) hn
  rw [← solveMTCB_eq hwf] at heq
  exact incl_of_or_eq heq

/-- Result as a total function; out of range reads `lo` (the only off-graph constraint is `check`). -/
def solveMTCBFun (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α) (sd : Std.HashSet α) :
    Node → ESet univ.length :=
  let arr := solveMTCB P univ t lo sd
  fun n => if n < P.size then gA arr n else encode univ (lo n)

omit [LawfulHashable α] in
theorem solveMTCBFun_app (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) :
    solveMTCBFun P univ t lo sd n = if n < P.size then gA (solveMTCB P univ t lo sd) n else encode univ (lo n) := rfl

/-- The decoded backward-may term solution. -/
def resMTCB (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α) (sd : Std.HashSet α)
    (n : Node) : Std.HashSet α :=
  decode univ (solveMTCBFun P univ t lo sd n)


variable (hlo : ∀ n, ∀ x ∈ lo n, x ∈ univ) (hsd : ∀ x ∈ sd, x ∈ univ)

include hwf hnd hw hlo hsd in
theorem resMTCB_valid : MTCSpecB P univ t lo sd (resMTCB P univ t lo sd) := by
  -- Each lower-bound arm of `gMTCB` lands in the in-range result; assemble the four clauses.
  have harm : ∀ {n : Node}, n < P.size → ∀ {b : ESet univ.length},
      Incl b (gMTCB P univ t lo sd (solveMTCB P univ t lo sd) n) →
      ∀ x ∈ decode univ b, x ∈ resMTCB P univ t lo sd n := by
    intro n hn b hb x hx
    have : x ∈ decode univ (gA (solveMTCB P univ t lo sd) n) :=
      (incl_iff_sub (α := α) hnd).mp (incl_trans hb (solveMTCB_settled hwf hn)) x hx
    rw [resMTCB, solveMTCBFun_app, if_pos hn]; exact this
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- update: evs read from the successor lands in the tail's value
    intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    rw [resMTCB, solveMTCBFun_app, if_pos hc'lt] at hx
    have hxb : x ∈ decode univ (MTC.evb univ (c.node, c'.node) t (gA (solveMTCB P univ t lo sd) c'.node)) :=
      (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mpr hx
    refine harm hclt (incl_trans (joinList_mem_sub _ hpm) (incl_or_inr _ _)) x hxb
  · -- check: `lo n ⊆ h n` at every node
    intro n x hx
    by_cases hn : n < P.size
    · exact harm hn (incl_trans (incl_or_inl _ _) (incl_or_inl _ _)) x
        ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx)
    · rw [resMTCB, solveMTCBFun_app, if_neg hn]
      exact (mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx
  · -- seed: `sd` at every `halt`
    intro c hhalt x hx
    have hnlt : c.node < P.size := fetch_lt hhalt
    have hhb : isHalt P c.node = true := by simp [isHalt, hhalt]
    refine harm hnlt ?_ x ((mem_decode_encode_of_sub (fun y hy => hsd y hy)).mpr hx)
    show Incl (encode univ sd) (gMTCB P univ t lo sd (solveMTCB P univ t lo sd) c.node)
    unfold gMTCB; rw [if_pos hhb]; exact incl_trans (incl_or_inr _ _) (incl_or_inl _ _)
  · -- bound
    intro n x hx
    rw [resMTCB, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hlo hsd in
theorem resMTCB_least (h : Node → Std.HashSet α) (hh : MTCSpecB P univ t lo sd h) :
    ∀ n, ∀ x ∈ resMTCB P univ t lo sd n, x ∈ h n := by
  obtain ⟨hupd, hcheck, hseed, hbound⟩ := hh
  have hub : ∀ m, ∀ y ∈ h m, y ∈ decode univ (encode univ (h m)) :=
    fun m y hy => (mem_decode_encode_of_sub (fun z hz => hbound m z hz)).mpr hy
  -- `encode ∘ h` is a pre-fixpoint of `gMTCB`.
  have hpre : ∀ m, m < P.size →
      Incl (gMTCB P univ t lo sd
          (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m)
        (encode univ (h m)) := by
    intro m hm
    apply incl_or_elim
    · apply incl_or_elim
      · exact encode_incl_decode hnd (fun y hy => hub m y (hcheck m y hy))
      · by_cases hh2 : isHalt P m
        · rw [if_pos hh2]
          have hhalt : P.fetch m = some .halt := by simpa [isHalt] using hh2
          exact encode_incl_decode hnd (fun y hy => hub m y (hseed ⟨m, Store.init⟩ hhalt y hy))
        · rw [if_neg hh2]; exact incl_zero
    · apply joinList_incl
      intro m' hm'
      have hm'lt : m' < P.size := realizableSucc_lt hwf hm'
      obtain ⟨sg, sg', hstep⟩ := realizable_iff_step.mpr hm'
      rw [gA_ofFn _ hm'lt]
      apply incl_decode_encode
      intro x hx
      have hxs : x ∈ MTC.evs (m, m') t (decode univ (encode univ (h m'))) :=
        (MTC.evb_decode univ hnd (m, m') t _ x hw).mp hx
      have hxh' : x ∈ MTC.evs (m, m') t (h m') :=
        (MTC.evs_mem_congr (m, m') t (fun z => mem_decode_encode_of_sub (fun y hy => hbound m' y hy)) x).mp hxs
      exact hupd ⟨m, sg⟩ ⟨m', sg'⟩ hstep x hxh'
  have hdom := solveMay_extremal_of_prefix (g := gMTCB P univ t lo sd) gMTCB_mono
    (A := fun k => encode univ (h k)) hpre
  intro n x hx
  by_cases hn : n < P.size
  · rw [resMTCB, solveMTCBFun_app, if_pos hn] at hx
    have hdn : Incl (gA (solveMTCB P univ t lo sd) n) (encode univ (h n)) := by
      have := hdom n hn; rwa [← solveMTCB_eq hwf] at this
    exact (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mp
      ((incl_iff_sub (α := α) hnd).mp hdn x hx)
  · rw [resMTCB, solveMTCBFun_app, if_neg hn] at hx
    exact hcheck n x ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mp hx)

include hwf hnd hw hlo hsd in
/-- **Packaged generic backward-may correctness for a term.** Valid `MTCSpecB` and least. -/
theorem resMTCB_correct :
    MTCSpecB P univ t lo sd (resMTCB P univ t lo sd) ∧
    ∀ h, MTCSpecB P univ t lo sd h → ∀ n, ∀ x ∈ resMTCB P univ t lo sd n, x ∈ h n :=
  ⟨resMTCB_valid hwf hnd hw hlo hsd, fun h hh => resMTCB_least hwf hnd hw hlo hsd h hh⟩

/-! ## The backward-**must** generic vertical (greatest, meet over realizable successors) — the
    very-busy / anticipated-expressions quadrant. Mirror of `resMTC` with the direction axis flipped
    (predecessors → successors) and the boundary moved to `halt` (seeded `∅`); the extremality axis
    (meet/greatest/⊤) is unchanged. Same `MTC`, same four structural lemmas. -/

variable {hi : Node → Std.HashSet α}

/-! ## Doubly-clamped steps (full generality — a floor `lo` ∪ AND a ceiling `hi` ∩ in every quadrant).

Each is the existing quadrant step wrapped by the opposite clamp: the must steps gain a floor (`lo ∪ ·`),
the may steps gain a ceiling (`hi ∩ ·`). `lo = ∅` / `hi = univ` recover the existing solver, so these
subsume all four unclamped/single-clamped quadrants. Monotonicity and locality reuse the wrapped step's
lemmas verbatim (the clamps are constant `∪`/`∩` wrappers). The `_valid`/`_extremal` proofs — which must
thread both clamp clauses — are the per-quadrant `res*C` theorems below. -/

/-- Forward-must, doubly clamped (**cap-the-transfer**): `hi ∩ (lo ∪ gMTC)`. The ceiling `hi` is the
    primary (aligned) clamp — outermost `∩`, so `h ⊆ hi` cleanly; the floor `lo` is folded into the
    transfer (`∪`), relaxing the must-update to `h(n') ⊆ evs ∪ lo(n')`. Needs `lo ⊆ hi` (a non-empty band)
    to also give the clean floor `lo ⊆ h`. -/
def gFMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (m : Node) : ESet univ.length :=
  encode univ (hi m) &&& (encode univ (lo m) ||| gMTC P univ t sd arr m)

omit [LawfulHashable α] in
theorem gFMC_mono : GMono P (gFMC P univ t lo hi sd) := by
  intro a b hasz hbsz hab m hm
  unfold gFMC
  exact incl_and_mono (incl_refl _) (incl_or_mono (incl_refl _) (gMTC_mono a b hasz hbsz hab m hm))

omit [LawfulHashable α] in
theorem gFMC_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (m : Node)
    (hm : m ∉ realizableSucc P nd) :
    gFMC P univ t lo hi sd (arr.set! nd v) m = gFMC P univ t lo hi sd arr m := by
  unfold gFMC
  rw [gMTC_hloc arr nd v m hm]

/-- Backward-must node transfer: capped by the per-node ceiling `hi` (the `check`/upper-bound clause)
    and, at `halt`, by the seed `sd` (the boundary ceiling); else meet-over-realizable-successors of
    `evb t` at the current (tail) node. `hi`/`sd` are the symmetric mirrors of the may-quadrants' `lo`/
    `sd`; at `sd = ∅` the cap forces `0`, recovering the seedless halt boundary. -/
def gMTCBM (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  encode univ (hi n) &&& (if isHalt P n then encode univ sd else meetList (fun m => MTC.evb univ (n, m) t (gA arr m)) (realizableSucc P n))

omit [LawfulHashable α] in
theorem gMTCBM_mono : GMono P (gMTCBM P univ t hi sd) := by
  intro a b hasz hbsz hab n _
  unfold gMTCBM
  refine incl_and_mono (incl_refl _) ?_
  by_cases he : isHalt P n
  · rw [if_pos he, if_pos he]; exact incl_refl _
  · rw [if_neg he, if_neg he]
    apply meetList_mono
    intro m _
    apply MTC.evb_mono
    by_cases hm : m < P.size
    · exact hab m hm
    · rw [gA_ge (by rw [hasz]; exact hm), gA_ge (by rw [hbsz]; exact hm)]; exact incl_zero

omit [LawfulHashable α] in
theorem gMTCBM_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (n : Node)
    (hn : n ∉ realizablePred P nd) :
    gMTCBM P univ t hi sd (arr.set! nd v) n = gMTCBM P univ t hi sd arr n := by
  unfold gMTCBM
  congr 1
  by_cases he : isHalt P n
  · rw [if_pos he, if_pos he]
  · rw [if_neg he, if_neg he]
    apply meetList_congr
    intro s hs
    have hsnd : s ≠ nd := fun hse => hn (mem_realizablePred.mpr
      ⟨succList_mem_lt (realizableSucc_subset_succList (hse ▸ hs)), hse ▸ hs⟩)
    rw [gA_set_ne hsnd]

/-- The executable backward-must term solver (meet engine, `realizablePred` as the reader relation). -/
def solveMTCBM (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α) (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMust P (gMTCBM P univ t hi sd) realizablePred

omit [LawfulHashable α] in
theorem solveMTCBM_eq (hwf : WellFormed P) : solveMTCBM P univ t hi sd = solveMust P (gMTCBM P univ t hi sd) :=
  solveWL_eq_must gMTCBM_mono (fun nd => realizablePred_readers_in_range nd)
    (fun arr nd v n hn => gMTCBM_hloc arr nd v n hn)

omit [LawfulHashable α] in
theorem solveMTCBM_size (hwf : WellFormed P) : (solveMTCBM P univ t hi sd).size = P.size := by
  rw [solveMTCBM_eq hwf]; exact solveMust_size P (gMTCBM P univ t hi sd)

omit [LawfulHashable α] in
theorem solveMTCBM_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gA (solveMTCBM P univ t hi sd) n) (gMTCBM P univ t hi sd (solveMTCBM P univ t hi sd) n) := by
  have heq := solveMust_eq P (gMTCBM P univ t hi sd) hn
  rw [← solveMTCBM_eq hwf] at heq
  exact incl_of_and_eq heq

/-- Result as a total function; out of range reads the ceiling `hi` (the only off-graph constraint). -/
def solveMTCBMFun (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α) (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveMTCBM P univ t hi sd
  fun n => if n < P.size then gA arr n else encode univ (hi n)

omit [LawfulHashable α] in
theorem solveMTCBMFun_in_range (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    solveMTCBMFun P univ t hi sd m = gA (solveMTCBM P univ t hi sd) m := by
  show (if m < P.size then _ else _) = _
  rw [if_pos hm]

omit [LawfulHashable α] in
theorem solveMTCBMFun_in_range_neg {m : Node} (hm : ¬ m < P.size) :
    solveMTCBMFun P univ t hi sd m = encode univ (hi m) := by
  show (if m < P.size then _ else _) = _
  rw [if_neg hm]

/-- The decoded backward-must term solution. -/
def resMTCBM (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α) (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveMTCBMFun P univ t hi sd n)


include hwf in
theorem resMTCBM_edge (n m : Node) (hnm : m ∈ realizableSucc P n) :
    Incl (gA (solveMTCBM P univ t hi sd) n) (MTC.evb univ (n, m) t (gA (solveMTCBM P univ t hi sd) m)) := by
  have hnlt : n < P.size := succList_mem_lt (realizableSucc_subset_succList hnm)
  apply incl_trans (solveMTCBM_settled hwf hnlt)
  unfold gMTCBM
  refine incl_trans (incl_and_right _ _) ?_
  by_cases he : isHalt P n
  · -- `halt` has no realizable successor, so this case is vacuous (`hnm : m ∈ []`).
    exfalso
    have hf : P.fetch n = some .halt := by simpa [isHalt] using he
    have he0 : realizableSucc P n = [] := by simp [realizableSucc, hf]
    rw [he0] at hnm; simp at hnm
  · rw [if_neg he]; exact meetList_sub_mem _ hnm

include hwf hnd hw hsd in
theorem resMTCBM_valid : MTCSpecBM P univ t hi sd (resMTCBM P univ t hi sd) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hcnlt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hcn'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    rw [resMTCBM, solveMTCBMFun_in_range hwf hcnlt] at hx
    have hx' : x ∈ decode univ (MTC.evb univ (c.node, c'.node) t (gA (solveMTCBM P univ t hi sd) c'.node)) :=
      (incl_iff_sub (α := α) hnd).mp (resMTCBM_edge hwf c.node c'.node hpm) x hx
    rw [resMTCBM, solveMTCBMFun_in_range hwf hcn'lt]
    exact (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mp hx'
  · -- check: `resMTCBM n ⊆ hi n`
    intro n x hx
    by_cases hn : n < P.size
    · rw [resMTCBM, solveMTCBMFun_in_range hwf hn] at hx
      have : x ∈ decode univ (encode univ (hi n)) := (incl_iff_sub (α := α) hnd).mp
        (incl_trans (solveMTCBM_settled hwf hn) (by unfold gMTCBM; exact incl_and_left _ _)) x hx
      exact (mem_decode_encode.mp this).1
    · rw [resMTCBM, solveMTCBMFun_in_range_neg hn] at hx
      exact (mem_decode_encode.mp hx).1
  · -- seed: `resMTCBM (halt) ⊆ sd` (the boundary ceiling)
    intro c hhalt x hx
    have hnlt : c.node < P.size := fetch_lt hhalt
    have hhb : isHalt P c.node = true := by simp [isHalt, hhalt]
    rw [resMTCBM, solveMTCBMFun_in_range hwf hnlt] at hx
    have hs : Incl (gA (solveMTCBM P univ t hi sd) c.node) (gMTCBM P univ t hi sd (solveMTCBM P univ t hi sd) c.node) :=
      solveMTCBM_settled hwf hnlt
    have hcap : Incl (gMTCBM P univ t hi sd (solveMTCBM P univ t hi sd) c.node) (encode univ sd) := by
      unfold gMTCBM; rw [if_pos hhb]; exact incl_and_right _ _
    have : x ∈ decode univ (encode univ sd) := (incl_iff_sub (α := α) hnd).mp (incl_trans hs hcap) x hx
    exact (mem_decode_encode_of_sub (fun y hy => hsd y hy)).mp this
  · intro n x hx
    rw [resMTCBM, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw in
theorem resMTCBM_greatest (h : Node → Std.HashSet α) (hh : MTCSpecBM P univ t hi sd h) :
    ∀ n, ∀ x ∈ h n, x ∈ resMTCBM P univ t hi sd n := by
  obtain ⟨hupd, hcheck, hseed, hbound⟩ := hh
  have hpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (h k)) m)
        (gMTCBM P univ t hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m) := by
    intro m hm
    unfold gMTCBM
    apply incl_and_intro
    · exact MTC.encode_mono (fun y hy => hcheck m y hy)
    · by_cases he : isHalt P m
      · rw [if_pos he]
        have hhalt : P.fetch m = some .halt := by simpa [isHalt] using he
        exact MTC.encode_mono (fun y hy => hseed ⟨m, Store.init⟩ hhalt y hy)
      · rw [if_neg he]
        apply incl_meetList; intro m' hm'
        have hm'lt : m' < P.size := realizableSucc_lt hwf hm'
        obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hm'
        rw [gA_ofFn _ hm'lt]
        apply incl_iff.mpr; intro i hi2
        have hilt : i < univ.length := BitVec.lt_of_getLsbD hi2
        rw [getLsbD_encode hilt, decide_eq_true_eq] at hi2
        have hstepmem : univ[i] ∈ MTC.evs (m, m') t (h m') := hupd ⟨m, σ⟩ ⟨m', σ'⟩ hstep univ[i] hi2
        have hcong : univ[i] ∈ MTC.evs (m, m') t (decode univ (encode univ (h m'))) :=
          (MTC.evs_mem_congr (m, m') t (fun z => (mem_decode_encode_of_sub (fun y hy => hbound m' y hy)).symm)
            univ[i]).mp hstepmem
        have hmem : univ[i] ∈ decode univ (MTC.evb univ (m, m') t (encode univ (h m'))) :=
          (MTC.evb_decode univ hnd (m, m') t _ univ[i] hw).mpr hcong
        rw [mem_decode] at hmem
        obtain ⟨q, hq, hb, hqx⟩ := hmem
        obtain ⟨hqlt, hqe⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp hq)
        have : q.2 = i := (List.getElem_inj hnd).mp (hqe.trans (by rw [hqx]))
        rw [← this]; exact hb
  have hdom := solveMust_extremal_of_postfix (g := gMTCBM P univ t hi sd) gMTCBM_mono
    (A := fun k => encode univ (h k)) hpost
  intro n x hxn
  by_cases hnlt : n < P.size
  · have hdn : Incl (encode univ (h n)) (gA (solveMTCBM P univ t hi sd) n) := by
      have := hdom n hnlt; rwa [← solveMTCBM_eq hwf] at this
    have hxe : x ∈ decode univ (encode univ (h n)) :=
      (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mpr hxn
    rw [resMTCBM, solveMTCBMFun_in_range hwf hnlt]
    exact (incl_iff_sub (α := α) hnd).mp hdn x hxe
  · rw [resMTCBM, solveMTCBMFun_in_range_neg hnlt]
    exact (mem_decode_encode.mpr ⟨hcheck n x hxn, hbound n x hxn⟩)

include hwf hnd hw hsd in
/-- **Packaged generic backward-must correctness for a term** (very-busy / anticipated). -/
theorem resMTCBM_correct :
    MTCSpecBM P univ t hi sd (resMTCBM P univ t hi sd) ∧
    ∀ h, MTCSpecBM P univ t hi sd h → ∀ n, ∀ x ∈ h n, x ∈ resMTCBM P univ t hi sd n :=
  ⟨resMTCBM_valid hwf hnd hw hsd, fun h hh => resMTCBM_greatest hwf hnd hw h hh⟩

/-! ## The forward-**may** generic vertical (least, join over realizable predecessors) — reaching
    definitions. Mirror of `resMTCB` with the direction axis flipped (successors → predecessors) and the
    boundary at `entry` (seeded `sd`); the extremality axis (join/least/∅) is unchanged. -/

/-- Forward-may node transfer: an `sd` seed at `entry`, joined with the join-over-realizable-predecessors
    of `evb t` evaluated at each edge source. -/
def gMTCMF (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  (if n = P.entry then encode univ sd else 0) |||
    joinList (fun m => MTC.evb univ (m, n) t (gA arr m)) (realizablePred P n)

omit [LawfulHashable α] in
theorem gMTCMF_mono : GMono P (gMTCMF P univ t sd) := by
  intro a b _ _ hab n _
  unfold gMTCMF
  refine incl_or_mono (incl_refl _) ?_
  apply joinList_mono
  intro p hp
  exact MTC.evb_mono univ (p, n) t (hab p (mem_realizablePred.mp hp).1)

omit [LawfulHashable α] in
theorem gMTCMF_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (m : Node)
    (hm : m ∉ realizableSucc P nd) :
    gMTCMF P univ t sd (arr.set! nd v) m = gMTCMF P univ t sd arr m := by
  unfold gMTCMF
  congr 1
  apply joinList_congr
  intro p hp
  have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
  have hpnd : p ≠ nd := fun hpe => hm (hpe ▸ hpm)
  rw [gA_set_ne hpnd]

/-- The executable forward-may term solver (join engine, `realizableSucc` as the reader relation). -/
def solveMTCMF (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMay P (gMTCMF P univ t sd) realizableSucc

omit [LawfulHashable α] in
theorem solveMTCMF_eq (hwf : WellFormed P) : solveMTCMF P univ t sd = solveMay P (gMTCMF P univ t sd) :=
  solveWL_eq_may gMTCMF_mono (realizableSucc_readers_in_range hwf)
    (fun arr nd v m hm => gMTCMF_hloc arr nd v m hm)

omit [LawfulHashable α] in
theorem solveMTCMF_size (hwf : WellFormed P) : (solveMTCMF P univ t sd).size = P.size :=
  solveWL_size (botSeed_size P) (realizableSucc_readers_in_range hwf)

omit [LawfulHashable α] in
theorem solveMTCMF_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gMTCMF P univ t sd (solveMTCMF P univ t sd) n) (gA (solveMTCMF P univ t sd) n) := by
  have heq := solveMay_eq P (gMTCMF P univ t sd) hn
  rw [← solveMTCMF_eq hwf] at heq
  exact incl_of_or_eq heq

/-- Result as a total function; out of range reads `∅` (a may-analysis needs the least). -/
def solveMTCMFFun (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) :
    Node → ESet univ.length :=
  let arr := solveMTCMF P univ t sd
  fun n => if n < P.size then gA arr n else 0

omit [LawfulHashable α] in
theorem solveMTCMFFun_app (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) (n : Node) :
    solveMTCMFFun P univ t sd n = if n < P.size then gA (solveMTCMF P univ t sd) n else 0 := rfl

/-- The decoded forward-may term solution. -/
def resMTCMF (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) (n : Node) :
    Std.HashSet α :=
  decode univ (solveMTCMFFun P univ t sd n)


include hwf hnd hw hsd in
theorem resMTCMF_valid : MTCSpecMF P univ t sd (resMTCMF P univ t sd) := by
  have harm : ∀ {n : Node}, n < P.size → ∀ {b : ESet univ.length},
      Incl b (gMTCMF P univ t sd (solveMTCMF P univ t sd) n) →
      ∀ x ∈ decode univ b, x ∈ resMTCMF P univ t sd n := by
    intro n hn b hb x hx
    have : x ∈ decode univ (gA (solveMTCMF P univ t sd) n) :=
      (incl_iff_sub (α := α) hnd).mp (incl_trans hb (solveMTCMF_settled hwf hn)) x hx
    rw [resMTCMF, solveMTCMFFun_app, if_pos hn]; exact this
  refine ⟨?_, ?_, ?_⟩
  · -- update: evs read at the edge source lands in the head's value
    intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    have hcpred : c.node ∈ realizablePred P c'.node :=
      mem_realizablePred.mpr ⟨hclt, hpm⟩
    rw [resMTCMF, solveMTCMFFun_app, if_pos hclt] at hx
    have hxb : x ∈ decode univ (MTC.evb univ (c.node, c'.node) t (gA (solveMTCMF P univ t sd) c.node)) :=
      (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mpr hx
    refine harm hc'lt (incl_trans (joinList_mem_sub _ hcpred) (incl_or_inr _ _)) x hxb
  · -- seed: `sd` at the entry
    intro x hx
    refine harm hwf.entry_lt ?_ x ((mem_decode_encode_of_sub (fun y hy => hsd y hy)).mpr hx)
    show Incl (encode univ sd) (gMTCMF P univ t sd (solveMTCMF P univ t sd) P.entry)
    unfold gMTCMF; rw [if_pos rfl]; exact incl_or_inl _ _
  · intro n x hx
    rw [resMTCMF, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hsd in
theorem resMTCMF_least (h : Node → Std.HashSet α) (hh : MTCSpecMF P univ t sd h) :
    ∀ n, ∀ x ∈ resMTCMF P univ t sd n, x ∈ h n := by
  obtain ⟨hupd, hseed, hbound⟩ := hh
  have hub : ∀ m, ∀ y ∈ h m, y ∈ decode univ (encode univ (h m)) :=
    fun m y hy => (mem_decode_encode_of_sub (fun z hz => hbound m z hz)).mpr hy
  have hpre : ∀ m, m < P.size →
      Incl (gMTCMF P univ t sd
          (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m)
        (encode univ (h m)) := by
    intro m hm
    apply incl_or_elim
    · by_cases hme : m = P.entry
      · rw [if_pos hme]
        exact encode_incl_decode hnd (fun y hy => hub m y (by rw [hme]; exact hseed y hy))
      · rw [if_neg hme]; exact incl_zero
    · apply joinList_incl
      intro p hp
      have hplt : p < P.size := (mem_realizablePred.mp hp).1
      have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
      obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hpm
      rw [gA_ofFn _ hplt]
      apply incl_decode_encode
      intro x hx
      have hxs : x ∈ MTC.evs (p, m) t (decode univ (encode univ (h p))) :=
        (MTC.evb_decode univ hnd (p, m) t _ x hw).mp hx
      have hxh : x ∈ MTC.evs (p, m) t (h p) :=
        (MTC.evs_mem_congr (p, m) t (fun z => mem_decode_encode_of_sub (fun y hy => hbound p y hy)) x).mp hxs
      exact hupd ⟨p, σ⟩ ⟨m, σ'⟩ hstep x hxh
  have hdom := solveMay_extremal_of_prefix (g := gMTCMF P univ t sd) gMTCMF_mono
    (A := fun k => encode univ (h k)) hpre
  intro n x hx
  by_cases hn : n < P.size
  · rw [resMTCMF, solveMTCMFFun_app, if_pos hn] at hx
    have hdn : Incl (gA (solveMTCMF P univ t sd) n) (encode univ (h n)) := by
      have := hdom n hn; rwa [← solveMTCMF_eq hwf] at this
    exact (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mp
      ((incl_iff_sub (α := α) hnd).mp hdn x hx)
  · rw [resMTCMF, solveMTCMFFun_app, if_neg hn, mem_decode] at hx
    obtain ⟨q, _, hb, _⟩ := hx; simp [BitVec.getLsbD_zero] at hb

include hwf hnd hw hsd in
/-- **Packaged generic forward-may correctness for a term** (reaching definitions). -/
theorem resMTCMF_correct :
    MTCSpecMF P univ t sd (resMTCMF P univ t sd) ∧
    ∀ h, MTCSpecMF P univ t sd h → ∀ n, ∀ x ∈ resMTCMF P univ t sd n, x ∈ h n :=
  ⟨resMTCMF_valid hwf hnd hw hsd, fun h hh => resMTCMF_least hwf hnd hw hsd h hh⟩

/-! ## The doubly-clamped forward-**must** generic vertical (**cap-the-transfer** `hi ∩ (lo ∪ gMTC)`).

Full clamp generality for the forward-must quadrant: it carries **both** a floor `lo` and a ceiling `hi`.
The ceiling is the aligned (primary) clamp — outermost `∩`, so `h ⊆ hi` cleanly; the floor is folded into
the transfer (`∪`), relaxing every upper-bound clause of the greatest solution — the `update` (to
`h c'.node ⊆ evs ∪ lo`) *and* the boundary `seed` (to `⊆ sd ∪ lo`). The step (`gFMC`) and its
`_mono`/`_hloc` are the constant-clamp wrappers proved above; here are the solver plumbing and the
`_valid`/`_greatest` proofs. Needs a non-empty band `lo ⊆ hi` (`hlohi`) for the clean floor clause. -/

/-- The executable doubly-clamped forward-must term solver (meet engine, `realizableSucc` reader). -/
def solveFMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMust P (gFMC P univ t lo hi sd) realizableSucc

omit [LawfulHashable α] in
theorem solveFMC_eq (hwf : WellFormed P) :
    solveFMC P univ t lo hi sd = solveMust P (gFMC P univ t lo hi sd) :=
  solveWL_eq_must gFMC_mono (realizableSucc_readers_in_range hwf)
    (fun arr nd v m hm => gFMC_hloc arr nd v m hm)

omit [LawfulHashable α] in
theorem solveFMC_size (hwf : WellFormed P) : (solveFMC P univ t lo hi sd).size = P.size := by
  rw [solveFMC_eq hwf]; exact solveMust_size P (gFMC P univ t lo hi sd)

omit [LawfulHashable α] in
theorem solveFMC_settled (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    Incl (gA (solveFMC P univ t lo hi sd) m)
      (gFMC P univ t lo hi sd (solveFMC P univ t lo hi sd) m) := by
  have heq := solveMust_eq P (gFMC P univ t lo hi sd) hm
  rw [← solveFMC_eq hwf] at heq
  exact incl_of_and_eq heq

/-- Result as a total function; out of range reads the ceiling `hi` (mirrors `solveMTCBMFun`). -/
def solveFMCFun (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveFMC P univ t lo hi sd
  fun n => if n < P.size then gA arr n else encode univ (hi n)

omit [LawfulHashable α] in
theorem solveFMCFun_in_range (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    solveFMCFun P univ t lo hi sd m = gA (solveFMC P univ t lo hi sd) m := by
  show (if m < P.size then _ else _) = _; rw [if_pos hm]

omit [LawfulHashable α] in
theorem solveFMCFun_in_range_neg {m : Node} (hm : ¬ m < P.size) :
    solveFMCFun P univ t lo hi sd m = encode univ (hi m) := by
  show (if m < P.size then _ else _) = _; rw [if_neg hm]

/-- The decoded doubly-clamped forward-must term solution. -/
def resFMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveFMCFun P univ t lo hi sd n)

variable (hhi : ∀ n, ∀ x ∈ hi n, x ∈ univ) (hlohi : ∀ n, ∀ x ∈ lo n, x ∈ hi n)

include hwf hnd hw hlo hhi hlohi in
theorem resFMC_valid : MTCSpecC P univ t lo hi sd (resFMC P univ t lo hi sd) := by
  -- The floor `lo` lands in every in-range slot: `encode ∘ lo` is a `gFMC`-postfix (needs `lo ⊆ hi`).
  have hfloorpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (lo k)) m)
        (gFMC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (lo i.val))) m) := by
    intro m _
    unfold gFMC
    exact incl_and_intro (MTC.encode_mono (fun y hy => hlohi m y hy)) (incl_or_inl _ _)
  have hfloordom := solveMust_extremal_of_postfix (g := gFMC P univ t lo hi sd) gFMC_mono
    (A := fun k => encode univ (lo k)) hfloorpost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- update (cap-the-transfer): `x ∈ h c'.node → x ∈ evs t (h c.node) ∨ x ∈ lo c'.node`
    intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    have hp_pred : c.node ∈ realizablePred P c'.node := mem_realizablePred.mpr ⟨hclt, hpm⟩
    rw [resFMC, solveFMCFun_in_range hwf hc'lt] at hx
    have hincl : Incl (gA (solveFMC P univ t lo hi sd) c'.node)
        (encode univ (lo c'.node) ||| MTC.evb univ (c.node, c'.node) t (gA (solveFMC P univ t lo hi sd) c.node)) := by
      refine incl_trans (solveFMC_settled hwf hc'lt) ?_
      unfold gFMC
      refine incl_trans (incl_and_right _ _) ?_
      refine incl_or_mono (incl_refl _) ?_
      unfold gMTC
      exact incl_trans (incl_and_right _ _) (meetList_sub_mem _ hp_pred)
    have hmem : x ∈ decode univ (encode univ (lo c'.node) |||
        MTC.evb univ (c.node, c'.node) t (gA (solveFMC P univ t lo hi sd) c.node)) :=
      (incl_iff_sub (α := α) hnd).mp hincl x hx
    rw [mem_decode_or] at hmem
    rcases hmem with hlom | hevb
    · exact Or.inr (mem_decode_encode.mp hlom).1
    · refine Or.inl ?_
      rw [resFMC, solveFMCFun_in_range hwf hclt]
      exact (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mp hevb
  · -- floor: `lo n ⊆ h n`
    intro n x hx
    by_cases hn : n < P.size
    · have hdn : Incl (encode univ (lo n)) (gA (solveFMC P univ t lo hi sd) n) := by
        have := hfloordom n hn; rwa [← solveFMC_eq hwf] at this
      rw [resFMC, solveFMCFun_in_range hwf hn]
      exact (incl_iff_sub (α := α) hnd).mp hdn x
        ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx)
    · rw [resFMC, solveFMCFun_in_range_neg hn]
      exact (mem_decode_encode_of_sub (fun y hy => hhi n y hy)).mpr (hlohi n x hx)
  · -- ceiling: `h n ⊆ hi n`
    intro n x hx
    by_cases hn : n < P.size
    · rw [resFMC, solveFMCFun_in_range hwf hn] at hx
      have : x ∈ decode univ (encode univ (hi n)) := (incl_iff_sub (α := α) hnd).mp
        (incl_trans (solveFMC_settled hwf hn) (by unfold gFMC; exact incl_and_left _ _)) x hx
      exact (mem_decode_encode.mp this).1
    · rw [resFMC, solveFMCFun_in_range_neg hn] at hx
      exact (mem_decode_encode.mp hx).1
  · -- seed (relaxed ceiling): `x ∈ h entry → x ∈ sd ∨ x ∈ lo entry`
    intro x hx
    rw [resFMC, solveFMCFun_in_range hwf hwf.entry_lt] at hx
    have hincl : Incl (gA (solveFMC P univ t lo hi sd) P.entry)
        (encode univ (lo P.entry) ||| encode univ sd) := by
      refine incl_trans (solveFMC_settled hwf hwf.entry_lt) ?_
      unfold gFMC
      refine incl_trans (incl_and_right _ _) ?_
      refine incl_or_mono (incl_refl _) ?_
      unfold gMTC; rw [if_pos rfl]; exact incl_and_left _ _
    have hmem : x ∈ decode univ (encode univ (lo P.entry) ||| encode univ sd) :=
      (incl_iff_sub (α := α) hnd).mp hincl x hx
    rw [mem_decode_or] at hmem
    rcases hmem with hl | hs
    · exact Or.inr (mem_decode_encode.mp hl).1
    · exact Or.inl (mem_decode_encode.mp hs).1
  · -- within the universe
    intro n x hx
    rw [resFMC, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hlo hsd in
theorem resFMC_greatest (h : Node → Std.HashSet α) (hh : MTCSpecC P univ t lo hi sd h) :
    ∀ n, ∀ x ∈ h n, x ∈ resFMC P univ t lo hi sd n := by
  obtain ⟨hupd, hfloor, hceil, hseed, hbound⟩ := hh
  have hpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (h k)) m)
        (gFMC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m) := by
    intro m hm
    unfold gFMC
    apply incl_and_intro
    · -- ceiling clause: `h m ⊆ hi m`
      exact MTC.encode_mono (fun y hy => hceil m y hy)
    · -- cap-the-transfer core: `encode (h m) ⊆ encode (lo m) ||| gMTC (…) m`
      unfold gMTC
      rw [or_and_distrib, or_meetList]
      apply incl_and_intro
      · -- seed cap (relaxed by `lo`)
        by_cases he : m = P.entry
        · rw [if_pos he]
          apply encode_incl_decode hnd
          intro y hy
          rw [mem_decode_or]
          rcases hseed y (he ▸ hy) with hs | hl
          · exact Or.inr ((mem_decode_encode_of_sub (fun z hz => hsd z hz)).mpr hs)
          · exact Or.inl ((mem_decode_encode_of_sub (fun z hz => hlo m z hz)).mpr (by rw [he]; exact hl))
        · rw [if_neg he, or_topV]; exact incl_topV _
      · -- meet over realizable predecessors (each edge's `update`, relaxed by `lo`)
        apply incl_meetList
        intro p hp
        have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
        have hplt : p < P.size := (mem_realizablePred.mp hp).1
        obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hpm
        rw [gA_ofFn _ hplt]
        apply encode_incl_decode hnd
        intro y hy
        rw [mem_decode_or]
        rcases hupd ⟨p, σ⟩ ⟨m, σ'⟩ hstep y hy with hev | hlm
        · refine Or.inr ?_
          have hcong : y ∈ MTC.evs (p, m) t (decode univ (encode univ (h p))) :=
            (MTC.evs_mem_congr (p, m) t
              (fun z => (mem_decode_encode_of_sub (fun w hw2 => hbound p w hw2)).symm) y).mp hev
          exact (MTC.evb_decode univ hnd (p, m) t _ y hw).mpr hcong
        · exact Or.inl ((mem_decode_encode_of_sub (fun z hz => hlo m z hz)).mpr hlm)
  have hdom := solveMust_extremal_of_postfix (g := gFMC P univ t lo hi sd) gFMC_mono
    (A := fun k => encode univ (h k)) hpost
  intro n x hxn
  by_cases hnlt : n < P.size
  · have hdn : Incl (encode univ (h n)) (gA (solveFMC P univ t lo hi sd) n) := by
      have := hdom n hnlt; rwa [← solveFMC_eq hwf] at this
    rw [resFMC, solveFMCFun_in_range hwf hnlt]
    exact (incl_iff_sub (α := α) hnd).mp hdn x
      ((mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mpr hxn)
  · rw [resFMC, solveFMCFun_in_range_neg hnlt]
    exact mem_decode_encode.mpr ⟨hceil n x hxn, hbound n x hxn⟩

include hwf hnd hw hlo hhi hlohi hsd in
/-- **Packaged doubly-clamped forward-must correctness for a term** (cap-the-transfer). The decoded
    solution is a valid `MTCSpecC` solution and the greatest one. -/
theorem resFMC_correct :
    MTCSpecC P univ t lo hi sd (resFMC P univ t lo hi sd) ∧
    ∀ h, MTCSpecC P univ t lo hi sd h → ∀ n, ∀ x ∈ h n, x ∈ resFMC P univ t lo hi sd n :=
  ⟨resFMC_valid hwf hnd hw hlo hhi hlohi, fun h hh => resFMC_greatest hwf hnd hw hlo hsd h hh⟩

/-! ## The doubly-clamped forward-**may** generic vertical (**cap-the-transfer** `hi ∩ (lo ∪ gMTCMF)`).

The may dual of `resFMC`: the ceiling `hi` is the aligned (primary) clamp — outermost `∩`, so `h ⊆ hi`
cleanly and it caps the growing transfer *above* (only `evs ∩ hi` need land in `h`); the floor `lo` is the
always-present lower bound (`lo ∪ ·`). Both the `update` and the entry `seed` floor are capped by `hi`.
Least fixpoint via `solveWLMay`; out of range reads the floor `lo`. Needs the band `lo ⊆ hi`. -/

/-- Forward-may, doubly clamped (**cap-the-transfer** may dual): `hi ∩ (lo ∪ gMTCMF)`. The ceiling `hi`
    is the aligned (primary) clamp — outermost `∩`; the floor `lo` is the always-present lower bound. -/
def gFmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  encode univ (hi n) &&& (encode univ (lo n) ||| gMTCMF P univ t sd arr n)

omit [LawfulHashable α] in
theorem gFmC_mono : GMono P (gFmC P univ t lo hi sd) := by
  intro a b hasz hbsz hab n hn
  unfold gFmC
  exact incl_and_mono (incl_refl _) (incl_or_mono (incl_refl _) (gMTCMF_mono a b hasz hbsz hab n hn))

omit [LawfulHashable α] in
theorem gFmC_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (m : Node)
    (hm : m ∉ realizableSucc P nd) :
    gFmC P univ t lo hi sd (arr.set! nd v) m = gFmC P univ t lo hi sd arr m := by
  unfold gFmC
  rw [gMTCMF_hloc arr nd v m hm]

/-- The executable doubly-clamped forward-may term solver (join engine, `realizableSucc` reader). -/
def solveFmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMay P (gFmC P univ t lo hi sd) realizableSucc

omit [LawfulHashable α] in
theorem solveFmC_eq (hwf : WellFormed P) :
    solveFmC P univ t lo hi sd = solveMay P (gFmC P univ t lo hi sd) :=
  solveWL_eq_may gFmC_mono (realizableSucc_readers_in_range hwf)
    (fun arr nd v m hm => gFmC_hloc arr nd v m hm)

omit [LawfulHashable α] in
theorem solveFmC_size (hwf : WellFormed P) : (solveFmC P univ t lo hi sd).size = P.size :=
  solveWL_size (botSeed_size P) (realizableSucc_readers_in_range hwf)

omit [LawfulHashable α] in
theorem solveFmC_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gFmC P univ t lo hi sd (solveFmC P univ t lo hi sd) n) (gA (solveFmC P univ t lo hi sd) n) := by
  have heq := solveMay_eq P (gFmC P univ t lo hi sd) hn
  rw [← solveFmC_eq hwf] at heq
  exact incl_of_or_eq heq

/-- Result as a total function; out of range reads the floor `lo` (mirrors `solveMTCBFun`). -/
def solveFmCFun (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveFmC P univ t lo hi sd
  fun n => if n < P.size then gA arr n else encode univ (lo n)

omit [LawfulHashable α] in
theorem solveFmCFun_app (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) :
    solveFmCFun P univ t lo hi sd n = if n < P.size then gA (solveFmC P univ t lo hi sd) n else encode univ (lo n) := rfl

/-- The decoded doubly-clamped forward-may term solution. -/
def resFmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveFmCFun P univ t lo hi sd n)

include hwf hnd hw hlo hhi hlohi hsd in
theorem resFmC_valid : MTCSpecMFC P univ t lo hi sd (resFmC P univ t lo hi sd) := by
  have harm : ∀ {n : Node}, n < P.size → ∀ {b : ESet univ.length},
      Incl b (gFmC P univ t lo hi sd (solveFmC P univ t lo hi sd) n) →
      ∀ x ∈ decode univ b, x ∈ resFmC P univ t lo hi sd n := by
    intro n hn b hb x hx
    have : x ∈ decode univ (gA (solveFmC P univ t lo hi sd) n) :=
      (incl_iff_sub (α := α) hnd).mp (incl_trans hb (solveFmC_settled hwf hn)) x hx
    rw [resFmC, solveFmCFun_app, if_pos hn]; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- update (capped by ceiling): `x ∈ evs t (h c.node) → x ∈ hi c'.node → x ∈ h c'.node`
    intro c c' hstep x hx hxhi
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    have hcpred : c.node ∈ realizablePred P c'.node := mem_realizablePred.mpr ⟨hclt, hpm⟩
    rw [resFmC, solveFmCFun_app, if_pos hclt] at hx
    refine harm hc'lt (incl_refl _) x ?_
    unfold gFmC
    rw [mem_decode_and hnd, mem_decode_or]
    refine ⟨(mem_decode_encode_of_sub (fun y hy => hhi c'.node y hy)).mpr hxhi, Or.inr ?_⟩
    have hincl : Incl (MTC.evb univ (c.node, c'.node) t (gA (solveFmC P univ t lo hi sd) c.node))
        (gMTCMF P univ t sd (solveFmC P univ t lo hi sd) c'.node) := by
      unfold gMTCMF
      exact incl_trans (joinList_mem_sub
        (fun m => MTC.evb univ (m, c'.node) t (gA (solveFmC P univ t lo hi sd) m)) hcpred) (incl_or_inr _ _)
    exact (incl_iff_sub (α := α) hnd).mp hincl x
      ((MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mpr hx)
  · -- floor: `lo n ⊆ h n`
    intro n x hx
    by_cases hn : n < P.size
    · have hb : Incl (encode univ (lo n)) (gFmC P univ t lo hi sd (solveFmC P univ t lo hi sd) n) := by
        unfold gFmC
        exact incl_and_intro (MTC.encode_mono (fun y hy => hlohi n y hy)) (incl_or_inl _ _)
      exact harm hn hb x ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx)
    · rw [resFmC, solveFmCFun_app, if_neg hn]
      exact (mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx
  · -- ceiling: `h n ⊆ hi n`
    have hceilpre : ∀ m, m < P.size →
        Incl (gFmC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (hi i.val))) m)
          (encode univ (hi m)) := fun m _ => by unfold gFmC; exact incl_and_left _ _
    have hceildom := solveMay_extremal_of_prefix (g := gFmC P univ t lo hi sd) gFmC_mono
      (A := fun k => encode univ (hi k)) hceilpre
    intro n x hx
    by_cases hn : n < P.size
    · rw [resFmC, solveFmCFun_app, if_pos hn] at hx
      have hdn : Incl (gA (solveFmC P univ t lo hi sd) n) (encode univ (hi n)) := by
        have := hceildom n hn; rwa [← solveFmC_eq hwf] at this
      exact (mem_decode_encode.mp ((incl_iff_sub (α := α) hnd).mp hdn x hx)).1
    · rw [resFmC, solveFmCFun_app, if_neg hn] at hx
      exact hlohi n x (mem_decode_encode.mp hx).1
  · -- seed (capped by ceiling): `x ∈ sd → x ∈ hi entry → x ∈ h entry`
    intro x hx hxhi
    refine harm hwf.entry_lt (incl_refl _) x ?_
    unfold gFmC
    rw [mem_decode_and hnd, mem_decode_or]
    refine ⟨(mem_decode_encode_of_sub (fun y hy => hhi P.entry y hy)).mpr hxhi, Or.inr ?_⟩
    have hincl : Incl (encode univ sd) (gMTCMF P univ t sd (solveFmC P univ t lo hi sd) P.entry) := by
      unfold gMTCMF; rw [if_pos rfl]; exact incl_or_inl _ _
    exact (incl_iff_sub (α := α) hnd).mp hincl x ((mem_decode_encode_of_sub (fun y hy => hsd y hy)).mpr hx)
  · -- within the universe
    intro n x hx
    rw [resFmC, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hlo hhi hlohi hsd in
theorem resFmC_least (h : Node → Std.HashSet α) (hh : MTCSpecMFC P univ t lo hi sd h) :
    ∀ n, ∀ x ∈ resFmC P univ t lo hi sd n, x ∈ h n := by
  obtain ⟨hupd, hfloor, hceil, hseed, hbound⟩ := hh
  have hub : ∀ m, ∀ y ∈ h m, y ∈ decode univ (encode univ (h m)) :=
    fun m y hy => (mem_decode_encode_of_sub (fun z hz => hbound m z hz)).mpr hy
  -- `encode ∘ h` is a pre-fixpoint of `gFmC`: the ceiling cap is what makes the capped update land.
  have hpre : ∀ m, m < P.size →
      Incl (gFmC P univ t lo hi sd
          (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m)
        (encode univ (h m)) := by
    intro m hm
    unfold gFmC gMTCMF
    rw [and_or_distrib, and_or_distrib, and_joinList]
    apply incl_or_elim
    · -- `hi ∩ lo ⊆ h`
      exact incl_trans (incl_and_right _ _) (MTC.encode_mono (fun y hy => hfloor m y hy))
    · apply incl_or_elim
      · -- `hi ∩ seed ⊆ h`
        by_cases he : m = P.entry
        · rw [if_pos he]
          apply incl_decode_encode
          intro y hy
          rw [mem_decode_and hnd] at hy
          have hyhi : y ∈ hi m := (mem_decode_encode.mp hy.1).1
          have hysd : y ∈ sd := (mem_decode_encode.mp hy.2).1
          exact he ▸ hseed y hysd (by rw [← he]; exact hyhi)
        · rw [if_neg he, and_zero]; exact incl_zero
      · -- `hi ∩ (join of evb over predecessors) ⊆ h`
        apply joinList_incl
        intro p hp
        have hplt : p < P.size := (mem_realizablePred.mp hp).1
        have hpm : m ∈ realizableSucc P p := (mem_realizablePred.mp hp).2
        obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hpm
        rw [gA_ofFn _ hplt]
        apply incl_decode_encode
        intro y hy
        rw [mem_decode_and hnd] at hy
        have hyhi : y ∈ hi m := (mem_decode_encode.mp hy.1).1
        have hys : y ∈ MTC.evs (p, m) t (decode univ (encode univ (h p))) :=
          (MTC.evb_decode univ hnd (p, m) t _ y hw).mp hy.2
        have hyh : y ∈ MTC.evs (p, m) t (h p) :=
          (MTC.evs_mem_congr (p, m) t (fun z => mem_decode_encode_of_sub (fun w hw2 => hbound p w hw2)) y).mp hys
        exact hupd ⟨p, σ⟩ ⟨m, σ'⟩ hstep y hyh hyhi
  have hdom := solveMay_extremal_of_prefix (g := gFmC P univ t lo hi sd) gFmC_mono
    (A := fun k => encode univ (h k)) hpre
  intro n x hx
  by_cases hn : n < P.size
  · rw [resFmC, solveFmCFun_app, if_pos hn] at hx
    have hdn : Incl (gA (solveFmC P univ t lo hi sd) n) (encode univ (h n)) := by
      have := hdom n hn; rwa [← solveFmC_eq hwf] at this
    exact (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mp
      ((incl_iff_sub (α := α) hnd).mp hdn x hx)
  · rw [resFmC, solveFmCFun_app, if_neg hn] at hx
    exact hfloor n x ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mp hx)

include hwf hnd hw hlo hhi hlohi hsd in
/-- **Packaged doubly-clamped forward-may correctness for a term** (cap-the-transfer, may dual). -/
theorem resFmC_correct :
    MTCSpecMFC P univ t lo hi sd (resFmC P univ t lo hi sd) ∧
    ∀ h, MTCSpecMFC P univ t lo hi sd h → ∀ n, ∀ x ∈ resFmC P univ t lo hi sd n, x ∈ h n :=
  ⟨resFmC_valid hwf hnd hw hlo hsd hhi hlohi, fun h hh => resFmC_least hwf hnd hw hlo hsd hhi hlohi h hh⟩

/-! ## The doubly-clamped backward-**must** generic vertical (**cap-the-transfer** `lo ∪ gMTCBM`).

The backward `resFMC` (boundary at `halt`): `gMTCBM` already carries the aligned ceiling `hi` (and the
`halt`-boundary ceiling `sd`); here we add the opposite-polarity floor `lo` as the outer `∪`. Clean because
`lo ∪ (hi ∩ core) = hi ∩ (lo ∪ core)` when `lo ⊆ hi`: the floor relaxes both the `update`
(`h c.node ⊆ evs ∪ lo`) and the `halt`-seed (`⊆ sd ∪ lo`). Greatest fixpoint via `solveWLMust`,
`realizablePred` reader; out of range reads the ceiling `hi`. Needs the band `lo ⊆ hi`. -/

/-- Backward-must, doubly clamped (**cap-the-transfer**): `lo ∪ gMTCBM`. The floor `lo` is the outer `∪`
    (opposite-polarity); `gMTCBM` carries the aligned ceiling `hi`. -/
def gBMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  encode univ (lo n) ||| gMTCBM P univ t hi sd arr n

omit [LawfulHashable α] in
theorem gBMC_mono : GMono P (gBMC P univ t lo hi sd) := by
  intro a b hasz hbsz hab n hn
  unfold gBMC
  exact incl_or_mono (incl_refl _) (gMTCBM_mono a b hasz hbsz hab n hn)

omit [LawfulHashable α] in
theorem gBMC_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (n : Node)
    (hn : n ∉ realizablePred P nd) :
    gBMC P univ t lo hi sd (arr.set! nd v) n = gBMC P univ t lo hi sd arr n := by
  unfold gBMC
  rw [gMTCBM_hloc arr nd v n hn]

/-- The executable doubly-clamped backward-must term solver (meet engine, `realizablePred` reader). -/
def solveBMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMust P (gBMC P univ t lo hi sd) realizablePred

omit [LawfulHashable α] in
theorem solveBMC_eq (hwf : WellFormed P) :
    solveBMC P univ t lo hi sd = solveMust P (gBMC P univ t lo hi sd) :=
  solveWL_eq_must gBMC_mono (fun nd => realizablePred_readers_in_range nd)
    (fun arr nd v n hn => gBMC_hloc arr nd v n hn)

omit [LawfulHashable α] in
theorem solveBMC_size (hwf : WellFormed P) : (solveBMC P univ t lo hi sd).size = P.size := by
  rw [solveBMC_eq hwf]; exact solveMust_size P (gBMC P univ t lo hi sd)

omit [LawfulHashable α] in
theorem solveBMC_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gA (solveBMC P univ t lo hi sd) n) (gBMC P univ t lo hi sd (solveBMC P univ t lo hi sd) n) := by
  have heq := solveMust_eq P (gBMC P univ t lo hi sd) hn
  rw [← solveBMC_eq hwf] at heq
  exact incl_of_and_eq heq

/-- Result as a total function; out of range reads the ceiling `hi` (mirrors `solveMTCBMFun`). -/
def solveBMCFun (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveBMC P univ t lo hi sd
  fun n => if n < P.size then gA arr n else encode univ (hi n)

omit [LawfulHashable α] in
theorem solveBMCFun_in_range (hwf : WellFormed P) {m : Node} (hm : m < P.size) :
    solveBMCFun P univ t lo hi sd m = gA (solveBMC P univ t lo hi sd) m := by
  show (if m < P.size then _ else _) = _; rw [if_pos hm]

omit [LawfulHashable α] in
theorem solveBMCFun_in_range_neg {m : Node} (hm : ¬ m < P.size) :
    solveBMCFun P univ t lo hi sd m = encode univ (hi m) := by
  show (if m < P.size then _ else _) = _; rw [if_neg hm]

/-- The decoded doubly-clamped backward-must term solution. -/
def resBMC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveBMCFun P univ t lo hi sd n)

include hwf hnd hw hlo hhi hlohi in
theorem resBMC_valid : MTCSpecBMC P univ t lo hi sd (resBMC P univ t lo hi sd) := by
  have hfloorpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (lo k)) m)
        (gBMC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (lo i.val))) m) := by
    intro m _
    unfold gBMC; exact incl_or_inl _ _
  have hfloordom := solveMust_extremal_of_postfix (g := gBMC P univ t lo hi sd) gBMC_mono
    (A := fun k => encode univ (lo k)) hfloorpost
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- update (cap-the-transfer): `x ∈ h c.node → x ∈ evs t (h c'.node) ∨ x ∈ lo c.node`
    intro c c' hstep x hx
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    rw [resBMC, solveBMCFun_in_range hwf hclt] at hx
    have hincl : Incl (gA (solveBMC P univ t lo hi sd) c.node)
        (encode univ (lo c.node) ||| MTC.evb univ (c.node, c'.node) t (gA (solveBMC P univ t lo hi sd) c'.node)) := by
      refine incl_trans (solveBMC_settled hwf hclt) ?_
      unfold gBMC
      refine incl_or_mono (incl_refl _) ?_
      unfold gMTCBM
      refine incl_trans (incl_and_right _ _) ?_
      have hnh : ¬ isHalt P c.node := by
        intro he
        have hf : P.fetch c.node = some .halt := by simpa [isHalt] using he
        have he0 : realizableSucc P c.node = [] := by simp [realizableSucc, hf]
        rw [he0] at hpm; simp at hpm
      rw [if_neg hnh]; exact meetList_sub_mem _ hpm
    have hmem : x ∈ decode univ (encode univ (lo c.node) |||
        MTC.evb univ (c.node, c'.node) t (gA (solveBMC P univ t lo hi sd) c'.node)) :=
      (incl_iff_sub (α := α) hnd).mp hincl x hx
    rw [mem_decode_or] at hmem
    rcases hmem with hlom | hevb
    · exact Or.inr (mem_decode_encode.mp hlom).1
    · refine Or.inl ?_
      rw [resBMC, solveBMCFun_in_range hwf hc'lt]
      exact (MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mp hevb
  · -- floor: `lo n ⊆ h n`
    intro n x hx
    by_cases hn : n < P.size
    · have hdn : Incl (encode univ (lo n)) (gA (solveBMC P univ t lo hi sd) n) := by
        have := hfloordom n hn; rwa [← solveBMC_eq hwf] at this
      rw [resBMC, solveBMCFun_in_range hwf hn]
      exact (incl_iff_sub (α := α) hnd).mp hdn x
        ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx)
    · rw [resBMC, solveBMCFun_in_range_neg hn]
      exact (mem_decode_encode_of_sub (fun y hy => hhi n y hy)).mpr (hlohi n x hx)
  · -- ceiling: `h n ⊆ hi n`
    intro n x hx
    by_cases hn : n < P.size
    · rw [resBMC, solveBMCFun_in_range hwf hn] at hx
      have hcap : Incl (gBMC P univ t lo hi sd (solveBMC P univ t lo hi sd) n) (encode univ (hi n)) := by
        unfold gBMC
        exact incl_or_elim (MTC.encode_mono (fun y hy => hlohi n y hy))
          (by unfold gMTCBM; exact incl_and_left _ _)
      have : x ∈ decode univ (encode univ (hi n)) :=
        (incl_iff_sub (α := α) hnd).mp (incl_trans (solveBMC_settled hwf hn) hcap) x hx
      exact (mem_decode_encode.mp this).1
    · rw [resBMC, solveBMCFun_in_range_neg hn] at hx
      exact (mem_decode_encode.mp hx).1
  · -- halt-seed (relaxed ceiling): `x ∈ h(halt) → x ∈ sd ∨ x ∈ lo(halt)`
    intro c hhalt x hx
    have hnlt : c.node < P.size := fetch_lt hhalt
    have hhb : isHalt P c.node = true := by simp [isHalt, hhalt]
    rw [resBMC, solveBMCFun_in_range hwf hnlt] at hx
    have hcap : Incl (gBMC P univ t lo hi sd (solveBMC P univ t lo hi sd) c.node)
        (encode univ (lo c.node) ||| encode univ sd) := by
      unfold gBMC
      refine incl_or_mono (incl_refl _) ?_
      unfold gMTCBM; rw [if_pos hhb]; exact incl_and_right _ _
    have hmem : x ∈ decode univ (encode univ (lo c.node) ||| encode univ sd) :=
      (incl_iff_sub (α := α) hnd).mp (incl_trans (solveBMC_settled hwf hnlt) hcap) x hx
    rw [mem_decode_or] at hmem
    rcases hmem with hl | hs
    · exact Or.inr (mem_decode_encode.mp hl).1
    · exact Or.inl (mem_decode_encode.mp hs).1
  · -- within the universe
    intro n x hx
    rw [resBMC, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hlo hsd in
theorem resBMC_greatest (h : Node → Std.HashSet α) (hh : MTCSpecBMC P univ t lo hi sd h) :
    ∀ n, ∀ x ∈ h n, x ∈ resBMC P univ t lo hi sd n := by
  obtain ⟨hupd, hfloor, hceil, hseed, hbound⟩ := hh
  have hpost : ∀ m, m < P.size →
      Incl ((fun k => encode univ (h k)) m)
        (gBMC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m) := by
    intro m hm
    unfold gBMC gMTCBM
    rw [or_and_distrib]
    apply incl_and_intro
    · -- `h m ⊆ lo m ∪ hi m` (via the ceiling clause)
      exact incl_trans (MTC.encode_mono (fun y hy => hceil m y hy)) (incl_or_inr _ _)
    · by_cases he : isHalt P m
      · -- `halt`-seed cap, relaxed by `lo`
        rw [if_pos he]
        have hhalt : P.fetch m = some .halt := by simpa [isHalt] using he
        apply encode_incl_decode hnd
        intro y hy
        rw [mem_decode_or]
        rcases hseed ⟨m, Store.init⟩ hhalt y hy with hs | hl
        · exact Or.inr ((mem_decode_encode_of_sub (fun z hz => hsd z hz)).mpr hs)
        · exact Or.inl ((mem_decode_encode_of_sub (fun z hz => hlo m z hz)).mpr hl)
      · -- meet over realizable successors (each edge's `update`, relaxed by `lo`)
        rw [if_neg he, or_meetList]
        apply incl_meetList
        intro m' hm'
        have hm'lt : m' < P.size := realizableSucc_lt hwf hm'
        obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hm'
        rw [gA_ofFn _ hm'lt]
        apply encode_incl_decode hnd
        intro y hy
        rw [mem_decode_or]
        rcases hupd ⟨m, σ⟩ ⟨m', σ'⟩ hstep y hy with hev | hl
        · refine Or.inr ?_
          have hcong : y ∈ MTC.evs (m, m') t (decode univ (encode univ (h m'))) :=
            (MTC.evs_mem_congr (m, m') t
              (fun z => (mem_decode_encode_of_sub (fun w hw2 => hbound m' w hw2)).symm) y).mp hev
          exact (MTC.evb_decode univ hnd (m, m') t _ y hw).mpr hcong
        · exact Or.inl ((mem_decode_encode_of_sub (fun z hz => hlo m z hz)).mpr hl)
  have hdom := solveMust_extremal_of_postfix (g := gBMC P univ t lo hi sd) gBMC_mono
    (A := fun k => encode univ (h k)) hpost
  intro n x hxn
  by_cases hnlt : n < P.size
  · have hdn : Incl (encode univ (h n)) (gA (solveBMC P univ t lo hi sd) n) := by
      have := hdom n hnlt; rwa [← solveBMC_eq hwf] at this
    rw [resBMC, solveBMCFun_in_range hwf hnlt]
    exact (incl_iff_sub (α := α) hnd).mp hdn x
      ((mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mpr hxn)
  · rw [resBMC, solveBMCFun_in_range_neg hnlt]
    exact mem_decode_encode.mpr ⟨hceil n x hxn, hbound n x hxn⟩

include hwf hnd hw hlo hhi hlohi hsd in
/-- **Packaged doubly-clamped backward-must correctness for a term** (cap-the-transfer, `halt` boundary). -/
theorem resBMC_correct :
    MTCSpecBMC P univ t lo hi sd (resBMC P univ t lo hi sd) ∧
    ∀ h, MTCSpecBMC P univ t lo hi sd h → ∀ n, ∀ x ∈ h n, x ∈ resBMC P univ t lo hi sd n :=
  ⟨resBMC_valid hwf hnd hw hlo hhi hlohi, fun h hh => resBMC_greatest hwf hnd hw hlo hsd h hh⟩

/-! ## The doubly-clamped backward-**may** generic vertical (**cap-the-transfer** `hi ∩ gMTCB`).

The backward `resFmC` (boundary at `halt`), and the may dual of `resBMC`: `gMTCB` already carries the
aligned floor `lo` (and the `halt`-boundary floor `sd`); here we add the opposite-polarity ceiling `hi`
as the outer `∩`. It caps the growing transfer *above* (only `evs ∩ hi` need land in `h`) and the
`halt`-seed floor (`sd ∩ hi`). Least fixpoint via `solveWLMay`, `realizablePred` reader; out of range
reads the floor `lo`. Needs the band `lo ⊆ hi`. -/

/-- Backward-may, doubly clamped (**cap-the-transfer** may dual): `hi ∩ gMTCB`. The ceiling `hi` is the
    outer `∩` (opposite-polarity); `gMTCB` carries the aligned floor `lo`. -/
def gBmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α) (sd : Std.HashSet α)
    (arr : Array (ESet univ.length)) (n : Node) : ESet univ.length :=
  encode univ (hi n) &&& gMTCB P univ t lo sd arr n

omit [LawfulHashable α] in
theorem gBmC_mono : GMono P (gBmC P univ t lo hi sd) := by
  intro a b hasz hbsz hab n hn
  unfold gBmC
  exact incl_and_mono (incl_refl _) (gMTCB_mono a b hasz hbsz hab n hn)

omit [LawfulHashable α] in
theorem gBmC_hloc (arr : Array (ESet univ.length)) (nd : Node) (v : ESet univ.length) (n : Node)
    (hn : n ∉ realizablePred P nd) :
    gBmC P univ t lo hi sd (arr.set! nd v) n = gBmC P univ t lo hi sd arr n := by
  unfold gBmC
  rw [gMTCB_hloc arr nd v n hn]

/-- The executable doubly-clamped backward-may term solver (join engine, `realizablePred` reader). -/
def solveBmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Array (ESet univ.length) :=
  solveWLMay P (gBmC P univ t lo hi sd) realizablePred

omit [LawfulHashable α] in
theorem solveBmC_eq (hwf : WellFormed P) :
    solveBmC P univ t lo hi sd = solveMay P (gBmC P univ t lo hi sd) :=
  solveWL_eq_may gBmC_mono (fun nd => realizablePred_readers_in_range nd)
    (fun arr nd v n hn => gBmC_hloc arr nd v n hn)

omit [LawfulHashable α] in
theorem solveBmC_size (hwf : WellFormed P) : (solveBmC P univ t lo hi sd).size = P.size :=
  solveWL_size (botSeed_size P) (fun nd => realizablePred_readers_in_range nd)

omit [LawfulHashable α] in
theorem solveBmC_settled (hwf : WellFormed P) {n : Node} (hn : n < P.size) :
    Incl (gBmC P univ t lo hi sd (solveBmC P univ t lo hi sd) n) (gA (solveBmC P univ t lo hi sd) n) := by
  have heq := solveMay_eq P (gBmC P univ t lo hi sd) hn
  rw [← solveBmC_eq hwf] at heq
  exact incl_of_or_eq heq

/-- Result as a total function; out of range reads the floor `lo` (mirrors `solveMTCBFun`). -/
def solveBmCFun (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → ESet univ.length :=
  let arr := solveBmC P univ t lo hi sd
  fun n => if n < P.size then gA arr n else encode univ (lo n)

omit [LawfulHashable α] in
theorem solveBmCFun_app (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) :
    solveBmCFun P univ t lo hi sd n = if n < P.size then gA (solveBmC P univ t lo hi sd) n else encode univ (lo n) := rfl

/-- The decoded doubly-clamped backward-may term solution. -/
def resBmC (P : Program) (univ : List α) (t : MTC α) (lo hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) (n : Node) : Std.HashSet α :=
  decode univ (solveBmCFun P univ t lo hi sd n)

include hwf hnd hw hlo hhi hlohi hsd in
theorem resBmC_valid : MTCSpecBC P univ t lo hi sd (resBmC P univ t lo hi sd) := by
  have harm : ∀ {n : Node}, n < P.size → ∀ {b : ESet univ.length},
      Incl b (gBmC P univ t lo hi sd (solveBmC P univ t lo hi sd) n) →
      ∀ x ∈ decode univ b, x ∈ resBmC P univ t lo hi sd n := by
    intro n hn b hb x hx
    have : x ∈ decode univ (gA (solveBmC P univ t lo hi sd) n) :=
      (incl_iff_sub (α := α) hnd).mp (incl_trans hb (solveBmC_settled hwf hn)) x hx
    rw [resBmC, solveBmCFun_app, if_pos hn]; exact this
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- update (capped by ceiling): `x ∈ evs t (h c'.node) → x ∈ hi c.node → x ∈ h c.node`
    intro c c' hstep x hx hxhi
    have hpm : c'.node ∈ realizableSucc P c.node := realizable_iff_step.mp ⟨c.store, c'.store, hstep⟩
    have hclt : c.node < P.size := succList_mem_lt (realizableSucc_subset_succList hpm)
    have hc'lt : c'.node < P.size := realizableSucc_lt hwf hpm
    rw [resBmC, solveBmCFun_app, if_pos hc'lt] at hx
    refine harm hclt (incl_refl _) x ?_
    unfold gBmC
    rw [mem_decode_and hnd]
    refine ⟨(mem_decode_encode_of_sub (fun y hy => hhi c.node y hy)).mpr hxhi, ?_⟩
    have hincl : Incl (MTC.evb univ (c.node, c'.node) t (gA (solveBmC P univ t lo hi sd) c'.node))
        (gMTCB P univ t lo sd (solveBmC P univ t lo hi sd) c.node) := by
      unfold gMTCB
      exact incl_trans (joinList_mem_sub
        (fun m => MTC.evb univ (c.node, m) t (gA (solveBmC P univ t lo hi sd) m)) hpm) (incl_or_inr _ _)
    exact (incl_iff_sub (α := α) hnd).mp hincl x
      ((MTC.evb_decode univ hnd (c.node, c'.node) t _ x hw).mpr hx)
  · -- floor: `lo n ⊆ h n`
    intro n x hx
    by_cases hn : n < P.size
    · have hb : Incl (encode univ (lo n)) (gBmC P univ t lo hi sd (solveBmC P univ t lo hi sd) n) := by
        unfold gBmC
        refine incl_and_intro (MTC.encode_mono (fun y hy => hlohi n y hy)) ?_
        unfold gMTCB; exact incl_trans (incl_or_inl _ _) (incl_or_inl _ _)
      exact harm hn hb x ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx)
    · rw [resBmC, solveBmCFun_app, if_neg hn]
      exact (mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mpr hx
  · -- ceiling: `h n ⊆ hi n`
    have hceilpre : ∀ m, m < P.size →
        Incl (gBmC P univ t lo hi sd (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (hi i.val))) m)
          (encode univ (hi m)) := fun m _ => by unfold gBmC; exact incl_and_left _ _
    have hceildom := solveMay_extremal_of_prefix (g := gBmC P univ t lo hi sd) gBmC_mono
      (A := fun k => encode univ (hi k)) hceilpre
    intro n x hx
    by_cases hn : n < P.size
    · rw [resBmC, solveBmCFun_app, if_pos hn] at hx
      have hdn : Incl (gA (solveBmC P univ t lo hi sd) n) (encode univ (hi n)) := by
        have := hceildom n hn; rwa [← solveBmC_eq hwf] at this
      exact (mem_decode_encode.mp ((incl_iff_sub (α := α) hnd).mp hdn x hx)).1
    · rw [resBmC, solveBmCFun_app, if_neg hn] at hx
      exact hlohi n x (mem_decode_encode.mp hx).1
  · -- halt-seed (capped by ceiling): `x ∈ sd → x ∈ hi(halt) → x ∈ h(halt)`
    intro c hhalt x hx hxhi
    have hnlt : c.node < P.size := fetch_lt hhalt
    have hhb : isHalt P c.node = true := by simp [isHalt, hhalt]
    refine harm hnlt (incl_refl _) x ?_
    unfold gBmC
    rw [mem_decode_and hnd]
    refine ⟨(mem_decode_encode_of_sub (fun y hy => hhi c.node y hy)).mpr hxhi, ?_⟩
    have hincl : Incl (encode univ sd) (gMTCB P univ t lo sd (solveBmC P univ t lo hi sd) c.node) := by
      unfold gMTCB; rw [if_pos hhb]
      exact incl_trans (incl_or_inr _ _) (incl_or_inl _ _)
    exact (incl_iff_sub (α := α) hnd).mp hincl x ((mem_decode_encode_of_sub (fun y hy => hsd y hy)).mpr hx)
  · -- within the universe
    intro n x hx
    rw [resBmC, mem_decode] at hx
    obtain ⟨q, hq, _, hqx⟩ := hx
    exact mem_iff_exists_zipIdx.mpr ⟨q, hq, hqx⟩

include hwf hnd hw hlo hhi hlohi hsd in
theorem resBmC_least (h : Node → Std.HashSet α) (hh : MTCSpecBC P univ t lo hi sd h) :
    ∀ n, ∀ x ∈ resBmC P univ t lo hi sd n, x ∈ h n := by
  obtain ⟨hupd, hfloor, hceil, hseed, hbound⟩ := hh
  have hpre : ∀ m, m < P.size →
      Incl (gBmC P univ t lo hi sd
          (Array.ofFn (n := P.size) (fun i : Fin P.size => encode univ (h i.val))) m)
        (encode univ (h m)) := by
    intro m hm
    unfold gBmC gMTCB
    rw [and_or_distrib, and_or_distrib, and_joinList]
    apply incl_or_elim
    · apply incl_or_elim
      · -- `hi ∩ lo ⊆ h`
        exact incl_trans (incl_and_right _ _) (MTC.encode_mono (fun y hy => hfloor m y hy))
      · -- `hi ∩ (halt-seed) ⊆ h`
        by_cases he : isHalt P m
        · rw [if_pos he]
          have hhalt : P.fetch m = some .halt := by simpa [isHalt] using he
          apply incl_decode_encode
          intro y hy
          rw [mem_decode_and hnd] at hy
          have hyhi : y ∈ hi m := (mem_decode_encode.mp hy.1).1
          have hysd : y ∈ sd := (mem_decode_encode.mp hy.2).1
          exact hseed ⟨m, Store.init⟩ hhalt y hysd hyhi
        · rw [if_neg he, and_zero]; exact incl_zero
    · -- `hi ∩ (join of evb over successors) ⊆ h`
      apply joinList_incl
      intro m' hm'
      have hm'lt : m' < P.size := realizableSucc_lt hwf hm'
      obtain ⟨σ, σ', hstep⟩ := realizable_iff_step.mpr hm'
      rw [gA_ofFn _ hm'lt]
      apply incl_decode_encode
      intro y hy
      rw [mem_decode_and hnd] at hy
      have hyhi : y ∈ hi m := (mem_decode_encode.mp hy.1).1
      have hys : y ∈ MTC.evs (m, m') t (decode univ (encode univ (h m'))) :=
        (MTC.evb_decode univ hnd (m, m') t _ y hw).mp hy.2
      have hyh : y ∈ MTC.evs (m, m') t (h m') :=
        (MTC.evs_mem_congr (m, m') t (fun z => mem_decode_encode_of_sub (fun w hw2 => hbound m' w hw2)) y).mp hys
      exact hupd ⟨m, σ⟩ ⟨m', σ'⟩ hstep y hyh hyhi
  have hdom := solveMay_extremal_of_prefix (g := gBmC P univ t lo hi sd) gBmC_mono
    (A := fun k => encode univ (h k)) hpre
  intro n x hx
  by_cases hn : n < P.size
  · rw [resBmC, solveBmCFun_app, if_pos hn] at hx
    have hdn : Incl (gA (solveBmC P univ t lo hi sd) n) (encode univ (h n)) := by
      have := hdom n hn; rwa [← solveBmC_eq hwf] at this
    exact (mem_decode_encode_of_sub (fun y hy => hbound n y hy)).mp
      ((incl_iff_sub (α := α) hnd).mp hdn x hx)
  · rw [resBmC, solveBmCFun_app, if_neg hn] at hx
    exact hfloor n x ((mem_decode_encode_of_sub (fun y hy => hlo n y hy)).mp hx)

include hwf hnd hw hlo hhi hlohi hsd in
/-- **Packaged doubly-clamped backward-may correctness for a term** (cap-the-transfer, may dual). -/
theorem resBmC_correct :
    MTCSpecBC P univ t lo hi sd (resBmC P univ t lo hi sd) ∧
    ∀ h, MTCSpecBC P univ t lo hi sd h → ∀ n, ∀ x ∈ resBmC P univ t lo hi sd n, x ∈ h n :=
  ⟨resBmC_valid hwf hnd hw hlo hsd hhi hlohi, fun h hh => resBmC_least hwf hnd hw hlo hsd hhi hlohi h hh⟩

/-! ## Smoke test — the reified path reproduces forward-must gen/kill (à la `Sink`/`Available`),
    with the transfer written as a term and correctness obtained from the single generic theorem. -/

section GenKill
variable (gen kill : Node → Std.HashSet α)

/-- `Sink`/`Available`-shape transfer as a term: `gen ∪ (X ∩ kill)`. Node-locals ignore the edge's
    second endpoint (`fun e => gen e.1`) — a node transfer is the sublanguage of the edge calculus. -/
def genKillT : MTC α := .union (.const (fun e => gen e.1)) (.inter .var (.const (fun e => kill e.1)))

/-- Its set denotation is exactly the gen/kill update RHS, so `MTCSpec (genKillT …)` *is* the ghost's
    `update`/`seed`/`bound` — no bridge lemma needed, it holds definitionally. -/
example (e : Node × Node) (X : Std.HashSet α) :
    MTC.evs e (genKillT gen kill) X
      = Std.HashSet.union (gen e.1) (X.filter (fun y => (kill e.1).contains y)) := rfl

/-- Generic gen/kill correctness, straight from `resMTC_correct`. -/
example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hg : ∀ n, ∀ x ∈ gen n, x ∈ univ) (hk : ∀ n, ∀ x ∈ kill n, x ∈ univ) (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpec P univ (genKillT gen kill) sd (resMTC P univ (genKillT gen kill) sd) ∧
    ∀ h, MTCSpec P univ (genKillT gen kill) sd h →
        ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ (genKillT gen kill) sd n :=
  resMTC_correct hwf hnd ⟨fun e => hg e.1, ⟨by trivial, fun e => hk e.1⟩⟩ hsd

end GenKill

/-! ## Smoke test — an **edge** transfer (LCM `Postponable`-shape): `earliest(p→m) ∪ (X ∩ transp(p))`,
    with `earliest` reading *both* endpoints of the edge. In the unified calculus this is just a `const`
    whose leaf reads `e = (p, m)` — no separate edge vertical, handled by the same `resMTC_correct`. -/
section Edge
variable (earliest : Node → Node → Std.HashSet α) (transp : Node → Std.HashSet α)

/-- Edge gen/kill as a term: `gen` reads the edge `(e.1, e.2)`. -/
def edgeT : MTC α := .union (.const (fun e => earliest e.1 e.2)) (.inter .var (.const (fun e => transp e.1)))

/-- Its denotation reads the full edge `(a, b)`. -/
example (e : Node × Node) (X : Std.HashSet α) :
    MTC.evs e (edgeT earliest transp) X
      = Std.HashSet.union (earliest e.1 e.2) (X.filter (fun y => (transp e.1).contains y)) := rfl

example (hwf : WellFormed P) (hnd : univ.Nodup)
    (he : ∀ p m, ∀ x ∈ earliest p m, x ∈ univ) (ht : ∀ n, ∀ x ∈ transp n, x ∈ univ) (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpec P univ (edgeT earliest transp) sd (resMTC P univ (edgeT earliest transp) sd) ∧
    ∀ h, MTCSpec P univ (edgeT earliest transp) sd h →
        ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ (edgeT earliest transp) sd n :=
  resMTC_correct hwf hnd ⟨fun e => he e.1 e.2, ⟨by trivial, fun e => ht e.1⟩⟩ hsd

end Edge

/-! ## Smoke test — a **gated** (non-separable) transfer, beyond gen/kill, still handled by the one
    generic theorem.  `gen ∪ gate(sng → res)` fires `res` only when the incoming value overlaps `sng`
    (the faint-liveness shape), which no `gen ∪ (X ∩ transp)` can express. -/
section Gated
variable (gen sng res : Node → Std.HashSet α)

def gatedT : MTC α := .union (.const (fun e => gen e.1)) (.gate (fun e => sng e.1) (fun e => res e.1))

example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hg : ∀ n, ∀ x ∈ gen n, x ∈ univ) (hs : ∀ n, ∀ x ∈ sng n, x ∈ univ)
    (hr : ∀ n, ∀ x ∈ res n, x ∈ univ) (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpec P univ (gatedT gen sng res) sd (resMTC P univ (gatedT gen sng res) sd) ∧
    ∀ h, MTCSpec P univ (gatedT gen sng res) sd h →
        ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ (gatedT gen sng res) sd n :=
  resMTC_correct hwf hnd ⟨fun e => hg e.1, ⟨fun e => hs e.1, fun e => hr e.1⟩⟩ hsd

end Gated

/-! ## Smoke test — a **gather** (AND-gather) transfer: "available if generated, or all subexpressions
    available".  `gen ∪ gather(sub)` needs a cross-element AND over subexpressions — the canonical
    example that flat gen/kill cannot express — yet the one generic theorem still solves it. With `∪`,
    `∩`, `gate`, `image`, and `gather`, the calculus reaches every monotone transfer over a finite `U`. -/
section Gathers
variable (gen : Node → Std.HashSet α) (U : Std.HashSet α) (sub : α → Std.HashSet α)

def structAvailT : MTC α := .union (.const (fun e => gen e.1)) (.gather U (fun _ => sub))

example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hg : ∀ n, ∀ x ∈ gen n, x ∈ univ) (hU : ∀ x ∈ U, x ∈ univ) (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpec P univ (structAvailT gen U sub) sd (resMTC P univ (structAvailT gen U sub) sd) ∧
    ∀ h, MTCSpec P univ (structAvailT gen U sub) sd h →
        ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ (structAvailT gen U sub) sd n :=
  resMTC_correct hwf hnd ⟨fun e => hg e.1, hU⟩ hsd

end Gathers

/-! ## Smoke test — the **opposite corner**: backward-**may** liveness from the *same* term calculus.
    `live(n) = use(n) ∪ (live(succ) ∖ def(n))` is the term `use ∪ (X ∖ def)`; driven by `resMTCB_correct`
    (join over successors, least, `sd` seed at `halt`) it yields the full liveness fixpoint — same `MTC`,
    same four structural lemmas as the forward-must path above, only the solver parameters flipped. -/
section Liveness
variable (use deff : Node → Std.HashSet α)

/-- Liveness transfer as a term: `use ∪ (X ∖ def)`. -/
def liveT : MTC α := .union (.const (fun e => use e.1)) (.diffc .var (fun e => deff e.1))

/-- Its set denotation is exactly the liveness update RHS. -/
example (e : Node × Node) (X : Std.HashSet α) :
    MTC.evs e (liveT use deff) X
      = Std.HashSet.union (use e.1) (X.filter (fun y => !(deff e.1).contains y)) := rfl

/-- Generic backward-may (liveness) correctness, straight from `resMTCB_correct`. `use` is folded into the
    transfer term (a `const` arm), so the per-node floor `lo` is empty. -/
example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hu : ∀ n, ∀ x ∈ use n, x ∈ univ) (hd : ∀ n, ∀ x ∈ deff n, x ∈ univ)
    (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpecB P univ (liveT use deff) (fun _ => ∅) sd (resMTCB P univ (liveT use deff) (fun _ => ∅) sd) ∧
    ∀ h, MTCSpecB P univ (liveT use deff) (fun _ => ∅) sd h →
        ∀ n, ∀ x ∈ resMTCB P univ (liveT use deff) (fun _ => ∅) sd n, x ∈ h n :=
  resMTCB_correct hwf hnd (t := liveT use deff) (lo := fun _ => ∅)
    ⟨fun e => hu e.1, trivial, fun e => hd e.1⟩ (fun _ x hx => absurd hx Std.HashSet.not_mem_empty) hsd

end Liveness

/-! ## Smoke test — **forward-may** reaching definitions from the same `gen ∪ (X ∖ kill)` term, via
    `resMTCMF_correct` (join over predecessors, least, `sd` seed at `entry`). -/
section Reaching
variable (gen kill : Node → Std.HashSet α)

def reachT : MTC α := .union (.const (fun e => gen e.1)) (.diffc .var (fun e => kill e.1))

example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hg : ∀ n, ∀ x ∈ gen n, x ∈ univ) (hk : ∀ n, ∀ x ∈ kill n, x ∈ univ)
    (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpecMF P univ (reachT gen kill) sd (resMTCMF P univ (reachT gen kill) sd) ∧
    ∀ h, MTCSpecMF P univ (reachT gen kill) sd h →
        ∀ n, ∀ x ∈ resMTCMF P univ (reachT gen kill) sd n, x ∈ h n :=
  resMTCMF_correct hwf hnd (t := reachT gen kill) ⟨fun e => hg e.1, trivial, fun e => hk e.1⟩ hsd

end Reaching

/-! ## Smoke test — **backward-must** very-busy / anticipated expressions from the liveness-shape term
    `use ∪ (X ∖ def)`, via `resMTCBM_correct` (meet over successors, greatest, `∅` at `halt`). -/
section VeryBusy
variable (use deff : Node → Std.HashSet α)

def antiT : MTC α := .union (.const (fun e => use e.1)) (.diffc .var (fun e => deff e.1))

example (hwf : WellFormed P) (hnd : univ.Nodup)
    (hu : ∀ n, ∀ x ∈ use n, x ∈ univ) (hd : ∀ n, ∀ x ∈ deff n, x ∈ univ) (hi : Node → Std.HashSet α)
    (hsd : ∀ x ∈ sd, x ∈ univ) :
    MTCSpecBM P univ (antiT use deff) hi sd (resMTCBM P univ (antiT use deff) hi sd) ∧
    ∀ h, MTCSpecBM P univ (antiT use deff) hi sd h →
        ∀ n, ∀ x ∈ h n, x ∈ resMTCBM P univ (antiT use deff) hi sd n :=
  resMTCBM_correct hwf hnd (t := antiT use deff) (hi := hi) ⟨fun e => hu e.1, trivial, fun e => hd e.1⟩ hsd

end VeryBusy

end Solver
