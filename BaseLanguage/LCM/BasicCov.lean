-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness

/-!
# `BasicCov` — coverage lemmas for the *basic* LCM insert (isolated insertions permitted)

The basic variant drops the `Used` analysis (`π_u`/`τ_u`): it inserts at every latest node/edge and replaces
every numbered computation. Its insert sets are the optimal ones with `∩ τᵤ` removed, hence
**supersets**: `insertBefore ⊆ insBefore'`, `insertOut ⊆ insOut'`, `insertAfter ⊆ insOut'`,
`insertEdge ⊆ latestEdge`.

## What this file establishes

* **Fault safety (`π_u`-free).** `insBefore'_sub_anti`: every basic node insert is anticipated
  (`insBefore' ⊆ latestNode ⊆ ηₚ ⊆ πₐ`), using the threaded `ηₚ ⊆ πₐ` invariant
  (`postpSubAnti_step`, itself `π_u`-free). So the *extra* isolated inserts are down-safe — no new faults.

* **Coverage.** `cov_implies_cov_basic`: the basic coverage `Cov_basic`
  (keyed on computations `ue`) follows from `Cov` (keyed on `πᵤ`) via the `Used.check`
  clause + the insert containments. `mstep_edge_sub`: the basic materialized set dominates the optimal one.
  Together `Cov_basic_step` maintains basic coverage across a step by reusing `Cov_step_edge`.
  (`Extremal S` stays a proof scaffold; the basic *transform* output uses no `π_u`.)

* **Blast radius.** `match_step_assign` (in `Correctness/MatchStep.lean`) takes `_hpa : ηₚ ⊆ πₐ` and
  `hcovered` (the covered-read obligation) and touches `πᵤ`/`recoverable` only via the `recoverable`-gate and `hcovered`, so porting to
  the basic transform is: gate ⟶ `numbered`, `Cov ⟶ Cov_basic` (this file), everything else reused.

`transform_preserves_halt_basic` and `transform_preserves_faulting_basic` are proved in `BasicCorrect.lean`:
rather than a separately-defined basic transform (`insBefore'`/`insEdge'`), `BasicCorrect` runs the *optimal*
`transform` against the `πᵤ`/`τᵤ`-widened bundle `mkBasic S`, so `match_step_assign`/`_ifz` are reused
directly. The coverage and fault-safety obligations are discharged here.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

variable {P : Program}

/-! ## Basic insert quantities (τ_u = allExprs inlined = optimal insert with `∩ τᵤ` dropped) -/

def insBefore' (S : LcmSpec P) (n : Node) : Assignments :=
  (Assignments.sdiff (latestNode P S.ηₚ S.τₚ n) (latestOut P S n)).filter S.keep

def insOut' (S : LcmSpec P) (n : Node) : Assignments :=
  latestOut P S n

/-- Basic coverage invariant — every *computation* not freshly placed at `n` is materialized in `M`. -/
def Cov_basic (S : LcmSpec P) (n : Node) (M : Assignments) : Prop :=
  Assignments.Subset
    (Assignments.sdiff (Assignments.sdiff ((ue P n).filter S.keep) (insBefore' S n)) (insOut' S n)) M

/-- Basic materialized-set update across `c → c'` (τ_u-free; uses `insOut'` for the exit, `latestEdge` for the
    edge — a *superset* of the optimal `Mstep_edge`, which is all coverage needs). -/
def Mstep_edge' (S : LcmSpec P) (c c' : Node) (M : Assignments) : Assignments :=
  Assignments.union
    (Assignments.union (Assignments.inter (Assignments.union M (insBefore' S c)) (pass P c)) (insOut' S c))
    (latestEdge P S.πₐ S.ηₐ S.ηₚ c c')

/-! ## Fault safety of the basic (incl. isolated) node inserts, `π_u`-free -/

theorem insBefore'_sub_anti (S : LcmSpec P) {n : Node}
    (hpa : Assignments.Subset (S.ηₚ n) (S.πₐ n)) :
    Assignments.Subset (insBefore' S n) (S.πₐ n) := by
  intro e he
  exact hpa e (latestNode_sub_postp S n e
    (Assignments.mem_sdiff.mp (Analysis.SetOps.mem_filter'.mp he).1).1)

/-! ## Insert containments (basic ⊇ optimal) -/

theorem insertBefore_sub_insBefore' (S : LcmSpec P) (n : Node) :
    Assignments.Subset (insertBefore P S n) (insBefore' S n) := by
  intro e he; unfold insertBefore at he; rw [Assignments.mem_inter] at he
  exact Analysis.SetOps.mem_filter'.mpr ⟨he.1, (mem_τᵤK.mp he.2).2⟩

theorem insertOut_sub_insOut' (S : LcmSpec P) (n : Node) :
    Assignments.Subset (insertOut P S n) (insOut' S n) := by
  intro e he; unfold insertOut at he; rw [Assignments.mem_inter] at he; exact he.1

theorem insertEdge_sub_latestEdge (S : LcmSpec P) (i j : Node) :
    Assignments.Subset (insertEdge P S i j) (latestEdge P S.πₐ S.ηₐ S.ηₚ i j) := by
  intro e he; unfold insertEdge at he; rw [Assignments.mem_inter] at he; exact he.1

theorem insertAfter_sub_insOut' (S : LcmSpec P) (i : Node) :
    Assignments.Subset (insertAfter P S i) (insOut' S i) := by
  intro e he
  unfold insertAfter at he; unfold insOut' latestOut
  cases hf : P.fetch i with
  | none => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty
  | some instr =>
    cases instr with
    | assign x ex next => simp only [hf] at he ⊢; rw [Assignments.mem_inter] at he; exact he.1
    | noop next => simp only [hf] at he ⊢; rw [Assignments.mem_inter] at he; exact he.1
    | ifz x z nz => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty
    | halt => simp only [hf] at he; exact absurd he Std.HashSet.not_mem_empty

/-! ## A transparent numbered computation is on no out-edge (`π_u`-free; πᵤ by `replace_covered_basic`) -/

theorem ue_transp_notLatestOut (S : LcmSpec P) {nd : Node} {x : Var} {e : Expr} {next : Node}
    (hf : P.fetch nd = some (.assign x e next)) (hnum : isNumbered e = true)
    (hnsr : exprReadsVar e x = false) :
    e ∉ latestOut P S nd := by
  have heall : e ∈ allExprs P := fetch_mem_allExprs hf hnum
  have hcomp : e ∈ ue P nd := by
    unfold ue; rw [hf]; simp only [hnum, if_true]; exact Assignments.mem_singleton.2 rfl
  have htransp : e ∈ pass P nd := by
    unfold pass; rw [Assignments.mem_filter']
    exact ⟨heall, by simp [transpB, hf, instrDefVar, hnsr]⟩
  have hde : e ∈ de P nd := Assignments.mem_inter.mpr ⟨hcomp, htransp⟩
  have hav : e ∈ availableOut P S.ηₐ nd := by
    unfold availableOut; rw [Assignments.mem_union]; exact Or.inl hde
  have hnle : e ∉ latestEdge P S.πₐ S.ηₐ S.ηₚ nd next := by
    intro hin
    unfold latestEdge at hin
    rw [Assignments.mem_sdiff] at hin
    rcases Assignments.mem_union.mp hin.1 with hear | hcarry
    · unfold earliest at hear
      rw [Assignments.mem_inter, Assignments.mem_inter] at hear
      have hnav : e ∉ availableOut P S.ηₐ nd := by
        have := hear.1.2; unfold compl at this; exact (Assignments.mem_sdiff.mp this).2
      exact hnav hav
    · exact (Assignments.mem_sdiff.mp hcarry).2 hcomp
  unfold latestOut; rw [hf]; exact hnle

/-- **Replace read-validity for the basic gate.** The basic transform replaces *every* numbered
    computation; the temp it reads is materialized before the control (`e0 ∈ M ∪ insBefore'`). A transparent
    numbered `e0` is on no out-edge (`ue_transp_notLatestOut`), so if it isn't placed at the node entry,
    `Cov_basic` puts it in `M`. `π_u`-free (no `S.πᵤ`, no `Extremal`). -/
theorem replace_covered_basic (S : LcmSpec P) {nd : Node} {x : Var} {e0 : Expr} {next : Node} {M : Assignments}
    (hf : P.fetch nd = some (.assign x e0 next)) (hnum : isNumbered e0 = true)
    (hkeep : S.keep e0 = true)
    (hnsr : exprReadsVar e0 x = false) (hcov : Cov_basic S nd M) :
    e0 ∈ M ∨ e0 ∈ insBefore' S nd := by
  have hcomp : e0 ∈ (ue P nd).filter S.keep := by
    refine Analysis.SetOps.mem_filter'.mpr ⟨?_, hkeep⟩
    unfold ue; rw [hf]; simp only [hnum, if_true]; exact Assignments.mem_singleton.2 rfl
  by_cases hib : e0 ∈ insBefore' S nd
  · exact Or.inr hib
  · exact Or.inl (hcov e0 (Assignments.mem_sdiff.mpr
      ⟨Assignments.mem_sdiff.mpr ⟨hcomp, hib⟩, ue_transp_notLatestOut S hf hnum hnsr⟩))

/-! ## The coverage crux: `Cov ⇒ Cov_basic`, and maintenance by reuse -/

/-- **`Cov_basic` follows from `Cov`.** A basic-covered computation `e` is not on the node's own latest
    frontier (else `e ∉ insOut' = latestOut` would put it in `insBefore'`), so `Used.check` demands it:
    `e ∈ ue ∖ latestNode ⊆ πᵤ`. The insert containments then place it in `demandSet`, and
    `demand_materialized` carries that into `ηₘ` — which is what the new `Cov` covers.

    Stated over `GateComplete`, so it runs under either `GateMode`: under `.demand` that hypothesis is
    definitional and this is the classical argument verbatim; under `.materialized` it is
    `gateComplete_materialized`, which supplies the extra containment from `ExtremalMat`. -/
theorem cov_implies_cov_basic (S : LcmSpec P) (hgc : GateComplete S) {n : Node} {M : Assignments}
    (hcov : Cov S n M) : Cov_basic S n M := by
  intro e he
  rw [Assignments.mem_sdiff, Assignments.mem_sdiff] at he
  obtain ⟨⟨hueK, hnib'⟩, hnio'⟩ := he
  have hkeep : S.keep e = true := (Analysis.SetOps.mem_filter'.mp hueK).2
  have hue : e ∈ ue P n := (Analysis.SetOps.mem_filter'.mp hueK).1
  have hnln : e ∉ latestNode P S.ηₚ S.τₚ n := fun hln =>
    hnib' (Analysis.SetOps.mem_filter'.mpr ⟨Assignments.mem_sdiff.mpr ⟨hln, hnio'⟩, hkeep⟩)
  have hdem : e ∈ demandSet S n := mem_demandSet.mpr
    ⟨⟨mem_πᵤK.mpr ⟨S.isUsed.check n e (Assignments.mem_sdiff.mpr ⟨hue, hnln⟩), hkeep⟩,
      fun hib => hnib' (insertBefore_sub_insBefore' S n e hib)⟩,
     fun hio => hnio' (insertOut_sub_insOut' S n e hio)⟩
  exact hcov e (hgc n e hdem)

/-- `Cov` is monotone in `M`. -/
theorem cov_mono (S : LcmSpec P) {n : Node} {M M' : Assignments}
    (h : Cov S n M) (hsub : Assignments.Subset M M') : Cov S n M' :=
  fun e he => hsub e (h e he)

/-- The optimal materialized update is contained in the basic one. -/
theorem mstep_edge_sub (S : LcmSpec P) (c c' : Node) (M : Assignments) :
    Assignments.Subset (Mstep_edge S c c' M) (Mstep_edge' S c c' M) := by
  intro e he
  unfold Mstep_edge Mstep Mstep_edge' at *
  rw [Assignments.mem_union] at he ⊢
  rcases he with hms | hedge
  · left
    rw [Assignments.mem_union] at hms ⊢
    rcases hms with hbody | hafter
    · left
      rw [Assignments.mem_inter, Assignments.mem_union] at hbody ⊢
      refine ⟨?_, hbody.2⟩
      rcases hbody.1 with hM | hib
      · exact Or.inl hM
      · exact Or.inr (insertBefore_sub_insBefore' S c e hib)
    · right; exact insertAfter_sub_insOut' S c e hafter
  · right; exact insertEdge_sub_latestEdge S c c' e hedge

/-- **Basic coverage maintenance.** Basic coverage is maintained across a step, by reusing `Cov_step_edge`.
    Keeps `Extremal S` as a scaffold; the basic transform output uses no `π_u`. -/
theorem Cov_basic_step (S : LcmSpec P) (hg : GateSound P S) (hgc : GateComplete S)
    {c c' : Config} {M : Assignments}
    (hstep : Step P c c') (hcov : Cov S c.node M) :
    Cov_basic S c'.node (Mstep_edge' S c.node c'.node M) :=
  cov_implies_cov_basic S hgc
    (cov_mono S (Cov_step_edge S hg hstep hcov) (mstep_edge_sub S c.node c'.node M))

end BaseLanguage.Analyses.LCM
