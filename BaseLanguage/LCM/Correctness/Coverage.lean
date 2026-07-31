-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness.Match

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## The coverage tool — least-`πᵤ` decomposition

The crux of LCM correctness: a demanded expression at `n` is either a genuine *local* use there
(`ue ∖ latestNode`) or demanded by a *successor* (hence `τᵤ`). Proved from **leastness** (`isUsed.2`):
if `e ∈ πᵤ n` were neither, then `πᵤ' := πᵤ ∖ {e at n}` would still satisfy `Used` — the only
non-trivial obligation is `predict` for a step `n → b`, where `e ∈ πᵤ b` would force `e ∈ τᵤ n`
(`isUsedOut.1.predict`), contradicting the assumption — so `isUsed.2` gives `πᵤ ⊆ πᵤ'`, i.e.
`e ∉ πᵤ n`, a contradiction. This is where correctness consumes `isUsed.2`. -/

theorem used_decomp {P : Program} (S : LcmSpec P) (hS : Extremal S) {n : Node} {e : Expr} (he : e ∈ S.πᵤ n) :
    e ∈ Assignments.sdiff (ue P n) (latestNode P S.ηₚ S.τₚ n) ∨ e ∈ S.τᵤ n := by
  rcases Classical.em (e ∈ S.τᵤ n) with h2 | h2
  · exact Or.inr h2
  rcases Classical.em (e ∈ Assignments.sdiff (ue P n) (latestNode P S.ηₚ S.τₚ n)) with h1 | h1
  · exact Or.inl h1
  exfalso
  -- the witness analysis: drop `e` from `used` at node `n` only
  let πᵤ' : Node → Assignments := fun m => if m = n then Assignments.sdiff (S.πᵤ m) (Assignments.singleton e) else S.πᵤ m
  have hud_n : πᵤ' n = Assignments.sdiff (S.πᵤ n) (Assignments.singleton e) := if_pos rfl
  have hud_ne : ∀ m, m ≠ n → πᵤ' m = S.πᵤ m := fun m h => if_neg h
  -- a realized successor `b` of `n` cannot demand `e` (else `e ∈ usedOut n`)
  have hsucc : ∀ {c c' : Config}, Step P c c' → c.node = n → e ∉ S.πᵤ c'.node := by
    intro c c' hstep hcn hmem
    exact h2 (hcn ▸ S.isUsedOut.predict c c' hstep e hmem)
  -- `e' ∈ used' m` ⇒ `e' ∈ used m`
  have hsub : ∀ m e', e' ∈ πᵤ' m → e' ∈ S.πᵤ m := by
    intro m e' he'
    by_cases hm : m = n
    · subst hm; rw [hud_n, Assignments.mem_sdiff] at he'; exact he'.1
    · rw [hud_ne m hm] at he'; exact he'
  have hvalid : Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ) πᵤ' := by
    refine ⟨?_, ?_, ?_⟩
    · -- predict : used'(c'.node) ⊆ used'(c.node) ∪ latestNode(c'.node) ∪ latestEdge(c,c')
      intro c c' hstep e' he'
      have he'πᵤ : e' ∈ S.πᵤ c'.node := hsub _ _ he'
      have hbase := S.isUsed.predict c c' hstep e' he'πᵤ
      rw [Assignments.mem_union, Assignments.mem_union] at hbase ⊢
      rcases hbase with hcu | hlat | hedge
      · refine Or.inl ?_
        by_cases ha : c.node = n
        · rw [show c.node = n from ha, hud_n, Assignments.mem_sdiff]
          refine ⟨ha ▸ hcu, ?_⟩
          intro hes; rw [Assignments.mem_singleton] at hes; subst hes
          exact hsucc hstep ha he'πᵤ
        · rw [hud_ne _ ha]; exact hcu
      · exact Or.inr (Or.inl hlat)
      · exact Or.inr (Or.inr hedge)
    · -- check : ue m ∖ latestNode m ⊆ used' m
      intro m e' he'
      have hbase : e' ∈ S.πᵤ m := S.isUsed.check m e' he'
      by_cases hm : m = n
      · subst hm; rw [hud_n, Assignments.mem_sdiff]
        refine ⟨hbase, ?_⟩
        intro hes; rw [Assignments.mem_singleton] at hes; subst hes; exact h1 he'
      · rw [hud_ne m hm]; exact hbase
    · -- bound
      intro m e' he'
      exact S.isUsed.within m e' (hsub m e' he')
  have hle : e ∈ πᵤ' n := hS.πᵤ πᵤ' hvalid n e he
  rw [hud_n, Assignments.mem_sdiff] at hle
  exact hle.2 (Assignments.mem_singleton.mpr rfl)

/-! ## Postponed-past expressions are not πᵤ — the `τₚ` blocker

The "postponed-past" set at `m`: still postponable beyond `m` (`∈ τₚ`), not locally πᵤ (`∉ ue`), not
placed here (`∉ latestNode`). -/
def postponedPast (P : Program) (S : LcmSpec P) (m : Node) : Assignments :=
  Assignments.sdiff (Assignments.sdiff (S.τₚ m) (ue P m)) (latestNode P S.ηₚ S.τₚ m)

theorem mem_postponedPast {P : Program} {S : LcmSpec P} {m : Node} {e : Expr} :
    e ∈ postponedPast P S m ↔
      e ∈ S.τₚ m ∧ e ∉ ue P m ∧ e ∉ latestNode P S.ηₚ S.τₚ m := by
  unfold postponedPast; rw [Assignments.mem_sdiff, Assignments.mem_sdiff, and_assoc]

/-- **`tauP` blocker.** An expression still *postponable past* `n` (`e ∈ tauP n`), not locally used and
    not placed at `n`, is **not** `πᵤ` at `n` — its temp is materialized strictly downstream, so the
    value entering `n` is not yet demanded. Proved by leastness (like `used_decomp`): `w := πᵤ ∖
    postponedPast` is a valid `Used` family; its `predict` turns `e ∈ postponedPast(c)` into `e ∈
    postponedPast(c')` (via `isTauP.1.predict` then the `latestNode = ηₚ ∩ (ue ∪ ¬τₚ)` algebra),
    contradicting `w`-membership at `c'`. Consumes `isUsed.2` + `isTauP.1`. (The naive `πᵤ ∩ ηₚ = ∅`
    is FALSE — `latestNode ⊆ ηₚ`, and a πᵤ `latestNode` point is in both; this `τₚ`/`∉ue`/`∉latestNode`
    refinement is the true statement.) -/
theorem tauP_not_used {P : Program} (S : LcmSpec P) (hS : Extremal S) {n : Node} {e : Expr}
    (htau : e ∈ S.τₚ n) (hue : e ∉ ue P n)
    (hlat : e ∉ latestNode P S.ηₚ S.τₚ n) : e ∉ S.πᵤ n := by
  have mk_latestNode : ∀ {m e'}, e' ∈ S.ηₚ m →
      e' ∈ Assignments.union (ue P m) (compl P (S.τₚ m)) → e' ∈ latestNode P S.ηₚ S.τₚ m := by
    intro m e' hp hu; unfold latestNode; rw [Assignments.mem_inter]; exact ⟨hp, hu⟩
  have hvalid : Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ)
      (fun m => Assignments.sdiff (S.πᵤ m) (postponedPast P S m)) := by
    refine ⟨?_, ?_, ?_⟩
    · -- predict (3-way: used ∪ latestNode ∪ latestEdge)
      intro c c' hstep e' he'
      obtain ⟨he'u, he'Z⟩ := Assignments.mem_sdiff.mp he'
      rw [Assignments.mem_union]
      by_cases hlc' : e' ∈ latestNode P S.ηₚ S.τₚ c'.node
      · exact Or.inr (Assignments.mem_union.mpr (Or.inl hlc'))
      · have hpred := S.isUsed.predict c c' hstep e' he'u
        rw [Assignments.mem_union, Assignments.mem_union] at hpred
        rcases hpred with hcu | hlat' | hedge
        · refine Or.inl (Assignments.mem_sdiff.mpr ⟨hcu, fun hz => ?_⟩)
          -- e'∈postponedPast(c) ⇒ e'∈postponedPast(c'), contradicting he'Z
          have htauc : e' ∈ S.τₚ c.node := (mem_postponedPast.mp hz).1
          have hpostp : e' ∈ S.ηₚ c'.node := S.isTauP.predict c c' hstep e' htauc
          have he'all : e' ∈ allExprs P := S.isUsed.within c.node e' hcu
          have hnue' : e' ∉ ue P c'.node := fun ha =>
            hlc' (mk_latestNode hpostp (Assignments.mem_union.mpr (Or.inl ha)))
          have htau' : e' ∈ S.τₚ c'.node := by
            rcases Classical.em (e' ∈ S.τₚ c'.node) with h | h
            · exact h
            · exact absurd (mk_latestNode hpostp (Assignments.mem_union.mpr (Or.inr (Assignments.mem_sdiff.mpr ⟨he'all, h⟩)))) hlc'
          exact he'Z (mem_postponedPast.mpr ⟨htau', hnue', hlc'⟩)
        · exact absurd hlat' hlc'
        · exact Or.inr (Assignments.mem_union.mpr (Or.inr hedge))
    · -- check: `ue ∖ latestNode ⊆ used ∖ postponedPast` (∈ue ⇒ ∉postponedPast)
      intro m e' he'
      rw [Assignments.mem_sdiff]
      exact ⟨S.isUsed.check m e' he', fun hz => (mem_postponedPast.mp hz).2.1 (Assignments.mem_sdiff.mp he').1⟩
    · -- bound
      intro m e' he'
      exact S.isUsed.within m e' (Assignments.mem_sdiff.mp he').1
  intro hused
  exact (Assignments.mem_sdiff.mp (hS.πᵤ _ hvalid n e hused)).2 (mem_postponedPast.mpr ⟨htau, hue, hlat⟩)

/-! ## The killed-case keystone

`πᵤ ⊆ πₐ` is false (available-fork; see the keystone note below), but `Cov_step`'s killed case
(`e ∉ pass c`) only needs it where `e ∉ ηₐ(c')` — and the relativized **`πᵤ ∖ ηₐ ⊆ πₐ`** does hold. Proved
by leastness with witness `πᵤ ∩ (πₐ ∪ ηₐ)`; the helpers are `tauP_not_used` (postponed-past),
`isAvail.update`, and the `earliest`/`availableOut` algebra. With `earliest` reading `¬πₐ(c)` directly, the
killed-case arm just splits on `e ∈ πₐ(c)`: if not, `e ∈ earliest(c,c')` (contradiction) unless `e ∈
availableOut(c)`, whose only non-`de` part lands in `ηₐ(c)` (`de ⊆ ue ⊆ πₐ`). -/

/-- `e ∈ postp ∧ e ∉ latestNode ⇒ e ∉ ue ∧ e ∈ tauP` (the `latestNode = postp ∩ (ue ∪ ¬tauP)` algebra). -/
theorem postp_not_latestNode {P : Program} (S : LcmSpec P) {n : Node} {e : Expr} (hp : e ∈ S.ηₚ n)
    (hall : e ∈ allExprs P) (hnl : e ∉ latestNode P S.ηₚ S.τₚ n) :
    e ∉ ue P n ∧ e ∈ S.τₚ n := by
  have hmk : e ∈ Assignments.union (ue P n) (compl P (S.τₚ n)) → False := by
    intro h; exact hnl (by unfold latestNode; rw [Assignments.mem_inter]; exact ⟨hp, h⟩)
  refine ⟨fun hu => hmk (Assignments.mem_union.mpr (Or.inl hu)), ?_⟩
  rcases Classical.em (e ∈ S.τₚ n) with h | h
  · exact h
  · exact absurd (Assignments.mem_union.mpr (Or.inr (Assignments.mem_sdiff.mpr ⟨hall, h⟩))) hmk

/-- **THE KEYSTONE (relativized): `used ∖ avail ⊆ anti`.** By leastness, witness
    `g = πᵤ ∩ (πₐ ∪ ηₐ)`. Covers `Cov_step`'s killed case (killed `e ⇒ e ∉ ηₐ(c') ⇒ e ∈ πₐ(c')`).
    The global `πᵤ ⊆ πₐ` is *false* (available-fork) but is not needed. -/
theorem used_diff_avail_sub_anti {P : Program} (S : LcmSpec P) (hS : Extremal S) (n : Node) :
    Assignments.Subset (Assignments.sdiff (S.πᵤ n) (S.ηₐ n)) (S.πₐ n) := by
  have hg : Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ)
      (fun m => Assignments.inter (S.πᵤ m) (Assignments.union (S.πₐ m) (S.ηₐ m))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep e he
      rw [Assignments.mem_inter, Assignments.mem_union] at he
      obtain ⟨heu, heav⟩ := he
      rw [Assignments.mem_union]
      by_cases hlc' : e ∈ latestNode P S.ηₚ S.τₚ c'.node
      · exact Or.inr (Assignments.mem_union.mpr (Or.inl hlc'))
      by_cases hei : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node
      · exact Or.inr (Assignments.mem_union.mpr (Or.inr hei))
      have heuc : e ∈ S.πᵤ c.node := by
        have hpred := S.isUsed.predict c c' hstep e heu
        rw [Assignments.mem_union, Assignments.mem_union] at hpred
        rcases hpred with h | h | h
        · exact h
        · exact absurd h hlc'
        · exact absurd h hei
      have heall : e ∈ allExprs P := S.isUsed.within c.node e heuc
      refine Or.inl (Assignments.mem_inter.mpr ⟨heuc, ?_⟩)
      rw [Assignments.mem_union]
      have hearl_imp : e ∈ earliest P S.πₐ S.ηₐ c.node c'.node → False := by
        intro hE
        have hpostp : e ∈ S.ηₚ c'.node := by
          rcases Classical.em (e ∈ S.ηₚ c'.node) with h | h
          · exact h
          · exact absurd (Assignments.mem_sdiff.mpr ⟨Assignments.mem_union.mpr (Or.inl hE), h⟩) hei
        obtain ⟨hnue', htau'⟩ := postp_not_latestNode S hpostp (S.isUsed.within c'.node e heu) hlc'
        exact tauP_not_used S hS htau' hnue' hlc' heu
      rcases heav with hanti' | havl'
      · -- `e ∈ πₐ(c')`: either `e ∈ πₐ(c)` (done), or `e ∉ πₐ(c)` ⇒ `e ∈ earliest(c,c')` unless
        -- `e ∈ availableOut(c)`, whose only non-`de` part is `ηₐ(c) ∩ pass(c) ⊆ ηₐ(c)` (`de ⊆ ue ⊆ πₐ`).
        rcases Classical.em (e ∈ S.πₐ c.node) with hpi | hnpi
        · exact Or.inl hpi
        · by_cases hav_c : e ∈ availableOut P S.ηₐ c.node
          · unfold availableOut at hav_c
            rw [Assignments.mem_union] at hav_c
            rcases hav_c with hde | hai
            · exact absurd (ue_sub_anti S hS c.node e (Assignments.mem_inter.mp hde).1) hnpi
            · exact Or.inr (Assignments.mem_inter.mp hai).1
          · exact absurd (by
              unfold earliest
              rw [Assignments.mem_inter, Assignments.mem_inter]
              refine ⟨⟨hanti', Assignments.mem_sdiff.mpr ⟨heall, hav_c⟩⟩, ?_⟩
              by_cases hce : c.node = P.entry
              · rw [if_pos hce]; exact heall
              · rw [if_neg hce]; exact Assignments.mem_sdiff.mpr ⟨heall, hnpi⟩) hearl_imp
      · have hup := S.isAvail.update c c' hstep e havl'
        rw [Assignments.mem_union] at hup
        rcases hup with hde | hai
        · exact Or.inl (ue_sub_anti S hS c.node e (Assignments.mem_inter.mp hde).1)
        · exact Or.inr (Assignments.mem_inter.mp hai).1
    · intro m e he
      rw [Assignments.mem_inter]
      exact ⟨S.isUsed.check m e he, Assignments.mem_union.mpr (Or.inl (ue_sub_anti S hS m e (Assignments.mem_sdiff.mp he).1))⟩
    · intro m e he
      exact S.isUsed.within m e (Assignments.mem_inter.mp he).1
  intro e he
  obtain ⟨heu, henav⟩ := Assignments.mem_sdiff.mp he
  have hge := hS.πᵤ _ hg n e heu
  rw [Assignments.mem_inter, Assignments.mem_union] at hge
  rcases hge.2 with h | h
  · exact h
  · exact absurd h henav

/-- **Killed-case coverage core (`Cov_step`):** a killed (`e ∉ pass c`), demanded (`e ∈ used c'`) and
    not-placed-at-`c'` (`e ∉ latestNode c'`) expression lands in `insertAfter(c)` — so the exit chain materializes
    its temp on the killed path. The keystone `used_diff_avail_sub_anti` supplies `e ∈ πₐ(c')`
    (killed ⇒ `e ∉ ηₐ(c')`); `e ∉ ηₚ(c')` is derived (`e ∈ ηₚ ∧ ∉ latestNode ⇒ postponed-past ⇒ ∉ πᵤ`,
    via `postp_not_latestNode`+`tauP_not_used`); the rest is the `earliest`/`availableOut` algebra +
    `isUsedOut.predict`. Non-`assign` steps are vacuous (transparent, contradicting `e ∉ pass c`). -/
theorem killed_in_insertAfter {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c c' : Config}
    (hstep : Step P c c') {e : Expr}
    (hused : e ∈ S.πᵤ c'.node) (hkill : e ∉ pass P c.node)
    (hnlat : e ∉ latestNode P S.ηₚ S.τₚ c'.node) : e ∈ insertAfter P S c.node := by
  have heall : e ∈ allExprs P := S.isUsed.within c'.node e hused
  have hpostp : e ∉ S.ηₚ c'.node := by
    intro hp
    obtain ⟨hnue', htau'⟩ := postp_not_latestNode S hp heall hnlat
    exact tauP_not_used S hS htau' hnue' hnlat hused
  have hnav_out : e ∉ availableOut P S.ηₐ c.node := by
    unfold availableOut; rw [Assignments.mem_union]
    rintro (h | h)
    · exact hkill (Assignments.mem_inter.mp h).2
    · exact hkill (Assignments.mem_inter.mp h).2
  have hnav' : e ∉ S.ηₐ c'.node := by
    intro h
    have hu := S.isAvail.update c c' hstep e h
    rw [Assignments.mem_union] at hu
    rcases hu with hde | hai
    · exact hkill (Assignments.mem_inter.mp hde).2
    · exact hkill (Assignments.mem_inter.mp hai).2
  have hanti' : e ∈ S.πₐ c'.node :=
    used_diff_avail_sub_anti S hS c'.node e (Assignments.mem_sdiff.mpr ⟨hused, hnav'⟩)
  have husedout : e ∈ S.τᵤ c.node := S.isUsedOut.predict c c' hstep e hused
  have hearl : e ∈ earliest P S.πₐ S.ηₐ c.node c'.node := by
    unfold earliest; rw [Assignments.mem_inter, Assignments.mem_inter]
    refine ⟨⟨hanti', Assignments.mem_sdiff.mpr ⟨heall, hnav_out⟩⟩, ?_⟩
    by_cases hce : c.node = P.entry
    · rw [if_pos hce]; exact heall
    · rw [if_neg hce]; exact Assignments.mem_sdiff.mpr ⟨heall, notAnti_of_notPass S wn hkill⟩
  cases hstep with
  | @assign nd σ x e0 next v hf hv =>
      unfold insertAfter
      rw [hf, Assignments.mem_inter]
      refine ⟨?_, husedout⟩
      unfold latestEdge; rw [Assignments.mem_sdiff]
      exact ⟨Assignments.mem_union.mpr (Or.inl hearl), hpostp⟩
  | ifzT hf _ => exact absurd (Assignments.mem_filter'.mpr ⟨heall, by simp [transpB, hf, instrDefVar]⟩) hkill
  | ifzF hf _ => exact absurd (Assignments.mem_filter'.mpr ⟨heall, by simp [transpB, hf, instrDefVar]⟩) hkill
  | noop hf   => exact absurd (Assignments.mem_filter'.mpr ⟨heall, by simp [transpB, hf, instrDefVar]⟩) hkill

/-! ## The isolation interplay — a `πᵤ`+`latestNode` point is non-isolated (the `Cov_step` lever)

A demanded expression that is *placeable* at `n` (`∈ πᵤ n ∩ latestNode n`) is **not isolated**
(`∈ τᵤ n`) — so it is in `insertBefore n`. This is the lever that lets `Cov_step`'s transparent case
*backflow* `πᵤ`: an `e ∈ πᵤ(c') ∖ insertBefore(c')` that is still `∈ latestNode(c')` is impossible, so
`e ∉ latestNode(c')` and `πᵤ.predict` carries it back. Proved by leastness, witness
`πᵤ ∖ (latestNode ∖ τᵤ)`; the `predict` bad case (`e ∈ latestNode(c) ∖ τᵤ(c)` yet `e ∈ πᵤ(c)`) is
killed by `isUsedOut.predict` (the realized step `c → c'` gives `e ∈ πᵤ(c') ⊆ τᵤ(c)`). -/
theorem used_inter_latestNode_sub_usedOut {P : Program} (S : LcmSpec P) (hS : Extremal S) (n : Node) :
    Assignments.Subset (Assignments.inter (S.πᵤ n) (latestNode P S.ηₚ S.τₚ n)) (S.τᵤ n) := by
  have hvalid : Used P (latestNode P S.ηₚ S.τₚ) (latestEdge P S.πₐ S.ηₐ S.ηₚ)
      (fun m => Assignments.sdiff (S.πᵤ m) (Assignments.sdiff (latestNode P S.ηₚ S.τₚ m) (S.τᵤ m))) := by
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep e he
      obtain ⟨heu, _⟩ := Assignments.mem_sdiff.mp he
      have hpred := S.isUsed.predict c c' hstep e heu
      rw [Assignments.mem_union, Assignments.mem_union] at hpred
      rw [Assignments.mem_union, Assignments.mem_union]
      rcases hpred with hcu | hlat | hedge
      · refine Or.inl (Assignments.mem_sdiff.mpr ⟨hcu, ?_⟩)
        rw [Assignments.mem_sdiff]; rintro ⟨_, hnoutc⟩
        exact hnoutc (S.isUsedOut.predict c c' hstep e heu)
      · exact Or.inr (Or.inl hlat)
      · exact Or.inr (Or.inr hedge)
    · intro m e he
      rw [Assignments.mem_sdiff]
      refine ⟨S.isUsed.check m e he, ?_⟩
      rw [Assignments.mem_sdiff]; rintro ⟨hl, _⟩; exact (Assignments.mem_sdiff.mp he).2 hl
    · intro m e he
      exact S.isUsed.within m e (Assignments.mem_sdiff.mp he).1
  intro e he
  rw [Assignments.mem_inter] at he
  have hle := Assignments.mem_sdiff.mp (hS.πᵤ _ hvalid n e he.1)
  rcases Classical.em (e ∈ S.τᵤ n) with h | h
  · exact h
  · exact absurd (Assignments.mem_sdiff.mpr ⟨he.2, h⟩) hle.2

/-- A demanded exit/edge point (`∈ latestOut ∩ usedOut`) is in `insertOut` — definitional. -/
theorem latestOut_usedOut_sub_insertOut {P : Program} {S : LcmSpec P} {n : Node} {e : Expr}
    (hlo : e ∈ latestOut P S n) (huo : e ∈ S.τᵤ n) : e ∈ insertOut P S n :=
  Assignments.mem_inter.mpr ⟨hlo, huo⟩

/-- **Isolation corollary (the `Cov_step` lever):** a demanded `e ∉ insertBefore(n) ∧ ∉ insertOut(n)`
    is not `latestNode(n)` — via the partition `latestNode ⊆ latestIn ∪ latestOut` and `πᵤ ∩ latestNode ⊆ τᵤ`.
    `insertOut = latestOut ∩ τᵤ` unifies the node-exit (`assign`/`noop`) and edge (`ifz`) placement. -/
theorem used_notInsertAt_notLatest {P : Program} (S : LcmSpec P) (hS : Extremal S) {n : Node} {e : Expr}
    (hu : e ∈ S.πᵤ n) (hni : e ∉ insertBefore P S n) (hnio : e ∉ insertOut P S n) :
    e ∉ latestNode P S.ηₚ S.τₚ n := by
  intro hl
  have hout : e ∈ S.τᵤ n := used_inter_latestNode_sub_usedOut S hS n e (Assignments.mem_inter.mpr ⟨hu, hl⟩)
  by_cases hlo : e ∈ latestOut P S n
  · exact hnio (latestOut_usedOut_sub_insertOut hlo hout)
  · refine hni ?_
    unfold insertBefore; rw [Assignments.mem_inter]
    exact ⟨Assignments.mem_sdiff.mpr ⟨hl, hlo⟩, hout⟩

/-! ## `latestEdge ⊆ insertEdge` — the transparent `Cov_step` case

A demanded exit/edge insert (`e ∈ latestEdge(c,c') ∩ τᵤ(c)`) lands in `insertEdge(c,c')`, for any realized
step. For a `1-successor` source (`assign`/`noop`) `insertEdge(c,next) = insertAfter c`; for an `ifz` it is
the taken branch's edge chain. -/

theorem step_succ_mem {P : Program} {c c' : Config} (h : Step P c c') :
    c'.node ∈ succList P c.node := by
  cases h with
  | @assign nd σ x e next v hf hv => rw [succList_eq hf]; simp [Cmd.succs]
  | ifzT hf _ => rw [succList_eq hf]; simp [Cmd.succs]
  | ifzF hf _ => rw [succList_eq hf]; simp [Cmd.succs]
  | noop hf => rw [succList_eq hf]; simp [Cmd.succs]

theorem earliest_sub_anti {P : Program} (S : LcmSpec P) (i j : Node) :
    Assignments.Subset (earliest P S.πₐ S.ηₐ i j) (S.πₐ j) := by
  intro e he; unfold earliest at he; rw [Assignments.mem_inter, Assignments.mem_inter] at he; exact he.1.1

/-- For a single-predecessor `cj` (only realized pred-node is `ci`), `earliest(ci,cj) ⊆ postp(cj)`. By
    `isPostp.2`, witness `ηₚ ∪ {earliest(ci,cj) at cj}`. -/
theorem earliest_sub_postp {P : Program} (S : LcmSpec P) (hS : Extremal S) {ci cj : Node}
    (hsp : ∀ a a', Step P a a' → a'.node = cj → a.node = ci) (hne : cj ≠ P.entry) :
    Assignments.Subset (earliest P S.πₐ S.ηₐ ci cj) (S.ηₚ cj) := by
  have hg : Postponable P S.πₐ S.ηₐ
      (fun m => if m = cj then Assignments.union (S.ηₚ m) (earliest P S.πₐ S.ηₐ ci cj)
                else S.ηₚ m) := by
    refine ⟨?_, ?_, ?_⟩
    · intro a a' hst e he
      have hpost_part : ∀ {e'}, e' ∈ S.ηₚ a'.node →
          e' ∈ Assignments.union (earliest P S.πₐ S.ηₐ a.node a'.node)
                (Assignments.sdiff (if a.node = cj then
                    Assignments.union (S.ηₚ a.node) (earliest P S.πₐ S.ηₐ ci cj)
                  else S.ηₚ a.node) (ue P a.node)) := by
        intro e' he'
        have hup := S.isPostp.update a a' hst e' he'
        rw [Assignments.mem_union] at hup ⊢
        rcases hup with hl | hr
        · exact Or.inl hl
        · refine Or.inr ?_
          rw [Assignments.mem_sdiff] at hr ⊢
          refine ⟨?_, hr.2⟩
          by_cases ha : a.node = cj
          · rw [if_pos ha]; exact Assignments.mem_union.mpr (Or.inl hr.1)
          · rw [if_neg ha]; exact hr.1
      by_cases ha' : a'.node = cj
      · rw [if_pos ha'] at he
        rw [Assignments.mem_union] at he
        rcases he with hp | hEe
        · exact hpost_part hp
        · rw [Assignments.mem_union]; refine Or.inl ?_
          rw [hsp a a' hst ha', ha']; exact hEe
      · rw [if_neg ha'] at he; exact hpost_part he
    · show Assignments.Subset (if P.entry = cj then _ else S.ηₚ P.entry) (entrySeed P)
      rw [if_neg (fun h => hne h.symm)]; exact S.isPostp.seed
    · intro m e he
      by_cases hm : m = cj
      · rw [if_pos hm] at he
        rw [Assignments.mem_union] at he
        rcases he with hp | hEe
        · exact S.isPostp.within m e hp
        · exact S.isAnti.within cj e (earliest_sub_anti S ci cj e hEe)
      · rw [if_neg hm] at he; exact S.isPostp.within m e he
  intro e he
  refine hS.ηₚ _ hg cj e ?_
  show e ∈ (if cj = cj then Assignments.union (S.ηₚ cj) (earliest P S.πₐ S.ηₐ ci cj) else S.ηₚ cj)
  rw [if_pos rfl]; exact Assignments.mem_union.mpr (Or.inr he)

/-- **Edge realization (definitional).** Realizing `latestEdge` at the edge `i → j` (gated by `usedOut`) is
    membership in `insertEdge i j` — no `hstep` needed. The `ifz` edge insert is realized on the branch edge
    chain, so it is simply `insertEdge`; no critical-edge splitting. -/
theorem edgeIns_sub_insertEdge {P : Program} (S : LcmSpec P) {i j : Node} {e : Expr}
    (hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ i j) (husedout : e ∈ S.τᵤ i) :
    e ∈ insertEdge P S i j := Assignments.mem_inter.mpr ⟨hedge, husedout⟩

/-- `insertAfter = insertEdge(i,next)` at a `1-successor` source (both `= latestEdge(i,next) ∩ usedOut i`). -/
theorem insertAfter_eq_insertEdge {P : Program} (S : LcmSpec P) {i next : Node}
    (hf : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next)) :
    insertAfter P S i = insertEdge P S i next := by
  rcases hf with h | ⟨x, e, h⟩ <;> simp only [insertAfter, insertEdge, h]

/-- `insertAfter = insertOut` at a `1-successor` source (`insertOut = latestOut ∩ usedOut`, and there
    `latestOut = latestEdge(i,next)`). -/
theorem insertAfter_eq_insertOut {P : Program} (S : LcmSpec P) {i next : Node}
    (hf : P.fetch i = some (.noop next) ∨ ∃ x e, P.fetch i = some (.assign x e next)) :
    insertAfter P S i = insertOut P S i := by
  rcases hf with h | ⟨x, e, h⟩ <;> simp only [insertAfter, insertOut, latestOut, h]

/-- **Exit-insert down-safety (1-extend):** an exit-inserted `e ∈ latestEdge(c,c')` is anticipated at `c'` —
    the `earliest` part by `earliest_sub_anti`, the **transparent carry** `(ηₚ c ∖ ue c) ∖ ηₚ c'` via
    the threaded `ηₚ c ⊆ πₐ c` (`hpa`) + `isAnti.predict` (`πₐ c ∖ ue ⊆ πₐ c'`). This is the
    `match_step` exit-chain no-fault for the widened frontier. -/
theorem edgeIns_sub_anti {P : Program} (S : LcmSpec P) {c c' : Config} (hstep : Step P c c')
    (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node)) {e : Expr}
    (he : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node) : e ∈ S.πₐ c'.node := by
  unfold latestEdge at he; rw [Assignments.mem_sdiff, Assignments.mem_union] at he
  rcases he.1 with hearl | hcarry
  · exact earliest_sub_anti S c.node c'.node e hearl
  · rw [Assignments.mem_sdiff] at hcarry
    exact S.isAnti.predict c c' hstep e (Assignments.mem_sdiff.mpr ⟨hpa e hcarry.1, hcarry.2⟩)

/-! ## The set-level `Cov_step` — coverage maintenance

`Cov n M` = every demanded temp not freshly placed at `n` (`πᵤ ∖ insertBefore ∖ insertAfter`) is in the
in-flight set `M`. `Mstep` = the materialized set after `c`'s block (entry inserts added, killed across the
control, exit inserts added). `Cov_step` maintains it across a step, assembling the pieces:
`used_notInsertAt_notLatest` (⇒ `e ∉ latestNode c'`, the isolation lever), `killed_in_insertAfter` (killed case),
`πᵤ`'s `predict` + `Cov c` (transparent-`πᵤ(c)` case), and `edgeIns_sub_insertEdge` (the
transparent-`latestEdge` case). No `μ`-ghost — pure set bookkeeping. -/

/-- **Edge selection.** A demanded (`used c'`), unplaced-at-`c'` (`∉ latestNode c'`) expression that is on *some*
    outgoing insertion of `c` (`∈ latestOut c`) is on the **taken** edge `c → c'` (`∈ insertEdge(c,c')`). The
    `earliest`/`carry` factors of `latestEdge` are head-independent, and `e ∈ πᵤ c'` forces `e ∈ πₐ c'`
    (not-available: `ηₐ c' ⊆ availableOut c`, contradicting `earliest`'s `¬availableOut`; not-postponable:
    `ηₚ c' ∧ ¬latestNode c' ⇒ ¬πᵤ c'`). So the insert on the *sibling* edge would equally be on the taken
    edge — this is why `Cov` may subtract *all* of `latestOut` (the whole `insertOut`) yet stay sound. -/
theorem latestOut_used_succ_sub_insertEdge {P : Program} (S : LcmSpec P) (hS : Extremal S)
    {c c' : Config} (hstep : Step P c c') {e : Expr}
    (hu : e ∈ S.πᵤ c'.node) (hnlat : e ∉ latestNode P S.ηₚ S.τₚ c'.node)
    (hlo : e ∈ latestOut P S c.node) (huo : e ∈ S.τᵤ c.node) :
    e ∈ insertEdge P S c.node c'.node := by
  have heall : e ∈ allExprs P := S.isUsed.within c'.node e hu
  have hnpc' : e ∉ S.ηₚ c'.node := by
    intro hp
    obtain ⟨hnue', htau'⟩ := postp_not_latestNode S hp heall hnlat
    exact tauP_not_used S hS htau' hnue' hnlat hu
  -- rebuild `latestEdge(c, other) ⇒ latestEdge(c, c')`: the `earliest`/`carry` witness carries over.
  have transfer : ∀ j, e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node j →
      e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c.node c'.node := by
    intro j hj
    unfold latestEdge at hj ⊢
    rw [Assignments.mem_sdiff, Assignments.mem_union] at hj ⊢
    refine ⟨?_, hnpc'⟩
    rcases hj.1 with hearl | hcarry
    · left
      unfold earliest at hearl ⊢
      rw [Assignments.mem_inter, Assignments.mem_inter] at hearl ⊢
      obtain ⟨⟨_, hnavail⟩, hentry⟩ := hearl
      refine ⟨⟨?_, hnavail⟩, hentry⟩
      refine used_diff_avail_sub_anti S hS c'.node e (Assignments.mem_sdiff.mpr ⟨hu, ?_⟩)
      intro havc'
      have hin : e ∈ availableOut P S.ηₐ c.node := S.isAvail.update c c' hstep e havc'
      exact (Assignments.mem_sdiff.mp hnavail).2 hin
    · right; exact hcarry
  refine edgeIns_sub_insertEdge S ?_ huo
  cases hstep with
  | @assign nd σ x e0 next v hf hv => simp only [latestOut, hf] at hlo; exact hlo
  | @noop nd σ next hf => simp only [latestOut, hf] at hlo; exact hlo
  | @ifzT nd σ x z nz hf hz =>
      simp only [latestOut, hf] at hlo
      rcases Assignments.mem_union.mp hlo with h | h
      · exact h
      · exact transfer nz h
  | @ifzF nd σ x z nz hf hz =>
      simp only [latestOut, hf] at hlo
      rcases Assignments.mem_union.mp hlo with h | h
      · exact transfer z h
      · exact h

/-- Coverage invariant: demanded-and-not-placed temps are in `M`. `insertOut = latestOut ∩ usedOut` unifies
    node-exit (`assign`/`noop`) and edge (`ifz`) placement leaving `n`. -/
def Cov {P : Program} (S : LcmSpec P) (n : Node) (M : Assignments) : Prop :=
  Assignments.Subset (Assignments.sdiff (Assignments.sdiff (S.πᵤ n) (insertBefore P S n)) (insertOut P S n)) M

/-- The materialized set after node `c`'s block, before the outgoing edge (`insertAfter` = the exit chain for
    `assign`/`noop`, `∅` for `ifz`). -/
def Mstep {P : Program} (S : LcmSpec P) (c : Node) (M : Assignments) : Assignments :=
  Assignments.union (Assignments.inter (Assignments.union M (insertBefore P S c)) (pass P c)) (insertAfter P S c)

/-- The materialized set after taking the **edge** `c → c'`: `Mstep` plus the edge insert `insertEdge(c,c')`.
    For a `1-successor` source `insertEdge(c,next) = insertAfter c ⊆ Mstep`, so this coincides with `Mstep`;
    for an `ifz` it adds the taken branch's edge chain. -/
def Mstep_edge {P : Program} (S : LcmSpec P) (c c' : Node) (M : Assignments) : Assignments :=
  Assignments.union (Mstep S c M) (insertEdge P S c c')

/-- **`Cov_step_edge` — set-level coverage maintenance across one step, edge-indexed.**
    The transparent-`latestEdge` case is the definitional `edgeIns_sub_insertEdge` (an `ifz` edge insert lands
    on its branch edge chain, tracked by `Mstep_edge`); the transparent-`πᵤ` case routes a would-be
    `insertOut` member to the taken edge via `latestOut_used_succ_sub_insertEdge`. -/
theorem Cov_step_edge {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) {c c' : Config} {M : Assignments}
    (hstep : Step P c c') (hcov : Cov S c.node M) : Cov S c'.node (Mstep_edge S c.node c'.node M) := by
  intro e he
  rw [Assignments.mem_sdiff, Assignments.mem_sdiff] at he
  obtain ⟨⟨hu, hnia⟩, hnio⟩ := he
  have hnlat : e ∉ latestNode P S.ηₚ S.τₚ c'.node := used_notInsertAt_notLatest S hS hu hnia hnio
  rw [Mstep_edge, Assignments.mem_union]
  by_cases htr : e ∈ pass P c.node
  · have hpred := S.isUsed.predict c c' hstep e hu
    rw [Assignments.mem_union, Assignments.mem_union] at hpred
    rcases hpred with hcu | hlat | hedge
    · by_cases hiac : e ∈ insertBefore P S c.node
      · exact Or.inl (Assignments.mem_union.mpr
          (Or.inl (Assignments.mem_inter.mpr ⟨Assignments.mem_union.mpr (Or.inr hiac), htr⟩)))
      by_cases hedge2 : e ∈ insertEdge P S c.node c'.node
      · exact Or.inr hedge2
      · have hnio_c : e ∉ insertOut P S c.node := fun hio =>
          hedge2 (latestOut_used_succ_sub_insertEdge S hS hstep hu hnlat
            (Assignments.mem_inter.mp hio).1 (Assignments.mem_inter.mp hio).2)
        have heM : e ∈ M := hcov e (Assignments.mem_sdiff.mpr ⟨Assignments.mem_sdiff.mpr ⟨hcu, hiac⟩, hnio_c⟩)
        exact Or.inl (Assignments.mem_union.mpr
          (Or.inl (Assignments.mem_inter.mpr ⟨Assignments.mem_union.mpr (Or.inl heM), htr⟩)))
    · exact absurd hlat hnlat
    · exact Or.inr (edgeIns_sub_insertEdge S hedge (S.isUsedOut.predict c c' hstep e hu))
  · exact Or.inl (Assignments.mem_union.mpr (Or.inr (killed_in_insertAfter S hS wn hstep hu htr hnlat)))

/-! ## Why `πᵤ ⊆ πₐ` is false — the entry+edge placement

The global keystone `πᵤ n ⊆ πₐ n` is **false**, on a chain of killers feeding a join:

```
0: ifz q 1 3
1: a := 5      → 2     -- kills a+b
2: a := 6      → 5     -- kills a+b   (1-succ killer → join)
3: t := a+b    → 4     -- computes a+b (available downstream)
4: noop        → 5
5: x := a+b    → 6     -- join (indeg 2); uses a+b
6: halt
```

`Used.predict` is `πᵤ(c') ⊆ πᵤ(c) ∪ latestNode(c')` — no transparency guard — so usedness backflows *through*
the killers `2` and `1` (blocked only by `latestNode`, and `a+b ∉ latestNode` there since `a+b ∉ ηₚ`). Hence
`a+b ∈ πᵤ(1)` and `a+b ∈ πᵤ(2)`, while `a+b ∉ πₐ(1)`, `a+b ∉ πₐ(2)` (each kills `a+b`, so
`Anticipated.check : πₐ ⊆ ue ∪ pass` excludes it). The refinement `πᵤ ∖ insertBefore ∖ insertAfter ⊆ πₐ` is
also false at node `1`.

`latestNode` is KRS `Latest(n)` and `πᵤ` is KRS `¬ISOLATED(n)` (single-valued, blocks at `latestNode`), both
faithful to the original KRS paper (Knoop–Rüthing–Steffen, *Lazy Code Motion*, PLDI'92). LCM realizes
placement at node entries **and** on the taken out-edge (KRS footnote-6's entry+exit alternative): edge
inserts land directly on the branch edge (`insertEdge` / `ifz` edge chains), a two-valued
`Latestin`/`Latestout` split with no critical-edge splitting. So coverage rests on the relativized
`used_diff_avail_sub_anti` (`πᵤ ∖ ηₐ ⊆ πₐ`, above), never a global `πᵤ ⊆ πₐ`. Correctness (halt + fault) and
eval-count optimality are proved and axiom-clean. -/

/-! ## Boundary at `halt` — `match_final_obs`

At a source `halt`, `πₐ(halt) = ∅` (seed), so `latestNode(halt) = ∅` (threaded `ηₚ ⊆ πₐ`), so
`insertBefore(halt) = ∅` — no inserts. The block is just the floated `halt`, reached with the store unchanged,
and the observables (original ⇒ non-fresh) agree by `Match` clause 2. *Simpler* than PDCE (which had an
exit-frontier materialization). -/

theorem match_final_obs {P : Program} (S : LcmSpec P) {c d : Config} {M : Assignments}
    (hm : Match P S c d M) (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node))
    (hfin : Final P c) (hobs : ∀ v ∈ P.obs, varIsOrig v = true) :
    ∃ d', Steps (transform P S) d d' ∧ Final (transform P S) d'
        ∧ ∀ v ∈ P.obs, d'.store v = c.store v := by
  obtain ⟨hlabel, hagree, _, _⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  have hfin' : P.fetch c.node = some .halt := hfin
  have hi : c.node < P.size := fetch_lt hfin'
  -- there are no inserts at `halt`: every candidate is anticipated there, and `anti(halt) = ∅`
  have hno_mem : ∀ e ∈ (insertBefore P S c.node).toList, False := by
    intro e he
    rw [mem_insertBefore] at he
    have hin : e ∈ S.πₐ c.node := hpa e (latestNode_sub_postp S c.node e he.1.1)
    have hempty := S.isAnti.seed c hfin e hin
    simp only [haltSeed, Assignments.empty] at hempty; exact Std.HashSet.not_mem_empty hempty
  have hdist : ∀ e ∈ (insertBefore P S c.node).toList, ∀ e' ∈ (insertBefore P S c.node).toList,
      e ≠ e' → tempFor P e ≠ tempFor P e' := fun e he _ _ _ _ => absurd he (hno_mem e)
  have hrec : ∀ e ∈ (insertBefore P S c.node).toList, eval dσ e ≠ none :=
    fun e he => absurd he (fun h => hno_mem e h)
  have hfresh : ∀ e ∈ (insertBefore P S c.node).toList, ∀ e' ∈ (insertBefore P S c.node).toList,
      exprReadsVar e (tempFor P e') = false := fun e he _ _ => absurd he (hno_mem e)
  subst hlabel
  obtain ⟨τ1, hs1, hoff1, _⟩ := insBlock_exec S hi hdist hrec hfresh
  refine ⟨⟨blockOff P S c.node + (insertBefore P S c.node).toList.length, τ1⟩, hs1, ?_, ?_⟩
  · -- the control slot fetches the floated `halt`
    show (transform P S).fetch _ = some .halt
    rw [ctrl_slot_fetch S hi]; simp only [ctrlCmd, hfin']
  · intro v hv
    have hvnf : NonFresh P v := nonFresh_of_orig (hobs v hv)
    show τ1 v = c.store v
    rw [hoff1 v (fun e _ => hvnf e)]; exact hagree v hvnf


end BaseLanguage.Analyses.LCM
