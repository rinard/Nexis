-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness
import BaseLanguage.LCM.NoRecompute

/-!
# `NoReinsert` — maintenance of the no-reinsert invariant (`e ∈ M ⇒ e ∉ ηₚ(node)`)

The eval-count optimality core needs the operational "no double-materialize" invariant — along the run, the
transform never re-materializes an expression it already holds. The lever is the invariant

  `Inv(c, M) := ∀ e ∈ M, e ∉ S.ηₚ c.node`

(then `e ∈ M ⇒ e ∉ insertBefore c.node` is immediate, since `insertBefore ⊆ latestNode ⊆ ηₚ`; the
`insertAfter` half is `insertAfter_postp_disjoint`). The question is whether `Inv` is maintained across one
step `c → c'` under `Mstep`.

* **Single-successor steps (`noop`/`assign`): `Inv` is maintained** (`Inv_step_single`). The three `Mstep`
  contributions all close from the spec laws:
  - `insertAfter c` → `insertAfter_postp_disjoint` (`e ∉ ηₚ(next)` directly);
  - carried `e ∈ M` (transparent) → IH `e ∉ ηₚ(c)` kills the `ηₚ(c) ∖ ue` branch of `Postponable.update`,
    and `e ∉ earliest(c,next)` via the **single-succ transfer** `pass(c) ∩ πₐ(next) ⊆ πₐ(c)`
    (`pass_antiSucc_sub_anti`) + `earliest_excludes_transferable`;
  - freshly-inserted `e ∈ insertBefore c` (transparent) → `e ∈ latestNode ⇒ e ∈ ue ∨ e ∉ τₚ`; the `ηₚ(c) ∖ ue`
    branch needs `e ∉ ue ⇒ e ∉ τₚ(c)`, refuted by the **single-succ transfer** `ηₚ(next) ⊆ τₚ(c)`
    (`postp_succ_sub_tauP`) against the contradiction-hypothesis `e ∈ ηₚ(next)`.
  The two single-succ transfer lemmas are greatest-`Transfer` witnesses (mirror `earliest_sub_postp`),
  projections of `πₐ`/`τₚ` extremality.
* **Multi-successor (branch) steps.** At a branch a *carried* `e ∈ M` can be `∈ earliest(c,c')` (held
  this-path but `∉ availableOut(c)` *must*, and `∉ πₐ(c)` because dead on the sibling branch) — the
  must-vs-this-path gap. `Inv_step_multi` mechanizes that the branch case closes iff the this-path obligation
  `hthis` holds, and `hthis` is false in general at a join-before-branch. So the per-node no-reinsert
  invariant is a single-successor tool; the branch's shared, forced recompute is carried by the direct
  `srcContrib` comparison (in `EvalCountOpt`), where the placement's equally-forced recompute matches it.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics

/-! ## The join-before-branch case

**The simple invariant `e ∈ M ⇒ e ∉ ηₚ(node)` is false at a join-before-branch** — the segment boundaries
there are *anticipation gaps*, not only kills. Concrete CFG:

```
0: ifz q 1 2 ; 1: t:=a+b → 3 ; 2: noop → 3 ; 3: ifz r 4 5 ; 4: x:=a+b → 6 ; 5: y:=7 → 6 ; 6: halt
```
On `0→1→3→4`, `a+b` is held (`∈ M`) from node 1, yet `a+b ∈ earliest(3,4) ⊆ ηₚ(4)`: it is `∉ ηₐ(3)`
(the `2→3` join-pred lacks it) and `∉ πₐ(3)` (dead on `3→5`), so `earliest(3,4)` fires and the transform
re-materializes at node 4 while `a+b ∈ M`. So the lever `e∈M ⇒ e∉ηₚ` cannot hold at multi-succ joins. The
count is still optimal: `a+b ∉ πₐ(3)` is an *anticipation gap*, so node 1 and node 4 sit in **different
fresh-need intervals**, and *every* down-safe placement is equally forced to compute at node 4 (it cannot
place on `2→3`, where `a+b ∉ πₐ(3)` — not down-safe). The double is shared, so no double *relative to a safe
placement*. The interval count comparison (segments split at `e ∉ πₐ`) carries the multi-succ case; the
per-node no-reinsert invariant is a single-successor tool.

The two lemmas below are the multi-succ structural facts the interval argument consumes: **a transparent carry
is never placed at a branch entry** (`insertBefore_multisucc_in_ue` — only genuine uses are placed there), because
the greatest `ηₚ` absorbs the whole carry into `τₚ` (`carry_in_tauP_multisucc`).
So a branch contributes to `insertBefore` only via a real `ue` use — it never starts a spurious interval. -/

/-- **Greatest-`tauP` carry absorption at a multi-successor node (edge-placement version).** If a carry `e`
    (`e ∉ ue(c)`) is postponable to *every* successor (`∀ j ∈ succ(c), e ∈ ηₚ j`), then `e ∈ τₚ(c)` — the
    carry is postponed to all successors. Greatest-`Transfer` witness `τₚ ∪ {e}@c`. The per-successor
    postponability is derived (in `insertBefore_multisucc_in_ue`) from `e ∉ latestOut`. -/
theorem carry_in_tauP_multisucc {P : Program} (S : LcmSpec P) (hS : Extremal S) {c : Node} {e : Expr}
    (hue : e ∉ ue P c) (hall : e ∈ allExprs P) (hsucc : ∀ j ∈ succList P c, e ∈ S.ηₚ j) :
    e ∈ S.τₚ c := by
  refine hS.τₚ
    (fun m => Assignments.union (S.τₚ m) (if m = c then Assignments.singleton e else Assignments.empty)) ?_ c e
    (Assignments.mem_union.mpr (Or.inr (by rw [if_pos rfl]; exact Assignments.mem_singleton.mpr rfl)))
  refine ⟨?_, ?_⟩
  · intro a a' hstep e' he'
    rcases Assignments.mem_union.mp he' with hp | hadd
    · exact S.isTauP.predict a a' hstep e' hp
    · by_cases hac : a.node = c
      · rw [if_pos hac, Assignments.mem_singleton] at hadd; subst hadd
        exact hsucc a'.node (hac ▸ step_succ_mem hstep)
      · rw [if_neg hac] at hadd; exact absurd hadd Std.HashSet.not_mem_empty
  · intro m e' he'
    rcases Assignments.mem_union.mp he' with hp | hadd
    · exact S.isTauP.within m e' hp
    · by_cases hmc : m = c
      · rw [if_pos hmc, Assignments.mem_singleton] at hadd; subst hadd; exact hall
      · rw [if_neg hmc] at hadd; exact absurd hadd Std.HashSet.not_mem_empty

/-- **A transparent carry is never entry-placed at a branch.** At a multi-successor node, every `insertBefore`
    expression is a genuine use (`∈ ue`): a carry (`∉ ue`) is on the frontier `latestNode = ηₚ ∩ (ue ∪ ¬τₚ)`
    only via `¬τₚ`, and — under edge placement — is subtracted by `latestOut` (`insertBefore = (latestNode ∖
    latestOut) ∩ τᵤ`). `e ∉ latestOut` means `e ∈ ηₚ` at *every* successor edge, so `carry_in_tauP_multisucc`
    gives `e ∈ τₚ`, contradicting `e ∈ ¬τₚ`. So a branch contributes to `insertBefore` only at real uses. -/
theorem insertBefore_multisucc_in_ue {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P)
    {c : Node} {e : Expr}
    (hmulti : 2 ≤ (succList P c).length) (he : e ∈ (insertBefore P S c).toList) : e ∈ ue P c := by
  have hlat : e ∈ latestNode P S.ηₚ S.τₚ c := insertBefore_sub_latestNode he
  have hnlo : e ∉ latestOut P S c :=
    (Assignments.mem_sdiff.mp (Assignments.mem_inter.mp (Assignments.mem_toList.1 he)).1).2
  unfold latestNode at hlat
  rw [Assignments.mem_inter, Assignments.mem_union] at hlat
  rcases hlat.2 with hue | hctp
  · exact hue
  · unfold compl at hctp
    have hntp := (Assignments.mem_sdiff.mp hctp).2
    have hall : e ∈ allExprs P := S.isPostp.within c e hlat.1
    by_cases hue : e ∈ ue P c
    · exact hue
    · obtain ⟨x, z, nz, hf⟩ : ∃ x z nz, P.fetch c = some (.ifz x z nz) := by
        obtain ⟨j0, hj0⟩ : ∃ j0, j0 ∈ succList P c := by
          rcases hsl : succList P c with _ | ⟨j0, rest⟩
          · rw [hsl] at hmulti; simp at hmulti
          · exact ⟨j0, by simp⟩
        obtain ⟨instr, hfetch, _⟩ := mem_succList hj0
        rw [succList_eq hfetch] at hmulti
        cases instr with
        | ifz x z nz => exact ⟨x, z, nz, hfetch⟩
        | assign _ _ _ => simp [Cmd.succs] at hmulti
        | noop _ => simp [Cmd.succs] at hmulti
        | halt => simp [Cmd.succs] at hmulti
      have hsucc : ∀ j ∈ succList P c, e ∈ S.ηₚ j := by
        intro j hj
        by_cases hpj : e ∈ S.ηₚ j
        · exact hpj
        · exfalso; apply hnlo
          have hedge : e ∈ latestEdge P S.πₐ S.ηₐ S.ηₚ c j := by
            unfold latestEdge; rw [Assignments.mem_sdiff, Assignments.mem_union]
            exact ⟨Or.inr (Assignments.mem_sdiff.mpr ⟨hlat.1, hue⟩), hpj⟩
          simp only [latestOut, hf]
          rw [succList_eq hf] at hj
          simp only [Cmd.succs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hj
          rcases hj with rfl | rfl
          · exact Assignments.mem_union.mpr (Or.inl hedge)
          · exact Assignments.mem_union.mpr (Or.inr hedge)
      exact absurd (carry_in_tauP_multisucc S hS hue hall hsucc) hntp

/-- **Single-successor transfer (postponability).** If every step from `c` lands at `next`, then
    `ηₚ(next) ⊆ τₚ(c)`. Same greatest-`Transfer` witness, on `ηₚ`/`τₚ`. -/
theorem postp_succ_sub_tauP {P : Program} (S : LcmSpec P) (hS : Extremal S) {c next : Node}
    (hss : ∀ a a' : Config, Step P a a' → a.node = c → a'.node = next) :
    Assignments.Subset (S.ηₚ next) (S.τₚ c) := by
  have hg : Transfer Assignments.Subset P S.ηₚ (fun m => if m = c then S.ηₚ next else S.τₚ m) := by
    refine ⟨?_, ?_⟩
    · intro a a' hst e he
      by_cases ha : a.node = c
      · rw [if_pos ha] at he; rw [hss a a' hst ha]; exact he
      · rw [if_neg ha] at he; exact S.isTauP.predict a a' hst e he
    · intro m e he
      by_cases hm : m = c
      · rw [if_pos hm] at he; exact S.isPostp.within next e he
      · rw [if_neg hm] at he; exact S.isTauP.within m e he
  intro e he
  have h := hS.τₚ _ hg c e
  rw [if_pos rfl] at h
  exact h he

/-- A `noop`/`assign` node has a unique successor `next` (deterministic control). -/
theorem single_succ_of_fetch {P : Program} {nd next : Node}
    (hf : P.fetch nd = some (.noop next) ∨ ∃ x e, P.fetch nd = some (.assign x e next)) :
    ∀ a a' : Config, Step P a a' → a.node = nd → a'.node = next := by
  intro a a' hst ha
  cases hst with
  | @noop nd2 σ next2 hf2 =>
      have hnd : nd2 = nd := ha; subst hnd
      rcases hf with h | ⟨x, e, h⟩
      · rw [h] at hf2; simp only [Option.some.injEq, Cmd.noop.injEq] at hf2; show next2 = next; exact hf2.symm
      · rw [h] at hf2; simp at hf2
  | @assign nd2 σ x e0 next2 v hf2 hv =>
      have hnd : nd2 = nd := ha; subst hnd
      rcases hf with h | ⟨x', e', h⟩
      · rw [h] at hf2; simp at hf2
      · rw [h] at hf2; simp only [Option.some.injEq, Cmd.assign.injEq] at hf2
        show next2 = next; exact hf2.2.2.symm
  | @ifzT nd2 σ x z nz hf2 hz =>
      have hnd : nd2 = nd := ha; subst hnd
      rcases hf with h | ⟨x', e', h⟩ <;> (rw [h] at hf2; simp at hf2)
  | @ifzF nd2 σ x z nz hf2 hz =>
      have hnd : nd2 = nd := ha; subst hnd
      rcases hf with h | ⟨x', e', h⟩ <;> (rw [h] at hf2; simp at hf2)

/-- **Single-successor anticipation-in** (`ANTin ⊇ TRANSP ∩ ANTout`):
    at a `noop`/`assign` node `c` with unique successor `next`, a transparent expression anticipated out
    (`e ∈ pass(c) ∩ πₐ(next)`) is anticipated in (`e ∈ πₐ(c)`). Proved by greatest-`πₐ` augmentation — the
    added expression sits at the non-`Final` `c`, and its `predict` obligation is exactly `e ∈ πₐ(next)`
    (single successor, so `πₐ(next)` *is* the meet). `earliest` blocks a held `e` via `e ∈ πₐ(c)`
    directly (`earliest_excludes_transferable`). -/
theorem pass_antiSucc_sub_anti {P : Program} (S : LcmSpec P) (hS : Extremal S) {c next : Node}
    (hf : P.fetch c = some (.noop next) ∨ ∃ x ex, P.fetch c = some (.assign x ex next))
    {e : Expr} (htr : e ∈ pass P c) (hanti : e ∈ S.πₐ next) : e ∈ S.πₐ c := by
  have hall : e ∈ allExprs P := pass_sub P c e htr
  have hss : ∀ a a' : Config, Step P a a' → a.node = c → a'.node = next := single_succ_of_fetch hf
  have hcne : ∀ {m : Config}, Final P m → m.node ≠ c := by
    intro m hfin hmc
    have hmh : P.fetch c = some Cmd.halt := by rw [← hmc]; exact hfin
    rcases hf with h | ⟨x, ex, h⟩ <;> rw [h] at hmh <;> exact absurd hmh (by simp)
  apply hS.πₐ (fun m => Assignments.union (S.πₐ m) (if m = c then Assignments.singleton e else ∅))
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro a a' hst e' he'
      rw [Assignments.mem_sdiff, Assignments.mem_union] at he'
      obtain ⟨he'g, he'nu⟩ := he'
      rcases he'g with h | h
      · exact Assignments.mem_union.mpr (Or.inl (S.isAnti.predict a a' hst e' (Assignments.mem_sdiff.mpr ⟨h, he'nu⟩)))
      · by_cases hm : a.node = c
        · rw [if_pos hm] at h; rw [Assignments.mem_singleton] at h; subst h
          rw [hss a a' hst hm]; exact Assignments.mem_union.mpr (Or.inl hanti)
        · rw [if_neg hm] at h; exact absurd h Std.HashSet.not_mem_empty
    · intro m e' he'
      rw [Assignments.mem_union] at he'
      rcases he' with h | h
      · exact S.isAnti.check m e' h
      · by_cases hm : m = c
        · rw [if_pos hm] at h; rw [Assignments.mem_singleton] at h; subst h
          exact Assignments.mem_union.mpr (Or.inr (hm ▸ htr))
        · rw [if_neg hm] at h; exact absurd h Std.HashSet.not_mem_empty
    · intro m hfin e' he'
      rw [Assignments.mem_union] at he'
      rcases he' with h | h
      · exact S.isAnti.seed m hfin e' h
      · rw [if_neg (hcne hfin)] at h; exact absurd h Std.HashSet.not_mem_empty
    · intro m e' he'
      rw [Assignments.mem_union] at he'
      rcases he' with h | h
      · exact S.isAnti.within m e' h
      · by_cases hm : m = c
        · rw [if_pos hm] at h; rw [Assignments.mem_singleton] at h; subst h; exact hall
        · rw [if_neg hm] at h; exact absurd h Std.HashSet.not_mem_empty
  · exact Assignments.mem_union.mpr (Or.inr (by rw [if_pos rfl]; exact Assignments.mem_singleton.mpr rfl))

/-- **Single-successor maintenance of the no-reinsert invariant.** For a `noop`/`assign`
    step `c → c'` (so `c'.node = next`), if every `e ∈ M` is `∉ ηₚ(c.node)` then every `e ∈ Mstep S c.node M`
    is `∉ ηₚ(c'.node)`. All three `Mstep` contributions close from the spec laws (see the file header). -/
theorem Inv_step_single {P : Program} (S : LcmSpec P) (hS : Extremal S) {c c' : Config} {next : Node} {M : Assignments}
    (hstep : Step P c c') (hnext : c'.node = next)
    (hf : P.fetch c.node = some (.noop next) ∨ ∃ x e, P.fetch c.node = some (.assign x e next))
    (hne : c.node ≠ P.entry)
    (hInv : ∀ e, e ∈ M → e ∉ S.ηₚ c.node) :
    ∀ e, e ∈ Mstep S c.node M → e ∉ S.ηₚ c'.node := by
  have hss : ∀ a a' : Config, Step P a a' → a.node = c.node → a'.node = next := single_succ_of_fetch hf
  intro e he hpost
  rw [hnext] at hpost
  rw [Mstep, Assignments.mem_union] at he
  rcases he with hMI | hexit
  · -- carried / freshly-inserted, transparent
    rw [Assignments.mem_inter, Assignments.mem_union] at hMI
    obtain ⟨hmi, htr⟩ := hMI
    -- e ∉ earliest(c, next)
    have hnearl : e ∉ earliest P S.πₐ S.ηₐ c.node next := by
      intro hearl
      have hanti : e ∈ S.πₐ next := earliest_sub_anti S c.node next e hearl
      exact earliest_excludes_transferable hne (pass_antiSucc_sub_anti S hS hf htr hanti) hearl
    -- so from Postponable.update, e ∈ postp(c) ∖ ue(c)
    have hup := S.isPostp.update c c' hstep e (hnext ▸ hpost)
    rw [hnext, Assignments.mem_union] at hup
    have hdiff : e ∈ Assignments.sdiff (S.ηₚ c.node) (ue P c.node) := hup.resolve_left hnearl
    rw [Assignments.mem_sdiff] at hdiff
    obtain ⟨hpc, hnue⟩ := hdiff
    rcases hmi with hM | hia
    · exact hInv e hM hpc
    · -- e ∈ insertBefore c : e ∈ latestNode ⇒ (e ∉ ue ⇒ e ∉ tauP c) ; but postp(next) ⊆ tauP c
      have hlat : e ∈ latestNode P S.ηₚ S.τₚ c.node := insertBefore_sub_latestNode (Assignments.mem_toList.2 hia)
      unfold latestNode at hlat
      rw [Assignments.mem_inter, Assignments.mem_union] at hlat
      have hntauP : e ∉ S.τₚ c.node := by
        rcases hlat.2 with hue | hctp
        · exact absurd hue hnue
        · unfold compl at hctp; exact (Assignments.mem_sdiff.mp hctp).2
      exact hntauP (postp_succ_sub_tauP S hS hss e hpost)
  · -- exit insert : e ∉ postp(next) directly
    have hfi : (∃ x ex, P.fetch c.node = some (.assign x ex next)) ∨ P.fetch c.node = some (.noop next) := by
      rcases hf with h | ⟨x, e0, h⟩
      · exact Or.inr h
      · exact Or.inl ⟨x, e0, h⟩
    exact insertAfter_postp_disjoint S hexit hfi hpost

/-! ## The within-segment "no second insert" engine (spec-level, no `M`)

Per-πₐ-segment `≤1` does not go through any `M`-invariant — at a forced recompute the held `e` genuinely
satisfies `e ∈ M ∩ ηₚ ∩ πₐ` at the *new* segment (the join-before-branch). But the **within-segment** fact —
*once placed at a node and kept transparent, `e` is discharged from `ηₚ` at the successor, hence not
re-placed* — is spec-derivable, and it is the engine inside `Inv_step_single`.
`insertBefore_transp_notPostp_succ` extracts it; `insertBefore_no_reinsert_single` is the immediate corollary (no
second `insertBefore` at the next node). Inducting this along a single-successor πₐ-run gives per-segment `≤1`
with no operational `M` tracking. The multi-successor in-segment step is covered by
`insertBefore_multisucc_in_ue` (a branch places only genuine uses, never a carry, so it cannot start a second
materialization of a carried `e`). -/

/-- **Within-segment discharge (the per-segment `≤1` engine).** At a single-successor (`noop`/`assign`) step,
    an entry-placed transparent `e` is dropped from `ηₚ` at the successor — so the lazy analysis will not
    place it again downstream while it stays in the segment. Extracted from `Inv_step_single`'s fresh case. -/
theorem insertBefore_transp_notPostp_succ {P : Program} (S : LcmSpec P) (hS : Extremal S) {c c' : Config} {next : Node} {e : Expr}
    (hstep : Step P c c') (hnext : c'.node = next)
    (hf : P.fetch c.node = some (.noop next) ∨ ∃ x ex, P.fetch c.node = some (.assign x ex next))
    (hne : c.node ≠ P.entry)
    (he : e ∈ (insertBefore P S c.node).toList) (hpi : e ∈ S.πₐ c.node) : e ∉ S.ηₚ c'.node := by
  have hss : ∀ a a' : Config, Step P a a' → a.node = c.node → a'.node = next := single_succ_of_fetch hf
  intro hpost
  rw [hnext] at hpost
  have hnearl : e ∉ earliest P S.πₐ S.ηₐ c.node next := earliest_excludes_transferable hne hpi
  have hup := S.isPostp.update c c' hstep e (hnext ▸ hpost)
  rw [hnext, Assignments.mem_union] at hup
  have hdiff := hup.resolve_left hnearl
  rw [Assignments.mem_sdiff] at hdiff
  obtain ⟨_, hnue⟩ := hdiff
  have hlat : e ∈ latestNode P S.ηₚ S.τₚ c.node := insertBefore_sub_latestNode he
  unfold latestNode at hlat
  rw [Assignments.mem_inter, Assignments.mem_union] at hlat
  have hntauP : e ∉ S.τₚ c.node := by
    rcases hlat.2 with hue | hctp
    · exact absurd hue hnue
    · unfold compl at hctp; exact (Assignments.mem_sdiff.mp hctp).2
  exact hntauP (postp_succ_sub_tauP S hS hss e hpost)

/-- **No immediate second insert within a single-successor anti-run.** Corollary: an entry-placed transparent
    `e` is not re-placed at the next node (`insertBefore ⊆ latestNode ⊆ ηₚ`, and it just left `ηₚ`). The local
    step of the per-segment `≤1` induction. -/
theorem insertBefore_no_reinsert_single {P : Program} (S : LcmSpec P) (hS : Extremal S) {c c' : Config} {next : Node} {e : Expr}
    (hstep : Step P c c') (hnext : c'.node = next)
    (hf : P.fetch c.node = some (.noop next) ∨ ∃ x ex, P.fetch c.node = some (.assign x ex next))
    (hne : c.node ≠ P.entry)
    (he : e ∈ (insertBefore P S c.node).toList) (hpi : e ∈ S.πₐ c.node) :
    e ∉ (insertBefore P S c'.node).toList := fun h =>
  insertBefore_transp_notPostp_succ S hS hstep hnext hf hne he hpi
    (latestNode_sub_postp S c'.node e (insertBefore_sub_latestNode h))

/-! ## The multi-successor maintenance reduces to one this-path obligation

The single-successor proof (`Inv_step_single`) closes the ηₚ/earliest cases from the spec laws alone. At a
**branch** the carried `e∈M` case cannot: `pass_antiSucc_sub_anti` does not apply (`πₐ(c) = ⋂` over both
successors), so `e∉earliest` is not derivable. `Inv_step_multi` below mechanizes exactly how far the spec laws get: the ifz
maintenance closes **iff** the single obligation

  `hthis : ∀ e ∈ M ∪ insertBefore(c), e ∈ pass(c) → e ∉ earliest(c.node, c'.node)`

holds — the **this-path availability** fact (a held/transparent `e` is not "newly earliest" on the taken
edge). `hthis` is **false in general** — the join-before-branch above realizes `e∈M ∧ e∈earliest(c,c')` (held
this-path, but `∉availableOut(c)` *must*). So the branch's shared, forced recompute is carried by the direct
`srcContrib_S ≤ srcContrib_Place` comparison (where Place's equally-forced recompute matches it), not by a
per-node "don't re-materialize" invariant. The `insertBefore(c)` half of `hthis` is dischargeable
(`insertBefore_multisucc_in_ue` ⇒ `e∈ue` ⇒ not the carried case), so the obligation is only about the carried
`M` — the gap is exactly the this-path-vs-must availability, the irreducible run-dependent content. -/

/-- **The multi-successor (ifz) maintenance, reduced to the this-path obligation `hthis`.** Mechanizes that the
    branch case closes given `hthis` (and only it): the `ηₚ ∖ ue` branch of `Postponable.update` is killed by
    `hInv` (carried) / `insertBefore_multisucc_in_ue` (fresh), leaving exactly `e ∉ earliest(c,c')` — which is
    `hthis`. Since `hthis` is the (generally false) this-path availability fact, this lemma is the precise
    statement of where the no-reinsert route stops. -/
theorem Inv_step_multi {P : Program} (S : LcmSpec P) (hS : Extremal S) (wn : WellNormalized P) {c c' : Config} {M : Assignments}
    (hstep : Step P c c') (hmulti : 2 ≤ (succList P c.node).length)
    (hInv : ∀ e, e ∈ M → e ∉ S.ηₚ c.node)
    (hthis : ∀ e, (e ∈ M ∨ e ∈ insertBefore P S c.node) → e ∈ pass P c.node →
      e ∉ earliest P S.πₐ S.ηₐ c.node c'.node) :
    ∀ e, e ∈ Mstep S c.node M → e ∉ S.ηₚ c'.node := by
  have hfetch : ∃ x z nz, P.fetch c.node = some (.ifz x z nz) := by
    cases hf : P.fetch c.node with
    | none => simp [succList, hf] at hmulti
    | some instr =>
        cases instr with
        | assign x e n => simp [succList, hf, Cmd.succs] at hmulti
        | noop n => simp [succList, hf, Cmd.succs] at hmulti
        | ifz x z nz => exact ⟨x, z, nz, rfl⟩
        | halt => simp [succList, hf, Cmd.succs] at hmulti
  have hexempty : insertAfter P S c.node = Assignments.empty := by
    obtain ⟨x, z, nz, hf⟩ := hfetch; unfold insertAfter; rw [hf]
  intro e he hpost
  rw [Mstep, hexempty] at he
  rcases Assignments.mem_union.mp he with hin | hempty
  · rw [Assignments.mem_inter, Assignments.mem_union] at hin
    obtain ⟨hmi, htr⟩ := hin
    have hnearl : e ∉ earliest P S.πₐ S.ηₐ c.node c'.node := hthis e hmi htr
    have hup := S.isPostp.update c c' hstep e hpost
    rw [Assignments.mem_union] at hup
    have hdiff : e ∈ Assignments.sdiff (S.ηₚ c.node) (ue P c.node) := hup.resolve_left hnearl
    rw [Assignments.mem_sdiff] at hdiff
    obtain ⟨hpc, hnue⟩ := hdiff
    rcases hmi with hM | hia
    · exact hInv e hM hpc
    · exact hnue (insertBefore_multisucc_in_ue S hS wn hmulti (Assignments.mem_toList.2 hia))
  · exact absurd hempty Std.HashSet.not_mem_empty

end BaseLanguage.Analyses.LCM
