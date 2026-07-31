-- Copyright (c) 2026 Martin Rinard
import analyses.lcm.LcmAdapter
import BaseLanguage.LCM.Correctness  -- for `ue_mem_allExprs` (used in `gs_not_greatest`'s validity witness)

/-!
# `LCM.GhostFindings` — the two flat/staged order-theoretic findings (standalone; bridges to nothing)

The declarative flat-tuple ghost layer (`Ghost.Ghosts`/operators/`Valid`/`Le`/`FlatAnalysis`
and the staged `Analysis`) exists **only** to host the two paper findings about the *flat product order*
`⊑` vs the *staged* order — it is not on the pipeline path (the structural `LcmSpec`/`Extremal` in
`LcmDefs` is). There are no `Ghost.Analysis ↔ LcmSpec` bridges: with the DSL, `LcmSpec`/`PdceSpec` *is* the
analysis by construction, so "realizable"/"the flat greatest exists" are definitional, not theorems.

Two findings live here (both cited in `figures.tex` / `PAPER_FIGURES.md`):
* `BridgeFailFast.gs_not_greatest` (`thm:no-greatest`) — the flat product order `⊑` has **no top**: with a
  genuinely-available redundancy, no valid `G` dominates all others (`ηₐ` enters `earliest`
  antitonically, so a smaller `ηₐ` admits a strictly larger valid `ηₚ`). This is inherently about
  the flat tuple order and cannot be restated over the staged structural `LcmSpec`.
* `Ghost.staged_unique` (`thm:staged-unique`) — well-posedness: the *staged* (DAG-lexicographic) spec pins
  **at most one** solution up to set-equality. Pure `Ghost` vocabulary, no semantics.

In the default build (imported by `BaseLanguage.lean`), no `sorry` — the two keystone findings are
machine-checked. Standalone build: `lake build BaseLanguage.LCM.GhostFindings`.
-/

namespace BaseLanguage.LCM.Ghost
open Tac Normalize Semantics Std
open BaseLanguage.Analyses.LCM hiding earliest latestNode latestEdge
set_option linter.unusedVariables false

/-- `G = (πₐ, ηₐ, ηₚ, πᵤ, τₚ, τᵤ)`, all `Node → Assignments`. -/
structure Ghosts where
  πₐ : Node → Assignments
  ηₐ : Node → Assignments
  ηₚ : Node → Assignments
  πᵤ : Node → Assignments
  τₚ : Node → Assignments
  τᵤ : Node → Assignments

/-! ## Placement quantities — `My`'s KRS quantities with the ghost tuple `G` threaded in.
    (`availableOut` needs no adapter: `BaseLanguage.Analyses.LCM.earliest` consumes it internally.) -/

def earliest (P : Program) (G : Ghosts) (n n' : Node) : Assignments :=
  BaseLanguage.Analyses.LCM.earliest P G.πₐ G.ηₐ n n'

def latestNode (P : Program) (G : Ghosts) (n : Node) : Assignments :=
  BaseLanguage.Analyses.LCM.latestNode P G.ηₚ G.τₚ n

def latestEdge (P : Program) (G : Ghosts) (n n' : Node) : Assignments :=
  BaseLanguage.Analyses.LCM.latestEdge P G.πₐ G.ηₐ G.ηₚ n n'

/-! ## Operators — conjunction of the per-ghost inclusions. -/

def predict (P : Program) (G : Ghosts) (n n' : Node) : Prop :=
  (Assignments.sdiff (G.πₐ n) (ue P n)).Subset (G.πₐ n') ∧
  (G.πᵤ n').Subset ((G.πᵤ n).union ((latestNode P G n').union (latestEdge P G n n')))

def check (P : Program) (G : Ghosts) (n : Node) : Prop :=
  (G.πₐ n).Subset ((ue P n).union (pass P n)) ∧
  (Assignments.sdiff (ue P n) (latestNode P G n)).Subset (G.πᵤ n)

def update (P : Program) (G : Ghosts) (n n' : Node) : Prop :=
  (G.ηₐ n').Subset ((de P n).union ((G.ηₐ n).inter (pass P n))) ∧
  (G.ηₚ n').Subset ((earliest P G n n').union (Assignments.sdiff (G.ηₚ n) (ue P n)))

def transfer (P : Program) (G : Ghosts) (n n' : Node) : Prop :=
  (G.τₚ n).Subset (G.ηₚ n') ∧ (G.πᵤ n').Subset (G.τᵤ n)

/-! ## Per-step relation, validity, order, analysis. -/

def R (P : Program) (G : Ghosts) (n n' : Node) : Prop :=
  predict P G n n' ∧ check P G n ∧ update P G n n' ∧ transfer P G n n'

def Valid (P : Program) (G : Ghosts) : Prop :=
  (∀ c c', Step P c c' → R P G c.node c'.node) ∧
  -- **Fault/stuck terminal `check`** — the backward-must dual of the halt seed. A config that is not
  -- `Final` and cannot `Step` (an always-faulting `assign`, or an out-of-range node) is an
  -- end of execution, so the node-local `check` (`πₐ ⊆ ueₙ∪passₙ`, `ueₙ∖latestNodeₙ ⊆ πᵤ`) holds there just
  -- as it does at a step-tail. Without this the backward-must ghosts (`πₐ`,`πᵤ`) are unconstrained at
  -- non-stepping nodes and that freedom leaks backward through `predict` into observable nodes; with it,
  -- `Valid ⇒ check` at *every* node, so the staged bundle is `Le`-extremal (`staged_bundle`).
  (∀ c, ¬ Final P c → (¬ ∃ c', Step P c c') → check P G c.node) ∧
  (∀ c, Final P c → (G.πₐ c.node).Subset ∅) ∧
  (G.ηₐ P.entry).Subset ∅ ∧ (G.ηₚ P.entry).Subset ∅ ∧
  (∀ n, (G.πₐ n).Subset (allExprs P) ∧ (G.ηₐ n).Subset (allExprs P) ∧ (G.ηₚ n).Subset (allExprs P) ∧
        (G.πᵤ n).Subset (allExprs P) ∧ (G.τₚ n).Subset (allExprs P) ∧
        (G.τᵤ n).Subset (allExprs P))

/-- Must-ghosts (`πₐ,ηₐ,ηₚ,τₚ`) grow; may-ghosts (`πᵤ,τᵤ`) shrink. -/
def Le (G G' : Ghosts) : Prop :=
  ∀ n, (G.πₐ n).Subset (G'.πₐ n) ∧ (G.ηₐ n).Subset (G'.ηₐ n) ∧ (G.ηₚ n).Subset (G'.ηₚ n) ∧
       (G.τₚ n).Subset (G'.τₚ n) ∧
       (G'.πᵤ n).Subset (G.πᵤ n) ∧ (G'.τᵤ n).Subset (G.τᵤ n)

/-- **Flat/naive analysis — REFUTED for LCM.** The `Le`-greatest valid `G`. This is the *wrong* target:
    `Le` maximizes the must-ghosts `ηₐ` and `ηₚ` independently, but `ηₐ` enters `earliest` antitonically, so
    **no** `Le`-greatest valid `G` exists (`BridgeFailFast.gs_not_greatest`). Kept only for the contrast; the
    real spec is the staged `Analysis` below. -/
def FlatAnalysis (P : Program) (G : Ghosts) : Prop :=
  Valid P G ∧ ∀ G', Valid P G' → Le G' G

/-- **Set-equality of two ghost components** (`Assignments.Subset` both ways, pointwise) — how a competing family
    is said to *agree* with `G` on one of `G`'s dependency ghosts. -/
def eqv (a b : Node → Assignments) : Prop := ∀ n, (a n).Subset (b n) ∧ (b n).Subset (a n)

theorem eqv.symm {a b : Node → Assignments} (h : eqv a b) : eqv b a := fun n => ⟨(h n).2, (h n).1⟩

/-- **The analysis — staged (DAG-lexicographic) selection.** `G` is valid, and at each ghost coordinate it
    is extremal (must: greatest `⊇`; may: least `⊆`) among the valid families `G'` that agree with `G` on
    that coordinate's dependencies — the staging `πₐ,ηₐ → ηₚ → τₚ → πᵤ → τᵤ`, mirroring `LcmSpec` field
    for field. Fixing the dependencies (crucially `ηₐ` *before* `ηₚ`) dissolves the antitone tension that
    makes the flat `FlatAnalysis` unsatisfiable. Unique up to `eqv` (`Ghost.staged_unique`). -/
def Analysis (P : Program) (G : Ghosts) : Prop :=
  Valid P G ∧
  -- πₐ : greatest anticipated, no dependencies
  (∀ G', Valid P G' → ∀ n, (G'.πₐ n).Subset (G.πₐ n)) ∧
  -- ηₐ : greatest available, no dependencies
  (∀ G', Valid P G' → ∀ n, (G'.ηₐ n).Subset (G.ηₐ n)) ∧
  -- ηₚ : greatest postponable, given πₐ, ηₐ   ← avail fixed before postp is maximized
  (∀ G', Valid P G' → eqv G'.πₐ G.πₐ → eqv G'.ηₐ G.ηₐ →
        ∀ n, (G'.ηₚ n).Subset (G.ηₚ n)) ∧
  -- τₚ : greatest transfer, given ηₚ
  (∀ G', Valid P G' → eqv G'.ηₚ G.ηₚ → ∀ n, (G'.τₚ n).Subset (G.τₚ n)) ∧
  -- πᵤ : least used, given πₐ, ηₐ, ηₚ, τₚ
  (∀ G', Valid P G' → eqv G'.πₐ G.πₐ → eqv G'.ηₐ G.ηₐ → eqv G'.ηₚ G.ηₚ → eqv G'.τₚ G.τₚ →
        ∀ n, (G.πᵤ n).Subset (G'.πᵤ n)) ∧
  -- τᵤ : least transfer, given πᵤ
  (∀ G', Valid P G' → eqv G'.πᵤ G.πᵤ → ∀ n, (G.τᵤ n).Subset (G'.τᵤ n))


/-! ## Staged well-posedness (uniqueness of the staged `Analysis`). -/

/-- **`G ≈ H` coordinatewise** — the conclusion of uniqueness (all six ghosts set-equal). -/
structure GEqv (G H : Ghosts) : Prop where
  πₐ : eqv G.πₐ H.πₐ
  ηₐ : eqv G.ηₐ H.ηₐ
  ηₚ : eqv G.ηₚ H.ηₚ
  πᵤ : eqv G.πᵤ H.πᵤ
  τₚ : eqv G.τₚ H.τₚ
  τᵤ : eqv G.τᵤ H.τᵤ

/-- **Well-posedness: the staged spec pins a unique solution (up to set-equality).** Purely in `Ghost`
    vocabulary — no semantics, no `Bundle`. Each coordinate is squeezed by applying `G`'s stage to `H` and
    `H`'s stage to `G`; the dependency hypotheses each stage needs are exactly the `≈`s already proved by
    the earlier stages (fed forward, `eqv.symm` as needed). This is why the *staged* order is well-behaved
    where the flat one is not: no coordinate is asked to beat a family that disagrees upstream. -/
theorem staged_unique {P : Program} {G H : Ghosts}
    (hG : Analysis P G) (hH : Analysis P H) : GEqv G H := by
  obtain ⟨hGv, hGπₐ, hGηₐ, hGηₚ, hGτₚ, hGπᵤ, hGτᵤ⟩ := hG
  obtain ⟨hHv, hHπₐ, hHηₐ, hHηₚ, hHτₚ, hHπᵤ, hHτᵤ⟩ := hH
  have Eπₐ : eqv G.πₐ H.πₐ := fun n => ⟨hHπₐ G hGv n, hGπₐ H hHv n⟩
  have Eηₐ : eqv G.ηₐ H.ηₐ := fun n => ⟨hHηₐ G hGv n, hGηₐ H hHv n⟩
  have Eηₚ : eqv G.ηₚ H.ηₚ :=
    fun n => ⟨hHηₚ G hGv Eπₐ Eηₐ n, hGηₚ H hHv Eπₐ.symm Eηₐ.symm n⟩
  have Eτₚ : eqv G.τₚ H.τₚ :=
    fun n => ⟨hHτₚ G hGv Eηₚ n, hGτₚ H hHv Eηₚ.symm n⟩
  have Eπᵤ : eqv G.πᵤ H.πᵤ :=
    fun n => ⟨hGπᵤ H hHv Eπₐ.symm Eηₐ.symm Eηₚ.symm Eτₚ.symm n, hHπᵤ G hGv Eπₐ Eηₐ Eηₚ Eτₚ n⟩
  have Eτᵤ : eqv G.τᵤ H.τᵤ :=
    fun n => ⟨hGτᵤ H hHv Eπᵤ.symm n, hHτᵤ G hGv Eπᵤ n⟩
  exact ⟨Eπₐ, Eηₐ, Eηₚ, Eπᵤ, Eτₚ, Eτᵤ⟩

end BaseLanguage.LCM.Ghost

/-! ## The flat-order refutation (`no-greatest`). -/

namespace BaseLanguage.LCM.BridgeFailFast
open Tac Normalize Semantics Std
open BaseLanguage.Analyses.LCM BaseLanguage.LCM.Ghost

/-- `∅ ⊆ x` for any `Assignments`. -/
theorem empty_Sub (x : Assignments) : Assignments.Subset ∅ x := fun _ he => absurd he Std.HashSet.not_mem_empty

/-- `a ⊆ a ∪ b`. -/
theorem Sub_union_left (a b : Assignments) : Assignments.Subset a (Assignments.union a b) :=
  fun _ he => Assignments.mem_union.mpr (Or.inl he)

/-- The staged bundle read as a ghost tuple `G = (πₐ,ηₐ,ηₚ,πᵤ,τₚ,τᵤ)`. -/
def G_S {P : Program} (S : LcmSpec P) : Ghosts :=
  ⟨S.πₐ, S.ηₐ, S.ηₚ, S.πᵤ, S.τₚ, S.τᵤ⟩

/-- The counterexample family: the staged `anti`, but **`avail ≡ ∅`** and its greatest `postp`
    `P'`; the may/transfer ghosts pinned to trivial extremes (`⊤` for may, `∅` for `τₚ`) so validity is
    immediate and no `Le`-comparison with `G_S` is obstructed on those coordinates. -/
def G_emptyAvail {P : Program} (S : LcmSpec P) (P' : Node → Assignments) : Ghosts :=
  ⟨S.πₐ, (fun _ => ∅), P', (fun _ => allExprs P), (fun _ => ∅), (fun _ => allExprs P)⟩

/-- **Unconditional: `S.ηₚ ⊑ P'` pointwise.** Dropping `avail` to `∅` can only *enlarge* `earliest`
    (`availableOut(∅,c) = de c ⊆ availableOut(S.ηₐ,c)`, so `¬availableOut` grows), hence the greatest
    `ηₚ` over `ηₐ ≡ ∅` contains the staged one. Proof: `S.ηₚ` is itself a `Postponable` family
    for `ηₐ ≡ ∅` (its update RHS only *grows* when `earliest` grows), so greatestness of `P'` applies. -/
theorem postp_le_emptyAvail {P : Program} (S : LcmSpec P) {P' : Node → Assignments}
    (hP' : Greatest Assignments.Subset (Postponable P S.πₐ (fun _ => ∅)) P') :
    ∀ n, Assignments.Subset (S.ηₚ n) (P' n) := by
  -- `earliest` is antitone in `avail`: bigger `avail` ⇒ bigger `availableOut` ⇒ smaller `¬availableOut`.
  have hearl : ∀ i j, Assignments.Subset (BaseLanguage.Analyses.LCM.earliest P S.πₐ S.ηₐ i j)
                                 (BaseLanguage.Analyses.LCM.earliest P S.πₐ (fun _ => ∅) i j) := by
    intro i j
    unfold BaseLanguage.Analyses.LCM.earliest
    -- only the middle `compl (availableOut ·)` factor differs; the other two factors are identical.
    apply Assignments.inter_subset_inter _ (Assignments.subset_refl)
    apply Assignments.inter_subset_inter (Assignments.subset_refl)
    -- `compl (availableOut S.ηₐ i) ⊆ compl (availableOut ∅ i)` since `availableOut ∅ i ⊆ availableOut S.ηₐ i`.
    intro _e he
    rw [BaseLanguage.Analyses.LCM.compl, Assignments.mem_sdiff] at he ⊢
    refine ⟨he.1, ?_⟩
    intro hin
    apply he.2
    -- `availableOut ∅ i = de i ∪ (∅ ∩ pass i) ⊆ de i ∪ (S.ηₐ i ∩ pass i) = availableOut S.ηₐ i`.
    rw [BaseLanguage.Analyses.LCM.availableOut, Assignments.mem_union] at hin ⊢
    exact hin.imp (fun h => h) (fun h => absurd (Assignments.mem_inter.mp h).1 Std.HashSet.not_mem_empty)
  -- Hence `S.ηₚ` satisfies `Postponable` for `avail ≡ ∅`; greatestness of `P'` gives the containment.
  refine hP'.2 S.ηₚ ⟨?_, S.isPostp.seed, S.isPostp.within⟩
  intro c c' hstep
  refine Assignments.subset_trans (S.isPostp.update c c' hstep) ?_
  exact Assignments.union_subset_union (hearl c.node c'.node) Assignments.subset_refl

/-- **`G_emptyAvail` is `Ghost.Valid`.** Every clause is discharged by an `S`-field, an `∅ ⊆ ·`, or a
    `· ⊆ ⊤`; the only substantive clause is `ηₚ`'s `update`, which is exactly `P'`'s `Postponable.update`. -/
theorem emptyAvail_family_valid {P : Program} (S : LcmSpec P) {P' : Node → Assignments}
    (hP' : Greatest Assignments.Subset (Postponable P S.πₐ (fun _ => ∅)) P') :
    Ghost.Valid P (G_emptyAvail S P') := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ∀ steps, R = predict ∧ check ∧ update ∧ transfer
    intro c c' hstep
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
    · exact S.isAnti.predict c c' hstep                          -- πₐ predict
    · exact Sub_union_left _ _                                     -- πᵤ ⊆ πᵤ ∪ … (πᵤ ≡ ⊤)
    · exact S.isAnti.check c.node                                -- πₐ check
    · exact fun e he => ue_mem_allExprs (Assignments.mem_sdiff.mp he).1   -- ue ∖ latestNode ⊆ ⊤
    · exact empty_Sub _                                            -- ηₐ' ⊆ … (ηₐ ≡ ∅)
    · exact hP'.1.update c c' hstep                               -- ηₚ' ⊆ earliest ∪ (ηₚ ∖ ue)  ← the crux
    · exact empty_Sub _                                            -- τₚ ⊆ ηₚ' (τₚ ≡ ∅)
    · exact Assignments.subset_refl                                        -- πᵤ' ⊆ τᵤ (both ⊤)
  · -- fault/stuck terminal `check` (πₐ from `isAnti.check`; πᵤ ≡ ⊤ absorbs `ue ∖ latestNode`)
    exact fun c _ _ => ⟨S.isAnti.check c.node,
                        fun e he => ue_mem_allExprs (Assignments.mem_sdiff.mp he).1⟩
  · exact fun c hfin => S.isAnti.seed c hfin                     -- Final ⇒ πₐ ⊆ ∅ (haltSeed)
  · exact empty_Sub _                                             -- ηₐ entry ⊆ ∅
  · exact hP'.1.seed                                              -- ηₚ entry ⊆ ∅ (entrySeed)
  · intro n                                                       -- bounds
    exact ⟨S.isAnti.within n, empty_Sub _, hP'.1.within n, Assignments.subset_refl,
           empty_Sub _, Assignments.subset_refl⟩

/-- **THE REFUTATION.** If the greatest `postp` over `avail ≡ ∅` strictly exceeds the staged `S.ηₚ`
    at some node (`hgap` — there is a genuinely-available redundant expression), then the staged bundle
    `G_S` is **not** `⊑`-greatest among valid ghost families: `¬ Ghost.FlatAnalysis P G_S`. Witness: the valid
    family `G_emptyAvail`, whose `ηₚ = P'` is *not* `⊆ S.ηₚ`, so `Le G_emptyAvail G_S` fails. -/
theorem gs_not_greatest {P : Program} (S : LcmSpec P) {P' : Node → Assignments}
    (hP' : Greatest Assignments.Subset (Postponable P S.πₐ (fun _ => ∅)) P')
    (hgap : ∃ n, ¬ Assignments.Subset (P' n) (S.ηₚ n)) :
    ¬ Ghost.FlatAnalysis P (G_S S) := by
  rintro ⟨_hvalid, hgreatest⟩
  obtain ⟨n, hn⟩ := hgap
  -- greatestness applied to the valid `avail ≡ ∅` family forces `P' ⊆ S.ηₚ` at every node.
  have hle := hgreatest (G_emptyAvail S P') (emptyAvail_family_valid S hP')
  exact hn (hle n).2.2.1

end BaseLanguage.LCM.BridgeFailFast
