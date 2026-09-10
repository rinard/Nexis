-- Copyright (c) 2026 Martin Rinard
import Seam.lcmmat.Adapter
import BaseLanguage.LCM.Transform

/-!
# The materialization gate is sound for **every valid** analysis

LCM's correctness proof assumes `Extremal S`, and the reason is one place: the replace gate

```
recoverable P S n = πᵤK(n) ∪ insertBefore(n)          -- BaseLanguage/LCM/Transform.lean
```

A valid but too-large `πᵤ` admits a rewrite with no matching insertion, and the transformed program then
reads a temporary nothing ever wrote (`examples/lcm-extremality/ExtremalityNeeded.lean` observes `0` where
the source observes `7`). Excluding that needs a **lower** bound on a **least** fixpoint — leastness
quantifies over every solution, so no clause can impose it, and the proof must take extremality as a
hypothesis instead.

`Materialized ηₘ` inverts the polarity. Its single `update` clause is an **upper** bound, and this file
proves what that buys: along any source run, every expression `ηₘ` admits was genuinely **placed by the
transform on the path actually taken**. The proof uses `hm.update`, `hm.seed` and `hm.within` — three
validity fields — and **no extremality whatsoever**, of `ηₘ` or of any other ghost.

`Written` is the placement trace: an inductive relation over the run, not a computed set, per the prime
directive's second clause (reachability is a traversal, so it is an inductive relation — no fixpoint, no
fuel, no analysis domain).

## Scope — what this does and does not establish

`matAvail_written` is the *analysis-level* half of soundness: it discharges the obligation that made
extremality necessary. The remaining half is store-level and orthogonal — that a placed temporary actually
holds its expression's value, which is the block-execution reasoning (`matNode_execF`, `steps_insSeg`) the
existing development already carries and which never depended on extremality. Wiring the two together is
the `Cov`/`Match` rebuild; that is not done here, and `BaseLanguage/LCM/Transform.lean` still uses the
classical gate.
-/

namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std
open BaseLanguage.Analyses.LCM

variable {P : Program} {πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments}

/-- **The placement trace.** `Written c e` holds when the transform has written the temporary for `e`
    somewhere along the run reaching `c`, and nothing since has invalidated it. An inductive relation
    over the semantic `Step`, so it speaks about the path actually taken rather than about every path. -/
inductive Written (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments) : Config → Expr → Prop
  /-- placed on this step, by the node-entry chain that survives `c`'s instruction or by the edge chain -/
  | place {c c' : Config} {e : Expr} :
      Step P c c' → e ∈ matPlace P πₐ ηₐ ηₚ τₚ τᵤ c.node c'.node → Written P πₐ ηₐ ηₚ τₚ τᵤ c' e
  /-- already written, and `c`'s instruction does not redefine an operand of `e` -/
  | carry {c c' : Config} {e : Expr} :
      Step P c c' → Written P πₐ ηₐ ηₚ τₚ τᵤ c e → e ∈ pass P c.node → Written P πₐ ηₐ ηₚ τₚ τᵤ c' e

/-- The `∖ notPass` carry, read back as transparency. Needs only that `e` is in the universe, which the
    ghost's own `within` clause supplies. -/
theorem mem_sdiff_notPass {n : Node} {e : Expr} {A : Assignments}
    (h : e ∈ Assignments.sdiff A (notPass P n)) (hall : e ∈ allExprs P) :
    e ∈ A ∧ e ∈ pass P n := by
  obtain ⟨hA, hnp⟩ := Assignments.mem_sdiff.mp h
  refine ⟨hA, ?_⟩
  by_cases hp : e ∈ pass P n
  · exact hp
  · exact absurd (Assignments.mem_sdiff.mpr ⟨hall, hp⟩) hnp

/-- **Soundness of the materialization gate, from validity alone.** On any run from the entry, every
    expression `ηₘ` admits at the configuration reached was placed by the transform along that run.

    The hypotheses are `Materialized` — one ghost's validity — and nothing else. In particular there is no
    `Extremal`, and no assumption about `πₐ`, `ηₐ`, `ηₚ`, `τₚ` or `τᵤ` beyond their appearing as the
    parameters `matPlace` reads. That is the whole point: the classical gate has no counterpart to this
    statement without extremality, and `ExtremalityNeeded.lean` is why. -/
theorem matAvail_written {m : Node → Assignments}
    (hm : Materialized P πₐ ηₐ ηₚ τₚ τᵤ m) {σ : Store} {c : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c) :
    ∀ e ∈ m c.node, Written P πₐ ηₐ ηₚ τₚ τᵤ c e := by
  induction hrun with
  | refl =>
      -- at the entry the seed is `entrySeed = ∅`, so `ηₘ` admits nothing and the claim is vacuous
      intro e he
      exact absurd (hm.seed e he) (by
        intro hmem
        simp only [entrySeed, Assignments.empty] at hmem
        exact Std.HashSet.not_mem_empty hmem)
  | @tail a b hsteps hstep ih =>
      intro e he
      rcases Assignments.mem_union.mp (hm.update a b hstep e he) with hpl | hcarry
      · exact Written.place hstep hpl
      · obtain ⟨hb, hpass⟩ :=
          mem_sdiff_notPass hcarry (hm.within a.node e (Assignments.mem_sdiff.mp hcarry).1)
        exact Written.carry hstep (ih e hb) hpass

/-- The solved bundle satisfies it — so the compiler's own analysis result is covered. -/
theorem matAvail_written_solved (P : Program) (wf : WellFormed P) {σ : Store} {c : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c) :
    ∀ e ∈ matAvail P c.node,
      Written P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P) c e :=
  matAvail_written (matAvail_valid P wf) hrun

/-! ## The placement trace is the transform's own placement

`matPlace` is a node-local, authored in `analyses/lcmmat/LcmMatDefs.lean` so a `.gsl` clause can name it.
The theorem below is the obligation that makes it *mean* what the name says: it is exactly the transform's
insert sets, split by phase.

The phase split is the delicate part and it is what this pins down. `insertBefore i` runs at `i`'s block
entry, **before** `i`'s own instruction, so it reaches the successor only through the transparency filter
`pass i`; `insertEdge i j` runs **after** that instruction, on the edge, so it reaches the successor
unconditionally. Getting that backwards would make `ηₘ` claim availability for a temporary the very next
instruction invalidates.

Stated for a bundle whose filter admits everything (`S.keep e = true`), because `matPlace` reads the
unfiltered `τᵤ` where the transform gates on `τᵤK = τᵤ ∩ keep` — the classical-mode scope recorded in
`LcmMat.gsl`. -/

/-- `latestOutG` is `latestOut` with the bundle's ghosts supplied positionally. -/
theorem latestOutG_eq (P : Program) (S : LCM.LcmSpec P) (i : Node) :
    latestOutG P S.πₐ S.ηₐ S.ηₚ i = LCM.latestOut P S i := rfl

/-- **`matPlace` is the transform's placement along the step, phase-split.** The `∩ pass` on the
    node-entry half and its absence on the edge half are forced by where each chain sits relative to the
    node's own instruction. -/
theorem mem_matPlace_iff {P : Program} {S : LCM.LcmSpec P} (hkeep : ∀ e, S.keep e = true)
    {i j : Node} {e : Expr} :
    e ∈ matPlace P S.πₐ S.ηₐ S.ηₚ S.τₚ S.τᵤ i j ↔
      e ∈ LCM.insertEdge P S i j ∨ (e ∈ LCM.insertBefore P S i ∧ e ∈ pass P i) := by
  unfold matPlace edgeGen nodeGen LCM.insertEdge LCM.insertBefore
  constructor
  · intro h
    rcases Assignments.mem_union.mp h with hE | hN
    · obtain ⟨hlat, hτ⟩ := Assignments.mem_inter.mp hE
      exact Or.inl (Assignments.mem_inter.mpr ⟨hlat, LCM.mem_τᵤK.mpr ⟨hτ, hkeep e⟩⟩)
    · obtain ⟨hng, hpass⟩ := Assignments.mem_inter.mp hN
      obtain ⟨hdiff, hτ⟩ := Assignments.mem_inter.mp hng
      exact Or.inr ⟨Assignments.mem_inter.mpr ⟨hdiff, LCM.mem_τᵤK.mpr ⟨hτ, hkeep e⟩⟩, hpass⟩
  · intro h
    rcases h with hE | ⟨hB, hpass⟩
    · obtain ⟨hlat, hτK⟩ := Assignments.mem_inter.mp hE
      exact Assignments.mem_union.mpr (Or.inl
        (Assignments.mem_inter.mpr ⟨hlat, (LCM.mem_τᵤK.mp hτK).1⟩))
    · obtain ⟨hdiff, hτK⟩ := Assignments.mem_inter.mp hB
      exact Assignments.mem_union.mpr (Or.inr (Assignments.mem_inter.mpr
        ⟨Assignments.mem_inter.mpr ⟨hdiff, (LCM.mem_τᵤK.mp hτK).1⟩, hpass⟩))

/-! ## The statement in the transform's own vocabulary

`Written` is phrased over `matPlace`, the node-local a `.gsl` clause can name. `PlacedBy` is the same
trace phrased over `Transform.lean`'s insert sets, and `written_placedBy` transports one to the other.
Composing with `matAvail_written` gives the analysis-level soundness statement in terms the transform
itself uses, with no extremality anywhere in the chain. -/

/-- The transform's placement trace: `PlacedBy c e` holds when the transform has materialized `tempFor e`
    along the run reaching `c` and nothing since has invalidated it. Phrased in `Transform.lean`'s
    vocabulary — `insertEdge` on the edge, `insertBefore` at the node entry (surviving the node's own
    instruction), `pass` for the carry. -/
inductive PlacedBy (P : Program) (S : LCM.LcmSpec P) : Config → Expr → Prop
  /-- materialized by the edge chain, after `c`'s instruction -/
  | edge {c c' : Config} {e : Expr} :
      Step P c c' → e ∈ LCM.insertEdge P S c.node c'.node → PlacedBy P S c' e
  /-- materialized by the entry chain at `c`, and `c`'s instruction leaves it valid -/
  | entry {c c' : Config} {e : Expr} :
      Step P c c' → e ∈ LCM.insertBefore P S c.node → e ∈ pass P c.node → PlacedBy P S c' e
  /-- already materialized, and `c`'s instruction does not redefine an operand of `e` -/
  | carry {c c' : Config} {e : Expr} :
      Step P c c' → PlacedBy P S c e → e ∈ pass P c.node → PlacedBy P S c' e

theorem written_placedBy {P : Program} {S : LCM.LcmSpec P} (hkeep : ∀ e, S.keep e = true)
    {c : Config} {e : Expr} (h : Written P S.πₐ S.ηₐ S.ηₚ S.τₚ S.τᵤ c e) : PlacedBy P S c e := by
  induction h with
  | place hstep hpl =>
      rcases (mem_matPlace_iff hkeep).mp hpl with hE | ⟨hB, hpass⟩
      · exact PlacedBy.edge hstep hE
      · exact PlacedBy.entry hstep hB hpass
  | carry hstep _ hpass ih => exact PlacedBy.carry hstep ih hpass

/-- **The analysis-level soundness statement, in the transform's own vocabulary.** On any run from the
    entry, every expression the materialization gate admits was materialized by the transform along that
    run. The hypotheses are one ghost's validity and the mode's filter — **no extremality**, of any ghost.

    This is the obligation whose classical counterpart forces `Extremal S` into LCM's correctness proof.
    What remains between here and a validity-only `transform_preserves_halt` is the store-level half — that
    a materialized temporary holds its expression's value — and the `Match`/`Cov` rebuild that consumes
    both. Neither is done; `Transform.lean` still gates on `πᵤK ∪ insertBefore`. -/
theorem matAvail_placedBy {P : Program} {S : LCM.LcmSpec P} {m : Node → Assignments}
    (hkeep : ∀ e, S.keep e = true)
    (hm : Materialized P S.πₐ S.ηₐ S.ηₚ S.τₚ S.τᵤ m) {σ : Store} {c : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ c) :
    ∀ e ∈ m c.node, PlacedBy P S c e :=
  fun e he => written_placedBy hkeep (matAvail_written hm hrun e he)

#assert_clean_axioms written_placedBy
#assert_clean_axioms matAvail_placedBy
#assert_clean_axioms latestOutG_eq
#assert_clean_axioms mem_matPlace_iff
#assert_clean_axioms matAvail_written
#assert_clean_axioms matAvail_written_solved

end BaseLanguage.Analyses.LcmMat
