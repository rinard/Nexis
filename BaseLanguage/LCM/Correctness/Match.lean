-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Correctness.ChainExec

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

/-! ## The forward-simulation relation `Match` and its initial boundary

`μ` is carried **operationally**: the materialized-temp set `M : Assignments`. Clause 3 is the `Holds`
predicate — pure store-bookkeeping, no ghost. Clause 4 (`M ⊆ allExprs`) keeps `tempFor` injective and
`insert_fresh` applicable on `M`. -/

/-- **`μ` membership** (`Holds`): temp `h` currently holds expression `e`'s source value. -/
def Holds (d c : Store) (h : Var) (e : Expr) : Prop :=
  eval d (.atom (.var h)) = eval c e

/-! ### The `Holds` (`μ`) lifecycle — birth / maintenance / use (used by `match_step`).
    Pure store-bookkeeping; no analysis. -/

/-- **Maintenance.** A source step `c → c.update w u` matched by a target step `d → d.update wT uT`
    preserves `Holds`, given `e` does not read the source's redefined `w` (transparency) and the target's
    redefined `wT` is not the temp `h` (freshness). -/
theorem transp_holds {c d : Store} {h w wT : Var} {e : Expr} {u uT : Val}
    (he_w : exprReadsVar e w = false) (hT_h : wT ≠ h) (hHolds : Holds d c h e) :
    Holds (d.update wT uT) (c.update w u) h e := by
  unfold Holds at hHolds ⊢
  have hne : h ≠ wT := fun hh => hT_h hh.symm
  have htgt : eval (d.update wT uT) (.atom (.var h)) = eval d (.atom (.var h)) := by
    simp [eval, evalAtom, Store.update, hne]
  rw [htgt, hHolds, eval_update_not_read he_w]

/-- A variable is **non-fresh** if it is not one of LCM's hoisting temps (`tempFor`). Pre-existing
    variables — source `.orig` *and* temps introduced by earlier passes — are all non-fresh; only the
    `tempFor` temps the transform materializes are fresh. The two stores agree on exactly the non-fresh
    variables (the transform writes every pre-existing variable identically). -/
def NonFresh (P : Program) (x : Var) : Prop := ∀ e, tempFor P e ≠ x

/-- An operand read by a source instruction is non-fresh (`tempFor` is fresh in `P`, `_unread`). -/
theorem nonFresh_of_used {P : Program} {nd : Node} {instr : Cmd} {x : Var}
    (hf : P.fetch nd = some instr) (hx : x ∈ instrUsedVars instr) : NonFresh P x :=
  fun e h => (tempFor_unread P e hf) (h ▸ hx)

/-- An original (observable) variable is non-fresh (`tempFor` temps are never original). -/
theorem nonFresh_of_orig {P : Program} {x : Var} (h : varIsOrig x = true) : NonFresh P x := by
  intro e he
  have hnb := tempFor_nonobs P e
  rw [he, h] at hnb
  exact absurd hnb (by simp)

/-- The variable a source instruction defines is non-fresh (`tempFor` clashes with no def, `noClash`). -/
theorem nonFresh_of_def {P : Program} {nd : Node} {instr : Cmd} {x : Var}
    (hf : P.fetch nd = some instr) (hx : instrDefVar instr = some x) : NonFresh P x := by
  intro e h
  apply (freshN_freshForN P).noClash ((allExprs P).toList.idxOf e) hf
  rw [hx]; exact congrArg some h.symm

/-- **The forward-simulation relation.** Source `c` and target `d` sit at the same block label; the
    stores agree on every **non-fresh** variable (the transform only adds `tempFor` temps); every temp in
    the materialized set `M` **holds** its expression's source value; and `M ⊆ allExprs`. -/
def Match (P : Program) (S : LcmSpec P) (c d : Config) (M : Assignments) : Prop :=
  d.node = blockOff P S c.node ∧
  (∀ x : Var, NonFresh P x → d.store x = c.store x) ∧
  (∀ e ∈ M, Holds d.store c.store (tempFor P e) e) ∧
  (∀ e ∈ M, e ∈ allExprs P)

/-- **`match_init`** — at the entry, `M = ∅`, the stores are equal, and the block labels coincide. -/
theorem match_init {P : Program} (S : LcmSpec P) (σ : Store) :
    Match P S ⟨P.entry, σ⟩ ⟨blockOff P S P.entry, σ⟩ Assignments.empty := by
  refine ⟨rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro e he; simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty
  · intro e he; simp only [Assignments.empty] at he; exact absurd he Std.HashSet.not_mem_empty

/-! ## Forward (head) form of a run

`Step`/`Steps` is built back-to-front (`tail`), and `Steps` is a `Prop` so it carries no usable length
measure. The LCM fault hazard (§5) needs to walk a halting run **forwards** (down-safety propagates an
anticipated expression forward until it is computed). A **head-recursive** RTC `StepsH` gives exactly that
— its native recursor peels the *first* step — and `Steps` converts into it. -/

/-- Head-recursive reflexive–transitive closure: `cons` a step at the **front**. -/
inductive StepsH (P : Program) : Config → Config → Prop where
  | refl {c} : StepsH P c c
  | head {a b c} : Step P a b → StepsH P b c → StepsH P a c

/-- Append a step at the end of a head-run. -/
theorem StepsH.snoc {P : Program} {a b c : Config}
    (h : StepsH P a b) (s : Step P b c) : StepsH P a c := by
  induction h with
  | refl => exact .head s .refl
  | head s' _ ih => exact .head s' (ih s)

/-- Every `Steps` run is a head-run (so we may induct on it front-to-back). -/
theorem steps_toH {P : Program} {c c' : Config} (h : Steps P c c') : StepsH P c c' := by
  induction h with
  | refl => exact .refl
  | tail _ s ih => exact ih.snoc s


/-! ## The LCM fault hazard — down-safe inserts never fault on a halting run (§5)

The crux that distinguishes LCM correctness from PDCE: hoisting an expression `e` *earlier* could fault
where the source diverges — but on a **halting** source run, down-safety (`πₐ`) guarantees `e` is
evaluated **on that very path** (anticipation propagates `e` forward, via `predict`, until a node computes
it; that computation fired, so it did not fault, and transparency keeps `e`'s operands — hence its value —
unchanged back to the insert point). So a down-safe insert never adds a fault on a halting run. -/

/-- A step out of node `n` changes no value of an expression transparent at `n` (it does not redefine an
    operand `e` reads). -/
theorem eval_step_transp {P : Program} {n : Node} {e : Expr} {c c' : Config}
    (hstep : Step P c c') (hn : c.node = n) (ht : transpB P n e = true) :
    eval c'.store e = eval c.store e := by
  cases hstep with
  | @assign nd σ x ee next v hf hv =>
      subst hn
      simp only [transpB, hf, instrDefVar] at ht
      have : exprReadsVar e x = false := by simpa using ht
      exact eval_update_not_read this
  | ifzT _ _ => subst hn; rfl
  | ifzF _ _ => subst hn; rfl
  | noop _ => subst hn; rfl

/-- **Down-safe no-fault.** On a halting run from `c`, every `e ∈ anti(c.node)` evaluates (no fault) at
    `c.store`. Proved by forward induction on the run length: either `e` is computed at `c` (the first
    step is the assign, which fired ⇒ no fault), or `e` survives transparently to the successor, where the
    shorter tail run gives the value, pulled back across the transparent step. -/
theorem antiNoFault {P : Program} (S : LcmSpec P) {c c_f : Config}
    (h : StepsH P c c_f) (hfin : Final P c_f) :
    ∀ e, e ∈ S.πₐ c.node → ∃ v, eval c.store e = some v := by
  revert hfin
  induction h with
  | @refl c =>
      intro hfin e he
      exact absurd (S.isAnti.seed c hfin e he) (by
        intro hmem; simp only [haltSeed, Assignments.empty] at hmem; exact Std.HashSet.not_mem_empty hmem)
  | @head c c' cend hstep _ ih =>
      intro hfin e he
      by_cases hue : e ∈ ue P c.node
      · -- `e` is computed at `c`; the (fired) head step is its assign, so it did not fault
        obtain ⟨x, next, hf, _⟩ := mem_ue hue
        obtain ⟨cn, cσ⟩ := c
        cases hstep with
        | @assign nd σ x' ee next' v hf' hv =>
            rw [hf'] at hf
            injection Option.some.inj hf with _ hee _
            exact ⟨v, hee ▸ hv⟩
        | ifzT hf' _ => rw [hf'] at hf; exact absurd hf (by simp)
        | ifzF hf' _ => rw [hf'] at hf; exact absurd hf (by simp)
        | noop hf'   => rw [hf'] at hf; exact absurd hf (by simp)
      · -- `e` survives transparently to the successor `c'`; recurse on the tail
        have htr : e ∈ Assignments.union (ue P c.node) (pass P c.node) := S.isAnti.check c.node e he
        have htransp : e ∈ pass P c.node := by
          rw [Assignments.mem_union] at htr; rcases htr with h1 | h2
          · exact absurd h1 hue
          · exact h2
        have hpred : e ∈ S.πₐ c'.node :=
          S.isAnti.predict c c' hstep e (by rw [Assignments.mem_sdiff]; exact ⟨he, hue⟩)
        obtain ⟨v, hv⟩ := ih hfin e hpred
        have htb : transpB P c.node e = true := by
          unfold pass at htransp; rw [Assignments.mem_filter'] at htransp; exact htransp.2
        exact ⟨v, by rw [← eval_step_transp hstep rfl htb]; exact hv⟩

/-! ## Placement containments and the threaded `ηₚ ⊆ πₐ` invariant

`insertBefore ⊆ latestNode ⊆ ηₚ`, and along realized steps `ηₚ ⊆ πₐ` is maintained (so the inserts at a
node are anticipated there, letting `antiNoFault` certify them fault-free). The base case
`ηₚ(entry) ⊆ ∅ ⊆ πₐ(entry)` holds by `isPostp.1.seed`; the simulation threads it forward. -/

/-- `latestNode n ⊆ postp n` (the node-form intersects `postp` with the placement frontier). -/
theorem latestNode_sub_postp {P : Program} (S : LcmSpec P) (n : Node) :
    Assignments.Subset (latestNode P S.ηₚ S.τₚ n) (S.ηₚ n) := by
  intro e he; unfold latestNode at he; rw [Assignments.mem_inter] at he; exact he.1

/-- An inserted expression is in the computed universe (`usedOut`'s `bound`). -/
theorem insertBefore_mem_allExprs {P : Program} {S : LcmSpec P} {i : Node} {e : Expr}
    (he : e ∈ (insertBefore P S i).toList) : e ∈ allExprs P := by
  rw [mem_insertBefore] at he; exact S.isUsedOut.within i e he.2

/-- **`postp ⊆ anti` is maintained across one realized step.** Uses `isPostp.1.update` (`postp(c') ⊆
    earliest ∪ (ηₚ(c) ∖ ue)`), that `earliest ⊆ πₐ` at the head, and `isAnti.1.predict`
    (`πₐ(c) ∖ ue ⊆ πₐ(c')`). -/
theorem postpSubAnti_step {P : Program} (S : LcmSpec P) {c c' : Config} (hstep : Step P c c')
    (hpa : Assignments.Subset (S.ηₚ c.node) (S.πₐ c.node)) :
    Assignments.Subset (S.ηₚ c'.node) (S.πₐ c'.node) := by
  intro e he
  have hup := S.isPostp.update c c' hstep e he
  rw [Assignments.mem_union] at hup
  rcases hup with hearl | hdiff
  · unfold earliest at hearl
    rw [Assignments.mem_inter, Assignments.mem_inter] at hearl
    exact hearl.1.1
  · rw [Assignments.mem_sdiff] at hdiff
    exact S.isAnti.predict c c' hstep e
      (by rw [Assignments.mem_sdiff]; exact ⟨hpa e hdiff.1, hdiff.2⟩)

/-- `postp(entry) ⊆ anti(entry)` — the base of the threaded invariant (`postp` seed is `∅`). -/
theorem postpSubAnti_entry {P : Program} (S : LcmSpec P) :
    Assignments.Subset (S.ηₚ P.entry) (S.πₐ P.entry) := by
  intro e he
  have := S.isPostp.seed e he
  simp only [entrySeed, Assignments.empty] at this
  exact absurd this Std.HashSet.not_mem_empty

/-! ## The control slot fetches `ctrlCmd`

After the `insChain`, the next slot (`blockOff i + |insertBefore i|`) holds the floated, rewritten control
instruction — the bridge from `insBlock_exec`'s end to the control step in `match_step`. -/

theorem ctrl_slot_fetch {P : Program} (S : LcmSpec P) {i : Node} (hi : i < P.size) :
    (transform P S).fetch (blockOff P S i + (insertBefore P S i).toList.length)
      = some (ctrlCmd P S i) := by
  have hkb : (insertBefore P S i).toList.length < (block P S i).length := by
    rw [block_length]; unfold blockLen; omega
  rw [transform_fetch hi hkb]
  simp only [block]
  rw [List.getElem?_append_right (le_of_eq insChain_length), insChain_length, Nat.sub_self]
  rfl

/-! ## `ue ⊆ πₐ` via greatest-augmentation

`πₐ ∪ ue` is a valid `Anticipated`, so the **greatest** `πₐ` (`isAnti.2`) absorbs it: `ue ⊆ πₐ`. A sub-lemma
the `earliest`-after-kill argument needs. (Contrast: the naive `πᵤ ⊆ πₐ` is **false** — at a fork, an
expression demanded on one branch is `πᵤ` but not `πₐ` — so coverage cannot rest on `πᵤ ⊆ πₐ`.) -/

theorem allExprs_foldl_mono (l : List Cmd) (acc : Assignments) {e : Expr} (h : e ∈ acc) :
    e ∈ l.foldl (fun acc instr => match instr with
          | .assign _ e' _ => if isNumbered e' then acc.insert e' else acc
          | _ => acc) acc := by
  induction l generalizing acc with
  | nil => exact h
  | cons i rest ih =>
      rw [List.foldl_cons]
      refine ih _ ?_
      cases i with
      | assign x e' next =>
          by_cases hn : isNumbered e' = true
          · simp only [hn, if_true]; rw [Std.HashSet.mem_insert]; exact Or.inr h
          · simp only [Bool.not_eq_true] at hn; simpa [hn] using h
      | ifz x z nz => simpa using h
      | noop nx => simpa using h
      | halt => simpa using h

theorem ue_mem_allExprs {P : Program} {n : Node} {e : Expr} (he : e ∈ ue P n) : e ∈ allExprs P := by
  obtain ⟨x, next, hf, _⟩ := mem_ue he
  have hlt : n < P.size := (Array.getElem?_eq_some_iff.mp (show P.code[n]? = some _ from hf)).1
  exact mem_allExprs_range.mpr ⟨n, List.mem_range.mpr hlt, he⟩

theorem ue_sub_anti {P : Program} (S : LcmSpec P) (hS : Extremal S) (n : Node) : Assignments.Subset (ue P n) (S.πₐ n) := by
  have hvalid : Anticipated P (fun m => Assignments.union (S.πₐ m) (ue P m)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c c' hstep e he
      rw [Assignments.mem_sdiff, Assignments.mem_union] at he
      have hanti : e ∈ S.πₐ c.node := he.1.resolve_right he.2
      exact Assignments.mem_union.mpr (Or.inl (S.isAnti.predict c c' hstep e
        (Assignments.mem_sdiff.mpr ⟨hanti, he.2⟩)))
    · intro m e he
      rw [Assignments.mem_union] at he
      rcases he with h | h
      · exact S.isAnti.check m e h
      · exact Assignments.mem_union.mpr (Or.inl h)
    · intro c hfin e he
      rw [Assignments.mem_union] at he
      rcases he with h | h
      · exact S.isAnti.seed c hfin e h
      · obtain ⟨x, next, hf, _⟩ := mem_ue h
        rw [hfin] at hf; exact absurd hf (by simp)
    · intro m e he
      rw [Assignments.mem_union] at he
      rcases he with h | h
      · exact S.isAnti.within m e h
      · exact ue_mem_allExprs h
  intro e he
  exact hS.πₐ _ hvalid n e (Assignments.mem_union.mpr (Or.inr he))

/-- **A use of a numbered `e` is transparent** (`NoSelfRead`): a node that computes `e` (`e ∈ ue`) does
    not redefine an operand of `e`, so `e ∈ pass`. The structural fact that rules out the "use-and-kill"
    double — and, with `πₐ ⊆ ue ∪ pass`, that `earliest` may read `¬πₐ` on its `¬availableOut` frontier. -/
theorem ue_sub_transp {P : Program} (wn : WellNormalized P) {n : Node} {e : Expr}
    (hue : e ∈ ue P n) : e ∈ pass P n := by
  have hall : e ∈ allExprs P := ue_mem_allExprs hue
  unfold ue at hue
  cases hf : P.fetch n with
  | none => rw [hf] at hue; exact absurd hue Std.HashSet.not_mem_empty
  | some instr =>
      cases instr with
      | assign x e0 next =>
          rw [hf] at hue
          by_cases hn : isNumbered e0
          · simp only [hn, if_true] at hue
            have he : e = e0 := (Assignments.mem_singleton.1 hue)
            subst he
            have hnsr : exprReadsVar e x = false := wn.noSelfRead hf hn
            unfold pass; rw [Assignments.mem_filter']
            exact ⟨hall, by simp [transpB, hf, instrDefVar, hnsr]⟩
          · simp only [hn] at hue; exact absurd hue Std.HashSet.not_mem_empty
      | ifz x z nz => rw [hf] at hue; exact absurd hue Std.HashSet.not_mem_empty
      | noop next => rw [hf] at hue; exact absurd hue Std.HashSet.not_mem_empty
      | halt => rw [hf] at hue; exact absurd hue Std.HashSet.not_mem_empty

/-- **Killed ⇒ not-anticipated-in** (`NoSelfRead`): `πₐ ⊆ ue ∪ pass` and `ue ⊆ pass`, so `e ∉ pass n ⇒
    e ∉ πₐ n`. This is what lets the new `earliest` (third factor `¬πₐ`) subsume the old `¬pass` placement. -/
theorem notAnti_of_notPass {P : Program} (S : LcmSpec P) (wn : WellNormalized P) {n : Node} {e : Expr}
    (hkill : e ∉ pass P n) : e ∉ S.πₐ n := by
  intro hpi
  rcases Assignments.mem_union.mp (S.isAnti.check n e hpi) with hue | hpass
  · exact hkill (ue_sub_transp wn hue)
  · exact hkill hpass


end BaseLanguage.Analyses.LCM
