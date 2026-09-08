-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.ExecCount
import BaseLanguage.PDCE.Optimality
/-! # Two-program execution-count optimality (synchronized by original steps)

`execCountOrig` executes `transform P S` under its own semantics but with fuel measured in *original*
steps (one block per unit), so two transformed programs run with the same `ks` are synchronized at
original-node boundaries. `execCountOrig = matCount` folds it to the source-side count; the headline
`transform_execCountOrig_le_any` compares two real compiled programs. -/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-- `m` is the entry of some original node's block — an original-node image. -/
def orig (P : Program) (S : PdceSpec P) (m : Node) : Bool :=
  (List.range P.size).any (fun i => decide (blockOff P S i = m))

/-- Execute `transform P S`, counting `a`, with fuel measured in ORIGINAL steps. `c` = source config
    (the clock), `d` = transformed config (invariant `Match P S c d`). Each unit runs one block of
    `transform P S` via its real `run`; a stop runs the final `matNode` block. -/
def execCountOrig (P : Program) (S : PdceSpec P) (a : Asgn) : Config → Config → Nat → Nat
  | _, _, 0      => 0
  | c, d, ks + 1 =>
      match step1 P c with
      | .next c' =>
          execCount (transform P S) a d (blockFuelTo P S c.node c'.node)
            + execCountOrig P S a c'
                (run (transform P S) d (blockFuelTo P S c.node c'.node)).1 ks
      | _ => execCount (transform P S) a d (matNode P S c.node).length

/-- `matNode`-block count is the `matNode` indicator (final/stopped block). -/
theorem execCount_matNode_block {P : Program} (S : PdceSpec P) (a : Asgn) {c d : Config}
    (hi : c.node < P.size) (hm : Match P S c d) :
    execCount (transform P S) a d (matNode P S c.node).length
      = (if a ∈ matNode P S c.node then 1 else 0) := by
  obtain ⟨hnode, h2, hrec, hindep⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  subst hnode
  have hrec' : ∀ b ∈ matNode P S c.node, eval dσ b.rhs = some (c.store b.lhs) := by
    intro b hb
    obtain ⟨hs, _, hl⟩ := mem_matNode.mp hb
    exact hrec b.lhs b.rhs (by simpa using hs) hl
  obtain ⟨τ1, _, _, _, hsc⟩ := matNode_execF S a hi hrec' hindep
  rw [execCount, hsc, count_filter_eq_nodup matNode_nodup]

/-- **The fold.** The original-fueled execution count of `transform P S` equals the source-side
    materialization count `matCount`. Prefix-general (any `ks`, no `Final`). Requires only node
    validity, threaded via `Match`/`WellFormed`. -/
theorem execCountOrig_eq_matCount {P : Program} (S : PdceSpec P) (wf : WellFormed P) (a : Asgn) :
    ∀ (ks : Nat) {c d : Config}, c.node < P.size → Match P S c d →
      execCountOrig P S a c d ks = matCount P S a c ks := by
  intro ks
  induction ks with
  | zero => intro c d _ _; rfl
  | succ k ih =>
      intro c d hi hm
      cases hstep : step1 P c with
      | next c' =>
          have hStep : Step P c c' := step1_next_iff.mp hstep
          obtain ⟨τF, hrun, hmatch, hcount⟩ := block_execCount S wf a hm hStep
          have hi' : c'.node < P.size := step_in_range wf hStep
          rw [matCount_next hstep]
          simp only [execCountOrig, hstep, hrun, hcount]
          rw [ih hi' hmatch]
          omega
      | halt =>
          simp only [execCountOrig, matCount, hstep]
          exact execCount_matNode_block S a hi hm
      | fault =>
          simp only [execCountOrig, matCount, hstep]
          exact execCount_matNode_block S a hi hm
      | stuck =>
          simp only [execCountOrig, matCount, hstep]
          exact execCount_matNode_block S a hi hm

/-- The per-step ballot inequality (★★), reflected to `Bool` and discharged by kernel `decide` — the
    two-sided potential's discharge over the 11 membership atoms, with the validity/extremality
    implications as hypotheses. Kernel `decide` (no `native_decide`), so it stays axiom-clean. -/
private theorem key_ballot :
    ∀ (skc skc' skpc skpc' lvc lvc' lvpc lvpc' bo pa bl : Bool),
      (skpc → skc) → (skpc' → skc') → (lvc → lvpc) → (lvc' → lvpc') →
      (skc' → (bo || (skc && pa))) → (skpc' → (bo || (skpc && pa))) →
      (pa && lvc' → lvc) → (pa && lvpc' → lvpc) → (bl → !pa) →
      (skc && bl && lvc).toNat + ((bo || (skc && pa)) && !skc' && lvc').toNat
        + (skpc && lvpc).toNat + (skc' && lvpc').toNat
      ≤ (skpc && bl && lvpc).toNat + ((bo || (skpc && pa)) && !skpc' && lvpc').toNat
        + (skc && lvpc).toNat + (skpc' && lvpc').toNat := by decide

/-- **The prefix-majorization induction (two-sided potential).** Carries the two-program comparison over
    an arbitrary start `c` with a *mixed* pending potential — `S'`'s in-flight-live on the left, `S`'s on
    the right (both gated by `S'.π`). The potential vanishes at `entry` (`sinkSeed = ∅`) and closes
    per-step from `sink_maximal` (`S'.ηK ⊆ S.ηK`) + `live_minimal` (`S.π ⊆ S'.π`) via the
    reflected ballot lemma `key_ballot`. -/
theorem matCount_le_any_aux {P : Program} (S S' : PdceSpec P) (hS : Extremal S)
    (hkq : S'.keep = S.keep) (a : Asgn) (hk : S.keep a = true) :
    ∀ (fuel : Nat) (c : Config),
      matCount P S a c fuel + (if a ∈ S'.ηK c.node ∧ a.lhs ∈ S'.π c.node then 1 else 0)
        ≤ matCount P S' a c fuel + (if a ∈ S.ηK c.node ∧ a.lhs ∈ S'.π c.node then 1 else 0) := by
  intro fuel
  induction fuel with
  | zero =>
      intro c
      have hE : a ∈ S'.ηK c.node → a ∈ S.ηK c.node := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c.node a h, hkq ▸ (mem_ηK.mp h).2⟩
      simp only [matCount]
      by_cases h1 : a ∈ S'.ηK c.node <;> by_cases h2 : a ∈ S.ηK c.node <;>
        by_cases h3 : a.lhs ∈ S'.π c.node <;> simp_all
  | succ f ih =>
      intro c
      cases hs : step1 P c with
      | next c' =>
          have hStep : Step P c c' := step1_next_iff.mp hs
          have hsE  : a ∈ S'.ηK c.node  → a ∈ S.ηK c.node  := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c.node  a h, hkq ▸ (mem_ηK.mp h).2⟩
          have hsE' : a ∈ S'.ηK c'.node → a ∈ S.ηK c'.node := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c'.node a h, hkq ▸ (mem_ηK.mp h).2⟩
          have hlE  : a.lhs ∈ S.π c.node  → a.lhs ∈ S'.π c.node  := fun h => hS.π S'.π S'.isLive c.node  a.lhs h
          have hlE' : a.lhs ∈ S.π c'.node → a.lhs ∈ S'.π c'.node := fun h => hS.π S'.π S'.isLive c'.node a.lhs h
          have hUS  : a ∈ S.ηK c'.node  → a ∈ born P c.node ∨ (a ∈ S.ηK c.node  ∧ a ∈ pass P c.node) := by
            intro h
            have hk := (mem_ηK.mp h).2
            have hu := S.isSink.update  c c' hStep a (ηK_sub S _ a h)
            rw [Assignments.mem_union, Assignments.mem_inter] at hu
            exact hu.imp id (fun hh => ⟨mem_ηK.mpr ⟨hh.1, hk⟩, hh.2⟩)
          have hUS' : a ∈ S'.ηK c'.node → a ∈ born P c.node ∨ (a ∈ S'.ηK c.node ∧ a ∈ pass P c.node) := by
            intro h
            have hk := (mem_ηK.mp h).2
            have hu := S'.isSink.update c c' hStep a (ηK_sub S' _ a h)
            rw [Assignments.mem_union, Assignments.mem_inter] at hu
            exact hu.imp id (fun hh => ⟨mem_ηK.mpr ⟨hh.1, hk⟩, hh.2⟩)
          have hCS  : a ∈ pass P c.node → a.lhs ∈ S.π c'.node  → a.lhs ∈ S.π c.node  :=
            fun hp hl => pass_live_carry S  hStep hp hl
          have hCS' : a ∈ pass P c.node → a.lhs ∈ S'.π c'.node → a.lhs ∈ S'.π c.node :=
            fun hp hl => pass_live_carry S' hStep hp hl
          have hnh : P.fetch c.node ≠ some .halt := by
            intro hh; have h' : step1 P c = .halt := by unfold step1; rw [hh]
            rw [h'] at hs; simp at hs
          have hbeq : blockedSet P c.node = Assignments.sdiff (allAsgns P) (pass P c.node) := by
            unfold blockedSet
            cases hf : P.fetch c.node with
            | none => rfl
            | some i => cases i with
              | halt => exact absurd hf hnh
              | assign x e nx => rfl
              | ifz x z nz => rfl
              | noop nx => rfl
          have hblkpass : a ∈ blockedSet P c.node → a ∉ pass P c.node := by
            rw [hbeq]; intro h; exact (Assignments.mem_sdiff.mp h).2
          rw [matCount_next hs, matCount_next hs]
          have IH := ih c'
          have eMNS  : a ∈ matNode P S  c.node ↔ a ∈ S.ηK c.node  ∧ a ∈ blockedSet P c.node ∧ a.lhs ∈ S.π c.node  := mem_matNode
          have eMNS' : a ∈ matNode P S' c.node ↔ a ∈ S'.ηK c.node ∧ a ∈ blockedSet P c.node ∧ a.lhs ∈ S'.π c.node := mem_matNode
          have eMES  : a ∈ matEdge P S  c.node c'.node ↔ (a ∈ born P c.node ∨ (a ∈ S.ηK c.node  ∧ a ∈ pass P c.node)) ∧ a ∉ S.ηK c'.node  ∧ a.lhs ∈ S.π c'.node  := by
            rw [mem_matEdge, mem_delayedExit]
            exact ⟨fun h => ⟨h.1, h.2.1, keep_live_of_matEdge hk h.2.2⟩,
                   fun h => ⟨h.1, h.2.1, Or.inl h.2.2⟩⟩
          have hk' : S'.keep a = true := by rw [hkq]; exact hk
          have eMES' : a ∈ matEdge P S' c.node c'.node ↔ (a ∈ born P c.node ∨ (a ∈ S'.ηK c.node ∧ a ∈ pass P c.node)) ∧ a ∉ S'.ηK c'.node ∧ a.lhs ∈ S'.π c'.node := by
            rw [mem_matEdge, mem_delayedExit]
            exact ⟨fun h => ⟨h.1, h.2.1, keep_live_of_matEdge hk' h.2.2⟩,
                   fun h => ⟨h.1, h.2.1, Or.inl h.2.2⟩⟩
          have hd : ∀ (Q : Prop) [Decidable Q], (if Q then (1:Nat) else 0) = (decide Q).toNat := by
            intro Q _; by_cases hQ : Q <;> simp [hQ]
          have K := key_ballot (decide (a ∈ S.ηK c.node)) (decide (a ∈ S.ηK c'.node))
            (decide (a ∈ S'.ηK c.node)) (decide (a ∈ S'.ηK c'.node))
            (decide (a.lhs ∈ S.π c.node)) (decide (a.lhs ∈ S.π c'.node))
            (decide (a.lhs ∈ S'.π c.node)) (decide (a.lhs ∈ S'.π c'.node))
            (decide (a ∈ born P c.node)) (decide (a ∈ pass P c.node)) (decide (a ∈ blockedSet P c.node))
            (by simpa using hsE) (by simpa using hsE') (by simpa using hlE) (by simpa using hlE')
            (by simpa using hUS) (by simpa using hUS') (by simpa using hCS) (by simpa using hCS')
            (by simpa using hblkpass)
          simp only [eMNS, eMNS', eMES, eMES', hd, Bool.decide_and, Bool.decide_or,
            decide_not, Bool.and_assoc] at K IH ⊢
          omega
      | halt =>
          have hsE : a ∈ S'.ηK c.node → a ∈ S.ηK c.node := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c.node a h, hkq ▸ (mem_ηK.mp h).2⟩
          have hlE : a.lhs ∈ S.π c.node → a.lhs ∈ S'.π c.node := fun h => hS.π S'.π S'.isLive c.node a.lhs h
          simp only [matCount, hs, mem_matNode]
          by_cases h1 : a ∈ S.ηK c.node <;> by_cases h2 : a ∈ S'.ηK c.node <;>
          by_cases h3 : a.lhs ∈ S.π c.node <;> by_cases h4 : a.lhs ∈ S'.π c.node <;>
          by_cases h5 : a ∈ blockedSet P c.node <;> simp_all <;> omega
      | fault =>
          have hsE : a ∈ S'.ηK c.node → a ∈ S.ηK c.node := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c.node a h, hkq ▸ (mem_ηK.mp h).2⟩
          have hlE : a.lhs ∈ S.π c.node → a.lhs ∈ S'.π c.node := fun h => hS.π S'.π S'.isLive c.node a.lhs h
          simp only [matCount, hs, mem_matNode]
          by_cases h1 : a ∈ S.ηK c.node <;> by_cases h2 : a ∈ S'.ηK c.node <;>
          by_cases h3 : a.lhs ∈ S.π c.node <;> by_cases h4 : a.lhs ∈ S'.π c.node <;>
          by_cases h5 : a ∈ blockedSet P c.node <;> simp_all <;> omega
      | stuck =>
          have hsE : a ∈ S'.ηK c.node → a ∈ S.ηK c.node := fun h => mem_ηK.mpr ⟨hS.η S'.ηK (isSink_ηK S') c.node a h, hkq ▸ (mem_ηK.mp h).2⟩
          have hlE : a.lhs ∈ S.π c.node → a.lhs ∈ S'.π c.node := fun h => hS.π S'.π S'.isLive c.node a.lhs h
          simp only [matCount, hs, mem_matNode]
          by_cases h1 : a ∈ S.ηK c.node <;> by_cases h2 : a ∈ S'.ηK c.node <;>
          by_cases h3 : a.lhs ∈ S.π c.node <;> by_cases h4 : a.lhs ∈ S'.π c.node <;>
          by_cases h5 : a ∈ blockedSet P c.node <;> simp_all <;> omega

theorem matCount_le_any {P : Program} (S S' : PdceSpec P) (hS : Extremal S)
    (hkq : S'.keep = S.keep) (a : Asgn) (hk : S.keep a = true) (σ : Store) (ks : Nat) :
    matCount P S a ⟨P.entry, σ⟩ ks ≤ matCount P S' a ⟨P.entry, σ⟩ ks := by
  have h := matCount_le_any_aux S S' hS hkq a hk ks ⟨P.entry, σ⟩
  have hS0  : a ∉ S.ηK  P.entry := by
    intro hmem; have := S.isSink.seed  a (ηK_sub S _ a hmem); simp [sinkSeed, Assignments.empty] at this
  have hS0' : a ∉ S'.ηK P.entry := by
    intro hmem; have := S'.isSink.seed a (ηK_sub S' _ a hmem); simp [sinkSeed, Assignments.empty] at this
  simp only [show (⟨P.entry, σ⟩ : Config).node = P.entry from rfl] at h
  simp only [hS0, hS0', false_and, if_false] at h
  simpa using h

/-- **Two-program execution-count optimality, all prefixes.** Running BOTH compiled programs for the
    same `ks` original steps, the extremal transform executes `a` no more often than the competitor. -/
theorem transform_execCountOrig_le_any {P : Program} (S S' : PdceSpec P) (hS : Extremal S)
    (wf : WellFormed P) (hkq : S'.keep = S.keep) (a : Asgn) (hk : S.keep a = true)
    (σ : Store) (ks : Nat) :
    execCountOrig P S  a ⟨P.entry, σ⟩ ⟨blockOff P S  P.entry, σ⟩ ks
      ≤ execCountOrig P S' a ⟨P.entry, σ⟩ ⟨blockOff P S' P.entry, σ⟩ ks := by
  rw [execCountOrig_eq_matCount S  wf a ks wf.entry_lt (match_init S  σ),
      execCountOrig_eq_matCount S' wf a ks wf.entry_lt (match_init S' σ)]
  exact matCount_le_any S S' hS hkq a hk σ ks

end BaseLanguage.Analyses.PDCE
