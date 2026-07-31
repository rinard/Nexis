-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Transform

/-!
# `LCM.Layout` — structural facts about the `transform` (entry + exit placement)

`entry`/`obs`/`size`, the block-length identity, the fetch-at-offset characterization, and
well-formedness, proved directly from `S : LcmSpec P`. The block/offset layout makes `fetch` a function
of the offset table — the simulation in `Correctness/*` relies on it.

An LCM block is `insChain ++ (ctrlCmd :: exitChain)` — entry inserts, the rewritten control, then (for an
`assign`) the **exit** inserts that realize KRS edge placement by appending to a 1-successor source. So
`blockLen i = |insertBefore i| + 1 + |insertAfter i|` (the last summand `0` for non-`assign`). Mirrors PDCE's
`matNode`/`matEdge` layout, but the edge chain attaches only to `assign` nodes.
-/

namespace BaseLanguage.Analyses.LCM
open Tac Normalize Semantics Std

@[simp] theorem transform_entry {P : Program} (S : LcmSpec P) :
    (transform P S).entry = blockOff P S P.entry := rfl

@[simp] theorem transform_obs {P : Program} (S : LcmSpec P) :
    (transform P S).obs = P.obs := rfl

/-- A block has exactly `blockLen` instructions (so the prefix-sum offsets are consistent). -/
theorem block_length {P : Program} (S : LcmSpec P) (i : Node) :
    (block P S i).length = blockLen P S i := by
  unfold block blockLen insChain exitChain
  cases P.fetch i with
  | none => simp
  | some instr =>
      cases instr <;>
        simp only [List.length_append, List.length_map, List.length_zipIdx, List.length_cons,
          List.length_nil] <;> omega

/-- The transform's size is the total of all block lengths, i.e. `blockOff … P.size`. -/
theorem transform_size {P : Program} (S : LcmSpec P) :
    (transform P S).size = blockOff P S P.size := by
  show ((List.range P.size).flatMap (block P S)).toArray.size = _
  rw [List.size_toArray, List.length_flatMap]
  simp only [block_length]
  rfl

/-! ### Offset arithmetic -/

theorem blockOff_succ {P : Program} {S : LcmSpec P} {i : Node} :
    blockOff P S (i + 1) = blockOff P S i + blockLen P S i := by
  unfold blockOff; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem blockLen_pos {P : Program} {S : LcmSpec P} {i : Node} : 0 < blockLen P S i := by
  unfold blockLen; omega

theorem blockOff_mono {P : Program} {S : LcmSpec P} {a b : Nat} (h : a ≤ b) :
    blockOff P S a ≤ blockOff P S b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [blockOff_succ]; omega

theorem blockOff_lt {P : Program} {S : LcmSpec P} {a b : Nat} (h : a < b) :
    blockOff P S a < blockOff P S b := by
  have h1 : blockOff P S a < blockOff P S (a + 1) := by
    rw [blockOff_succ]; have := @blockLen_pos P S a; omega
  exact Nat.lt_of_lt_of_le h1 (blockOff_mono h)

/-- A block offset is below the total size when its node is in range. -/
theorem blockOff_lt_size {P : Program} {S : LcmSpec P} {i : Node} (h : i < P.size) :
    blockOff P S i < (transform P S).size := by
  rw [transform_size]; exact blockOff_lt h

/-! ### Fetch-at-offset characterization -/

/-- The flat layout of the first `i` blocks has length exactly `blockOff i`. -/
theorem flatMap_prefix_length {P : Program} {S : LcmSpec P} {i : Nat} :
    ((List.range i).flatMap (block P S)).length = blockOff P S i := by
  rw [List.length_flatMap]
  unfold blockOff
  congr 1
  apply List.map_congr_left
  intro k _; exact block_length S k

/-- **Fetch at a block offset.** The instruction at absolute index `blockOff i + j` is the `j`-th
    instruction of node `i`'s block. This makes `fetch` a function of the offset table. -/
theorem transform_fetch {P : Program} {S : LcmSpec P} {i : Node} {j : Nat}
    (hi : i < P.size) (hj : j < (block P S i).length) :
    (transform P S).fetch (blockOff P S i + j) = (block P S i)[j]? := by
  obtain ⟨k, hk⟩ := Nat.le.dest hi  -- hk : i + 1 + k = P.size
  have hrange : List.range P.size
      = List.range i ++ [i] ++ (List.range k).map ((i + 1) + ·) := by
    rw [← hk, List.range_add, List.range_succ]
  have hflat : (List.range P.size).flatMap (block P S)
      = (List.range i).flatMap (block P S)
          ++ (block P S i ++ ((List.range k).map ((i + 1) + ·)).flatMap (block P S)) := by
    rw [hrange, List.flatMap_append, List.flatMap_append]
    simp [List.flatMap_cons]
  show (transform P S).code[blockOff P S i + j]? = _
  rw [show (transform P S).code = ((List.range P.size).flatMap (block P S)).toArray from rfl]
  rw [List.getElem?_toArray, hflat]
  rw [List.getElem?_append_right (by rw [flatMap_prefix_length]; omega),
      flatMap_prefix_length, Nat.add_sub_cancel_left,
      List.getElem?_append_left hj]

/-! ### Per-block successor bound -/

/-- Every successor label of `i` is `< lim`. -/
def InRange (lim : Nat) (i : Cmd) : Prop := ∀ s ∈ i.succs, s < lim

@[simp] theorem InRange_assign {lim x e n} : InRange lim (.assign x e n) ↔ n < lim := by
  simp [InRange, Cmd.succs]
@[simp] theorem InRange_noop {lim n} : InRange lim (.noop n) ↔ n < lim := by simp [InRange, Cmd.succs]
@[simp] theorem InRange_ifz {lim x z nz} : InRange lim (.ifz x z nz) ↔ z < lim ∧ nz < lim := by
  simp [InRange, Cmd.succs]
@[simp] theorem InRange_halt {lim} : InRange lim Cmd.halt := by simp [InRange, Cmd.succs]

/-- Every instruction of an insert chain has its (in-block) successor in range. -/
theorem insChain_inrange {P : Program} {m : List Expr} {s0 lim : Nat} (hb : s0 + m.length < lim) :
    ∀ instr ∈ insChain P m s0, InRange lim instr := by
  intro instr hi
  unfold insChain at hi; rw [List.mem_map] at hi
  obtain ⟨⟨a, kk⟩, hk, rfl⟩ := hi
  obtain ⟨_, hk2, _⟩ := List.mem_zipIdx hk
  simp only [InRange_assign]
  exact Nat.lt_of_le_of_lt (show s0 + kk + 1 ≤ s0 + m.length by omega) hb

/-- Every instruction of an exit chain has its (in-block or target) successor in range. -/
theorem exitChain_inrange {P : Program} {m : List Expr} {start target lim : Nat}
    (htgt : target < lim) (hb : start + m.length ≤ lim) :
    ∀ instr ∈ exitChain P m start target, InRange lim instr := by
  intro instr hi
  unfold exitChain at hi; rw [List.mem_map] at hi
  obtain ⟨⟨a, kk⟩, hk, rfl⟩ := hi
  obtain ⟨_, hk2, _⟩ := List.mem_zipIdx hk
  simp only [InRange_assign]
  split
  · exact htgt
  · rename_i hbeq
    have hne : kk + 1 ≠ m.length := by simpa using hbeq
    exact Nat.lt_of_lt_of_le (show start + kk + 1 < start + m.length by omega) hb

/-- An exit chain length is positive when its `isEmpty` test is not `true`. -/
theorem length_pos_of_isEmpty_false {m : List Expr} (h : ¬ m.isEmpty = true) : 0 < m.length := by
  cases m with
  | nil => simp at h
  | cons a rest => simp

/-- Every instruction in node `i`'s block has its successors in range. -/
theorem block_inrange {P : Program} {S : LcmSpec P} (wf : WellFormed P) {i : Node} (hi : i < P.size) :
    ∀ instr ∈ block P S i, InRange (transform P S).size instr := by
  have hsz : blockOff P S i + blockLen P S i ≤ (transform P S).size := by
    rw [transform_size, ← blockOff_succ]; exact blockOff_mono hi
  have hbl1 : (insertBefore P S i).toList.length + 1 ≤ blockLen P S i := by unfold blockLen; omega
  have hins : blockOff P S i + (insertBefore P S i).toList.length < (transform P S).size := by omega
  intro instr hmem
  simp only [block, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hmc | hctrl | hexit
  · exact insChain_inrange hins instr hmc
  · -- the control instruction
    subst hctrl
    cases hfi : P.fetch i with
    | none => simp only [ctrlCmd, hfi]; exact InRange_halt
    | some instr0 =>
      cases instr0 with
      | halt => simp only [ctrlCmd, hfi]; exact InRange_halt
      | noop next =>
          have hnext : blockOff P S next < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i
              = (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length := by
            simp only [blockLen, hfi]
          simp only [ctrlCmd, hfi, InRange_noop]
          split
          · exact hnext
          · rename_i he
            have hpos := length_pos_of_isEmpty_false he
            have hlt : blockOff P S i + (insertBefore P S i).toList.length + 1
                < blockOff P S i + blockLen P S i := by rw [hbl]; omega
            exact Nat.lt_of_lt_of_le hlt hsz
      | ifz x z nz =>
          have hz : blockOff P S z < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hnz : blockOff P S nz < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i = (insertBefore P S i).toList.length + 1
              + ((insertEdge P S i z).toList.length + (insertEdge P S i nz).toList.length) := by
            simp only [blockLen, hfi]
          simp only [ctrlCmd, hfi, InRange_ifz]
          refine ⟨?_, ?_⟩
          · split
            · exact hz
            · rename_i he
              have := length_pos_of_isEmpty_false he
              have hlt : blockOff P S i + (insertBefore P S i).toList.length + 1
                  < blockOff P S i + blockLen P S i := by rw [hbl]; omega
              exact Nat.lt_of_lt_of_le hlt hsz
          · split
            · exact hnz
            · rename_i he
              have := length_pos_of_isEmpty_false he
              have hlt : blockOff P S i + (insertBefore P S i).toList.length + 1
                    + (insertEdge P S i z).toList.length
                  < blockOff P S i + blockLen P S i := by rw [hbl]; omega
              exact Nat.lt_of_lt_of_le hlt hsz
      | assign x e next =>
          have hnext : blockOff P S next < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i
              = (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length := by
            simp only [blockLen, hfi]
          simp only [ctrlCmd, hfi]
          split <;> simp only [InRange_assign] <;> split <;>
            first
            | exact hnext
            | · rename_i he
                have hpos := length_pos_of_isEmpty_false he
                have hlt : blockOff P S i + (insertBefore P S i).toList.length + 1
                    < blockOff P S i + blockLen P S i := by rw [hbl]; omega
                exact Nat.lt_of_lt_of_le hlt hsz
  · -- the exit chain (only `assign` has one)
    revert hexit
    cases hfi : P.fetch i with
    | none => intro h; simp at h
    | some instr0 =>
      cases instr0 with
      | halt => intro h; simp at h
      | noop next =>
          intro hexit
          have hnext : blockOff P S next < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i = (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length := by
            simp only [blockLen, hfi]
          have hb : blockOff P S i + (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length
              ≤ (transform P S).size := by omega
          exact exitChain_inrange hnext hb instr (by simpa [hfi] using hexit)
      | ifz x z nz =>
          intro h
          rw [List.mem_append] at h
          have hz : blockOff P S z < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hnz : blockOff P S nz < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i = (insertBefore P S i).toList.length + 1
              + ((insertEdge P S i z).toList.length + (insertEdge P S i nz).toList.length) := by
            simp only [blockLen, hfi]
          rcases h with hzc | hnc
          · exact exitChain_inrange hz (by omega) instr hzc
          · exact exitChain_inrange hnz (by omega) instr hnc
      | assign x e next =>
          intro hexit
          have hnext : blockOff P S next < (transform P S).size :=
            blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i = (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length := by
            simp only [blockLen, hfi]
          have hb : blockOff P S i + (insertBefore P S i).toList.length + 1 + (insertAfter P S i).toList.length
              ≤ (transform P S).size := by omega
          exact exitChain_inrange hnext hb instr (by simpa [hfi] using hexit)

/-- **Well-formedness**, on the offset layout. -/
theorem transform_wellFormed {P : Program} (S : LcmSpec P) (wf : WellFormed P) :
    WellFormed (transform P S) where
  entry_lt := blockOff_lt_size wf.entry_lt
  succ_lt := by
    intro n instr s hf hs
    have hmem : instr ∈ (transform P S).code := Array.mem_of_getElem? hf
    show s < (transform P S).size
    have : instr ∈ (List.range P.size).flatMap (block P S) := by
      rwa [show (transform P S).code = ((List.range P.size).flatMap (block P S)).toArray from rfl,
           List.mem_toArray] at hmem
    rw [List.mem_flatMap] at this
    obtain ⟨i, hi, hib⟩ := this
    rw [List.mem_range] at hi
    exact block_inrange wf hi instr hib s hs

end BaseLanguage.Analyses.LCM
