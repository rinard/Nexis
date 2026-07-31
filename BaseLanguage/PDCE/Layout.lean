-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Transform

/-!
# `PDCE.Layout` — structural facts about the two-pass `transform`

`entry`/`obs`/`size`, the block-length identity, and well-formedness (`transform_wellFormed`), proved
directly from `S : PdceSpec P`. The block/offset layout makes `fetch` a function of the offset table.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

@[simp] theorem transform_entry {P : Program} (S : PdceSpec P) :
    (transform P S).entry = blockOff P S P.entry := rfl

@[simp] theorem transform_obs {P : Program} (S : PdceSpec P) :
    (transform P S).obs = P.obs := rfl

/-- A block has exactly `blockLen` instructions (so the prefix-sum offsets are consistent). -/
theorem block_length {P : Program} (S : PdceSpec P) (i : Node) :
    (block P S i).length = blockLen P S i := by
  unfold block blockLen matChain edgeChain
  cases P.fetch i with
  | none => simp
  | some instr =>
      cases instr with
      | assign x e next => simp; omega
      | noop next => simp; omega
      | ifz x z nz => simp; omega
      | halt => simp

/-- The transform's size is the total of all block lengths, i.e. `blockOff … P.size`. -/
theorem transform_size {P : Program} (S : PdceSpec P) :
    (transform P S).size = blockOff P S P.size := by
  show ((List.range P.size).flatMap (block P S)).toArray.size = _
  rw [List.size_toArray, List.length_flatMap]
  simp only [block_length]
  rfl

/-! ### Offset arithmetic -/

theorem blockOff_succ {P : Program} {S : PdceSpec P} {i : Node} :
    blockOff P S (i + 1) = blockOff P S i + blockLen P S i := by
  unfold blockOff; rw [List.range_succ, List.map_append, List.sum_append]; simp

theorem blockLen_pos {P : Program} {S : PdceSpec P} {i : Node} : 0 < blockLen P S i := by
  unfold blockLen; omega

theorem blockOff_mono {P : Program} {S : PdceSpec P} {a b : Nat} (h : a ≤ b) :
    blockOff P S a ≤ blockOff P S b := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [blockOff_succ]; omega

theorem blockOff_lt {P : Program} {S : PdceSpec P} {a b : Nat} (h : a < b) :
    blockOff P S a < blockOff P S b := by
  have h1 : blockOff P S a < blockOff P S (a + 1) := by
    rw [blockOff_succ]; have := @blockLen_pos P S a; omega
  exact Nat.lt_of_lt_of_le h1 (blockOff_mono h)

/-- **The node correspondence is injective.** `blockOff P S : Node → Node` maps each *original* node to the
    head of its block in the transformed program; distinct original nodes get distinct transformed nodes. So
    every original node has a well-defined corresponding transformed node (its block), and the materialized
    assignments occupy the *other* slots of the block — the ones this map never hits. -/
theorem blockOff_inj {P : Program} {S : PdceSpec P} {a b : Node}
    (h : blockOff P S a = blockOff P S b) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · exact absurd h (Nat.ne_of_lt (blockOff_lt hlt))
  · exact heq
  · exact absurd h.symm (Nat.ne_of_lt (blockOff_lt hgt))

/-- A block offset is below the total size when its node is in range. -/
theorem blockOff_lt_size {P : Program} {S : PdceSpec P} {i : Node} (h : i < P.size) :
    blockOff P S i < (transform P S).size := by
  rw [transform_size]; exact blockOff_lt h

/-! ### Fetch-at-offset characterization -/

/-- The flat layout of the first `i` blocks has length exactly `blockOff i`. -/
theorem flatMap_prefix_length {P : Program} {S : PdceSpec P} {i : Nat} :
    ((List.range i).flatMap (block P S)).length = blockOff P S i := by
  rw [List.length_flatMap]
  unfold blockOff
  congr 1
  apply List.map_congr_left
  intro k _; exact block_length S k

/-- **Fetch at a block offset.** The instruction at absolute index `blockOff i + j` is the `j`-th
    instruction of node `i`'s block. This makes `fetch` a function of the offset table. -/
theorem transform_fetch {P : Program} {S : PdceSpec P} {i : Node} {j : Nat}
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

theorem matChain_inrange {m : List Asgn} {s0 lim : Nat} (hb : s0 + m.length < lim) :
    ∀ instr ∈ matChain m s0, InRange lim instr := by
  intro instr hi
  unfold matChain at hi; rw [List.mem_map] at hi
  obtain ⟨⟨a, k⟩, hk, rfl⟩ := hi
  obtain ⟨_, hk2, _⟩ := List.mem_zipIdx hk
  simp only [InRange_assign]
  exact Nat.lt_of_le_of_lt (show s0 + k + 1 ≤ s0 + m.length by omega) hb

theorem edgeChain_inrange {e : List Asgn} {start target lim : Nat}
    (htgt : target < lim) (hb : start + e.length ≤ lim) :
    ∀ instr ∈ edgeChain e start target, InRange lim instr := by
  intro instr hi
  unfold edgeChain at hi; rw [List.mem_map] at hi
  obtain ⟨⟨a, k⟩, hk, rfl⟩ := hi
  obtain ⟨_, hk2, _⟩ := List.mem_zipIdx hk
  simp only [InRange_assign]
  split
  · exact htgt
  · rename_i hbeq
    have hne : k + 1 ≠ e.length := by simpa using hbeq
    exact Nat.lt_of_lt_of_le (show start + k + 1 < start + e.length by omega) hb

/-- An edge length is positive when its `isEmpty` test is not `true`. -/
theorem length_pos_of_isEmpty_false {e : List Asgn} (h : ¬ e.isEmpty = true) : 0 < e.length := by
  cases e with
  | nil => simp at h
  | cons a rest => simp

/-- Every instruction in node `i`'s block has its successors in range. -/
theorem block_inrange {P : Program} {S : PdceSpec P} (wf : WellFormed P) {i : Node} (hi : i < P.size) :
    ∀ instr ∈ block P S i, InRange (transform P S).size instr := by
  have hsz : blockOff P S i + blockLen P S i ≤ (transform P S).size := by
    rw [transform_size, ← blockOff_succ]; exact blockOff_mono hi
  have hmat : blockOff P S i + (matNode P S i).length < (transform P S).size := by
    have h := hsz; simp only [blockLen] at h; omega
  intro instr hmem
  simp only [block, List.mem_append] at hmem
  rcases hmem with hmc | hctrl
  · exact matChain_inrange hmat instr hmc
  · revert hctrl
    cases hfi : P.fetch i with
    | none => intro h; simp only [List.mem_singleton] at h; subst h; exact InRange_halt
    | some instr0 =>
      cases instr0 with
      | halt => intro h; simp only [List.mem_singleton] at h; subst h; exact InRange_halt
      | assign x e next =>
          intro h
          have hnext : blockOff P S next < (transform P S).size := blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hedge : blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i next).length ≤ (transform P S).size := by
            have h := hsz; simp only [blockLen, hfi] at h; omega
          simp only [List.mem_cons] at h
          rcases h with rfl | h
          · simp only [InRange_noop]; split
            · exact hnext
            · rename_i hne
              exact Nat.lt_of_lt_of_le (show blockOff P S i + (matNode P S i).length + 1
                  < blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i next).length by
                have := length_pos_of_isEmpty_false hne; omega) hedge
          · exact edgeChain_inrange hnext hedge instr h
      | noop next =>
          intro h
          have hnext : blockOff P S next < (transform P S).size := blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hedge : blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i next).length ≤ (transform P S).size := by
            have h := hsz; simp only [blockLen, hfi] at h; omega
          simp only [List.mem_cons] at h
          rcases h with rfl | h
          · simp only [InRange_noop]; split
            · exact hnext
            · rename_i hne
              exact Nat.lt_of_lt_of_le (show blockOff P S i + (matNode P S i).length + 1
                  < blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i next).length by
                have := length_pos_of_isEmpty_false hne; omega) hedge
          · exact edgeChain_inrange hnext hedge instr h
      | ifz x z nz =>
          intro h
          have hz : blockOff P S z < (transform P S).size := blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hnz : blockOff P S nz < (transform P S).size := blockOff_lt_size (wf.succ_lt hfi (by simp [Cmd.succs]))
          have hbl : blockLen P S i
              = (matNode P S i).length + 1 + (matEdge P S i z).length + (matEdge P S i nz).length := by
            unfold blockLen; rw [hfi]; exact (Nat.add_assoc _ _ _).symm
          have hez : blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i z).length ≤ (transform P S).size := by
            have h := hsz; rw [hbl] at h; omega
          have henz : blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i z).length + (matEdge P S i nz).length ≤ (transform P S).size := by
            have h := hsz; rw [hbl] at h; omega
          simp only [List.mem_cons, List.mem_append] at h
          rcases h with rfl | h | h
          · simp only [InRange_ifz]
            refine ⟨?_, ?_⟩
            · split
              · exact hz
              · rename_i hne
                exact Nat.lt_of_lt_of_le (show blockOff P S i + (matNode P S i).length + 1
                    < blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i z).length by
                  have := length_pos_of_isEmpty_false hne; omega) hez
            · split
              · exact hnz
              · rename_i hne
                exact Nat.lt_of_lt_of_le (show blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i z).length
                    < blockOff P S i + (matNode P S i).length + 1 + (matEdge P S i z).length + (matEdge P S i nz).length by
                  have := length_pos_of_isEmpty_false hne; omega) henz
          · exact edgeChain_inrange hz hez instr h
          · exact edgeChain_inrange hnz henz instr h

/-- **Step 1 — well-formedness**, on the offset layout. -/
theorem transform_wellFormed {P : Program} (S : PdceSpec P) (wf : WellFormed P) :
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

end BaseLanguage.Analyses.PDCE
