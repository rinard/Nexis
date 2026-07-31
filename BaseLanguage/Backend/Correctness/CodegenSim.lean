-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.TacToAsm

namespace BaseLanguage

/-!
# `CodegenSim` — foundation for the forward codegen simulation (`CodegenForward`)

The forward simulation `CodegenForward` is the verified backend's central theorem. This file lands its
**layout foundation**, sorry-free: the generated program is a
sequence of fixed-`B`-size blocks, so model pc `nd*B + j` indexes the `j`-th instruction of node `nd`'s
block (`codegen_block_get`). With that, per-block stepping reduces to reasoning about a known short
instruction list.

The obligations for `CodegenForward` staged on this foundation are now **all discharged**:
* expression-eval correctness — `emitExpr_correct` (`CodegenEmit.lean`): running `emitExpr e` from a
  `StateRel` state leaves `encode (eval e σ)` in `x9` (induction on `Expr`, using the `CodegenCorrect` ALU lemmas);
* per-block forward step for `assign`/`ifz`/`noop`/`halt`, incl. the `div`/`mod` `cbz→abort` fault path —
  `forward_step` (`CodegenForward.lean`);
* whole-program threading over `Steps` (halts) and the fuel accounting for divergence — `codegen_simulates`.
-/

namespace TacToAsm

open Tac

/-! ## Generic: indexing a `flatMap` of constant-length blocks -/

theorem length_flatMap_const {α} {g : Nat → List α} {L : Nat} (hL : ∀ i, (g i).length = L) :
    ∀ n, ((List.range n).flatMap g).length = n * L := by
  intro n
  induction n with
  | zero => simp [List.range_zero, Nat.zero_mul]
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih,
        List.flatMap_singleton, hL, Nat.add_mul, Nat.one_mul]

theorem flatMap_const_get {α} {g : Nat → List α} {L : Nat} (hL : ∀ i, (g i).length = L) :
    ∀ (n i j : Nat), i < n → j < L → ((List.range n).flatMap g)[i * L + j]? = (g i)[j]? := by
  intro n
  induction n with
  | zero => intro i j hi _; exact absurd hi (Nat.not_lt_zero i)
  | succ k ih =>
    intro i j hi hj
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    rcases Nat.lt_or_ge i k with hik | hik
    · have hb : i * L + j < ((List.range k).flatMap g).length := by
        rw [length_flatMap_const hL]
        have h2 : (i + 1) * L ≤ k * L := Nat.mul_le_mul_right L hik
        rw [Nat.add_mul, Nat.one_mul] at h2; omega
      rw [List.getElem?_append_left hb]; exact ih i j hik hj
    · have heq : i = k := Nat.le_antisymm (Nat.lt_succ_iff.mp hi) hik
      subst heq
      have hge : ((List.range i).flatMap g).length ≤ i * L + j := by
        rw [length_flatMap_const hL]; omega
      rw [List.getElem?_append_right hge, length_flatMap_const hL]
      congr 1; omega

/-! ## Block-length bounds (so `pad` yields exactly `B`) -/

theorem binArm_length_le (fp : Nat) (op : Binop) : (binArm fp op).length ≤ 3 := by
  cases op <;> simp [binArm]

theorem emitExpr_length_le (vs : List Var) (fp : Nat) (e : Expr) :
    (emitExpr vs fp e).length ≤ 6 := by
  cases e with
  | atom a => cases a <;> simp [emitExpr, loadAtom]
  | una op a => cases a <;> cases op <;> simp [emitExpr, loadAtom, unArm]
  | bin op a b =>
    simp only [emitExpr, List.length_append]
    have h1 : (loadAtom vs 9 a).length ≤ 1 := by cases a <;> simp [loadAtom]
    have h2 : (loadAtom vs 10 b).length ≤ 1 := by cases b <;> simp [loadAtom]
    have h3 := binArm_length_le fp op
    omega

theorem blockFor_length_le (vs : List Var) (fp : Nat) (instr : Cmd) :
    (blockFor vs fp instr).length ≤ B := by
  cases instr with
  | assign x e next =>
    simp only [blockFor, List.length_append, List.length_cons, List.length_nil]
    have := emitExpr_length_le vs fp e
    simp only [B]; omega
  | ifz x a b => simp [blockFor, B]
  | noop next => simp [blockFor, B]
  | halt => simp [blockFor, B]

/-! ## `pad` yields exactly `B`; each compiled block has length `B` -/

theorem pad_length {l : List Asm.Cmd} (h : l.length ≤ B) : (pad l).length = B := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem block_length (P : Program) (i : Nat) :
    (pad (blockFor (collectVars P) (P.code.size * B) (P.code[i]!))).length = B :=
  pad_length (blockFor_length_le _ _ _)

/-! ## Layout: pc `nd*B + j` indexes node `nd`'s block -/

/-- **The generated program is fixed-block-laid-out.** For `nd < numNodes` and `j < B`, model pc
    `nd*B + j` selects the `j`-th instruction of node `nd`'s padded block — the key to per-block stepping. -/
theorem codegen_block_get (P : Program) (nd j : Nat)
    (hnd : nd < P.code.size) (hj : j < B) :
    (codegen P)[nd * B + j]? =
      (pad (blockFor (collectVars P) (P.code.size * B) (P.code[nd]!)))[j]? := by
  have hidx : nd * B + j < ((List.range P.code.size).flatMap
      (fun i => pad (blockFor (collectVars P) (P.code.size * B) (P.code[i]!)))).length := by
    rw [length_flatMap_const (fun i => block_length P i)]
    have h2 : (nd + 1) * B ≤ P.code.size * B := Nat.mul_le_mul_right B hnd
    rw [Nat.add_mul, Nat.one_mul] at h2; omega
  simp only [codegen]
  rw [List.getElem?_toArray, List.getElem?_append_left hidx]
  exact flatMap_const_get (fun i => block_length P i) P.code.size nd j hnd hj

end TacToAsm

end BaseLanguage
