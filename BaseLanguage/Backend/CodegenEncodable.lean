-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.TacToAsm
import BaseLanguage.Backend.AsmEnc
import BaseLanguage.Meta.AxiomCheck

namespace BaseLanguage
namespace TacToAsm
open AsmEnc Tac

/-!
# `CodegenEncodable` — the code generator emits only encodable instructions

The connector that makes the Tier-1 legality guarantee end-to-end: every instruction the verified
`codegen` produces satisfies `AsmEnc.cmdWf` (registers `< 32`, slot offsets `8`-aligned). Composed with
`AsmEnc.emitCmd_wf` (which legalizes offsets past the immediate ceiling), the whole chain
**`codegen → cmdWf → emitCmd → AsmLine.wf`** is a theorem: the backend never emits an un-encodable line.
-/

/-- Every frame-slot byte offset is `8`-aligned (`16 + 8·idx`). -/
theorem slotOff_align (vs : List Var) (v : Var) : slotOff vs v % 8 = 0 := by
  unfold slotOff; omega

/-- A slot load into a register `< 32` is well-formed. -/
theorem cmdWf_ldrSlot {vs : List Var} {r : Nat} (v : Var) (hr : r < 32) :
    cmdWf (.ldrSlot r (slot vs v)) = true := by
  simp only [cmdWf, slot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨hr, slotOff_align vs v⟩

/-- A slot store from a register `< 32` is well-formed. -/
theorem cmdWf_strSlot {vs : List Var} {r : Nat} (v : Var) (hr : r < 32) :
    cmdWf (.strSlot r (slot vs v)) = true := by
  simp only [cmdWf, slot, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨hr, slotOff_align vs v⟩

/-- Loading an atom into a register `< 32` is well-formed. -/
theorem loadAtom_allWf {vs : List Var} {r : Nat} (hr : r < 32) (a : Atom) :
    (loadAtom vs r a).all cmdWf = true := by
  cases a with
  | var v => simp [loadAtom, cmdWf_ldrSlot v hr]
  | imm n => simp [loadAtom, cmdWf, hr]

/-- The unary-op instructions (fixed register `9`) are well-formed. -/
theorem unArm_allWf (op : Unop) : (unArm op).all cmdWf = true := by
  cases op <;> rfl

/-- The binary-op instructions (fixed registers `9`/`10`/`11`) are well-formed. -/
theorem binArm_allWf (fault : Nat) (op : Binop) : (binArm fault op).all cmdWf = true := by
  cases op <;> rfl

/-- Evaluating an expression into `x9`/`x10` is well-formed. -/
theorem emitExpr_allWf {vs : List Var} {fault : Nat} (e : Expr) :
    (emitExpr vs fault e).all cmdWf = true := by
  cases e with
  | atom a => exact loadAtom_allWf (r := 9) (by decide) a
  | una op a =>
    simp [emitExpr, List.all_append, loadAtom_allWf (r := 9) (by decide) a, unArm_allWf op]
  | bin op a b =>
    simp [emitExpr, List.all_append, loadAtom_allWf (r := 9) (by decide) a,
          loadAtom_allWf (r := 10) (by decide) b, binArm_allWf fault op]

/-- Every real instruction of a node's block is well-formed. -/
theorem blockFor_allWf {vs : List Var} {fault : Nat} (cmd : Tac.Cmd) :
    (blockFor vs fault cmd).all cmdWf = true := by
  cases cmd with
  | assign x e next =>
    have hb : cmdWf (Asm.Cmd.b (next * B)) = true := rfl
    simp [blockFor, List.all_append, emitExpr_allWf e,
          cmdWf_strSlot x (by decide : (9:Nat) < 32), hb]
  | ifz x a b =>
    have hcbz : cmdWf (Asm.Cmd.cbz 9 (a * B)) = true := rfl
    have hb : cmdWf (Asm.Cmd.b (b * B)) = true := rfl
    simp [blockFor, cmdWf_ldrSlot x (by decide : (9:Nat) < 32), hcbz, hb]
  | noop next => rfl
  | halt => rfl

/-- Padding a well-formed block with unreachable `abort`s stays well-formed. -/
theorem pad_allWf {l : List Asm.Cmd} (h : l.all cmdWf = true) : (pad l).all cmdWf = true := by
  have hrep : ∀ k, (List.replicate k Asm.Cmd.abort).all cmdWf = true := by
    intro k; induction k with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.all_cons, ih]; rfl
  simp only [pad, List.all_append, h, Bool.true_and, hrep]

/-- **The code generator emits only encodable instructions.** Every instruction in `codegen P`
    satisfies `cmdWf`; via `AsmEnc.emitCmd_wf` the emitted assembly is guaranteed encodable. -/
theorem codegen_cmdWf {P : Program} : ∀ c ∈ codegen P, cmdWf c = true := by
  intro c hc
  simp only [codegen, List.mem_toArray, List.mem_append, List.mem_flatMap, List.mem_range] at hc
  rcases hc with ⟨i, _, hmem⟩ | hmem
  · exact List.all_eq_true.1 (pad_allWf (blockFor_allWf (vs := collectVars P) (P.code[i]!))) c hmem
  · exact List.all_eq_true.1 (pad_allWf (l := [Asm.Cmd.abort]) rfl) c hmem

/-- **Headline (Tiers 1 + 2).** Every assembler line the backend emits for an instruction of
    `codegen P` is encodable — no un-encodable immediate offset (or illegal register) can be produced.
    `codegen_cmdWf` (this file) feeds `AsmEnc.emitCmd_wf`; the printer's `renderLine` then renders these
    already-legal, already-round-tripping (`AsmEnc.decode_emitCmd`) lines 1:1. -/
theorem codegen_emits_wf {P : Program} {c : Asm.Cmd} (hc : c ∈ codegen P) :
    (emitCmd c).all AsmLine.wf = true :=
  emitCmd_wf (codegen_cmdWf c hc)

#assert_clean_axioms codegen_cmdWf
#assert_clean_axioms codegen_emits_wf

end TacToAsm

end BaseLanguage
