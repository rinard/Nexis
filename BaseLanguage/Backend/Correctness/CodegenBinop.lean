-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Correctness.CodegenCorrect
import BaseLanguage.IR.TAC

namespace BaseLanguage

/-!
# `CodegenBinop` — the comparison value-correspondence (the `cmp;cset` payoff of the result-level model)

The arithmetic/bitwise `Binop`s correspond to the machine ALU **definitionally** (`encode = Int64.toBitVec`
is a `BitVec` homomorphism — `CodegenCorrect.alu_*`, all `rfl`). After modelling `cmp`/`cset` at the result
level (`Asm.lean`, option (b): `Cond.c.holds (subFlags a b)` *is* the matching `BitVec` comparison), the
**comparison** `Binop`s correspond definitionally too: the value `cmp x9 x10; cset x9 .c` leaves in `x9` is
exactly `encode (Binop.denote .c va vb)`, by `rfl`. No flag-identity proof, and (crucially) no `bv_decide`
— which on this toolchain pulls in a trusted native axiom, breaking the `[propext, Classical.choice,
Quot.sound]` discipline.

These are the per-operator value facts the `binArm`/`emitExpr` simulation consumes for the six comparison
operators; with `alu_*` (arithmetic), `alu_div`/`mod_msub` (division), and the shift bridges they cover
every `Binop`. The shifts are also a match — `Int64`'s `<<<`/`>>>` mask the amount mod 64 exactly like
AArch64 (`Int64.toBitVec_shiftLeft = … <<< b.smod 64`, and `(b.smod 64).toNat = b.toNat % 64`) — but their
bridge is a short `toNat`-of-`smod`/`umod` lemma rather than `rfl`, so it lives with the simulation step.
-/

namespace Asm

/-- **The shift-amount masks coincide.** `Int64`'s `<<<`/`>>>` reduce the amount by `smod 64`; the machine
    model masks by `toNat % 64` (the architectural low 6 bits). They agree: `(b.smod 64).toNat = b.toNat % 64`.
    (`smod`-by-`64`: the `msb=false` branch is `umod`; the `msb=true` branch's `64 − ((2⁶⁴−n) % 64)` equals
    `n % 64` because `2⁶⁴ ≡ 0 (mod 64)`.) -/
theorem toNat_smod_64 (b : BitVec 64) : (b.smod 64).toNat = b.toNat % 64 := by
  have hb : b.toNat < 2 ^ 64 := b.isLt
  have h64 : (64 : BitVec 64).toNat = 64 := by decide
  unfold BitVec.smod
  rw [show (64 : BitVec 64).msb = false from by decide]
  cases hm : b.msb
  · -- false: b.umod 64
    show (b % 64).toNat = b.toNat % 64
    rw [BitVec.toNat_umod, h64]
  · -- true: if (b.neg % 64) = 0 then it else 64 - it
    show (if b.neg % 64 = BitVec.zero 64 then b.neg % 64 else (64 : BitVec 64) - b.neg % 64).toNat
          = b.toNat % 64
    have hge : 2 * b.toNat ≥ 2 ^ 64 := BitVec.msb_eq_true_iff_two_mul_ge.mp hm
    have hu : (b.neg % 64).toNat = (2 ^ 64 - b.toNat) % 64 := by
      rw [BitVec.toNat_umod, h64, show b.neg = -b from rfl, BitVec.toNat_neg,
          show (2 ^ 64 - b.toNat) % 2 ^ 64 = 2 ^ 64 - b.toNat from by omega]
    by_cases hz : b.neg % 64 = BitVec.zero 64
    · rw [if_pos hz, hz]
      have hz0 : (b.neg % 64).toNat = 0 := by rw [hz]; rfl
      rw [hu] at hz0; show (0 : Nat) = b.toNat % 64; omega
    · rw [if_neg hz]
      have hune : (b.neg % 64).toNat ≠ 0 := fun h =>
        hz (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      rw [hu] at hune
      rw [BitVec.toNat_sub, hu, h64]
      omega

end Asm

namespace TacToAsm

open Tac Asm

/-- The value `cset Xd, c` writes after `cmp Xn, Xm` (Xn = `encode a`, Xm = `encode b`). -/
abbrev csetVal (c : Cond) (a b : Val) : Asm.Word :=
  if c.holds (subFlags (encode a) (encode b)) then 1 else 0

/-- `Int64` equality is bit-pattern equality (`encode = toBitVec` is injective). -/
theorem encode_beq (a b : Val) : (a == b) = (encode a == encode b) := by
  unfold encode
  by_cases h : a = b
  · subst h; simp
  · rw [beq_eq_false_iff_ne.mpr h,
        beq_eq_false_iff_ne.mpr (fun he => h (Int64.toBitVec_inj.mp he))]

/-- **`eq` correspondence** — `cmp;cset eq` computes `encode (a == b)`. -/
theorem cset_eq (a b : Val) :
    encode ((Binop.eq.denote a b).getD 0) = csetVal .eq a b := by
  simp only [Binop.denote, csetVal, Cond.holds, Val.ofBool, subFlags, Option.getD, encode_beq]
  split <;> rfl

/-- **`ne` correspondence.** -/
theorem cset_ne (a b : Val) :
    encode ((Binop.ne.denote a b).getD 0) = csetVal .ne a b := by
  simp only [Binop.denote, csetVal, Cond.holds, Val.ofBool, subFlags, Option.getD, encode_beq]
  split <;> rfl

/-- **`lt` (signed) correspondence.** -/
theorem cset_lt (a b : Val) :
    encode ((Binop.lt.denote a b).getD 0) = csetVal .lt a b := by
  simp only [Binop.denote, csetVal, Cond.holds, encode, Val.ofBool, subFlags, Option.getD]
  split <;> rfl

/-- **`le` (signed) correspondence.** -/
theorem cset_le (a b : Val) :
    encode ((Binop.le.denote a b).getD 0) = csetVal .le a b := by
  simp only [Binop.denote, csetVal, Cond.holds, encode, Val.ofBool, subFlags, Option.getD]
  split <;> rfl

/-- **`ltu` (unsigned) correspondence** — `cmp;cset lo`. -/
theorem cset_ltu (a b : Val) :
    encode ((Binop.ltu.denote a b).getD 0) = csetVal .lo a b := by
  simp only [Binop.denote, csetVal, Cond.holds, encode, Val.ofBool, subFlags, Option.getD]
  split <;> rfl

/-- **`leu` (unsigned) correspondence** — `cmp;cset ls`. -/
theorem cset_leu (a b : Val) :
    encode ((Binop.leu.denote a b).getD 0) = csetVal .ls a b := by
  simp only [Binop.denote, csetVal, Cond.holds, encode, Val.ofBool, subFlags, Option.getD]
  split <;> rfl

/-! ### Shift correspondences — `Int64`'s masked shift = the machine's `aluEval` masked shift -/

/-- **`shl` correspondence.** `Int64 <<<` masks by `smod 64`, the machine by `toNat % 64`; equal by
    `Asm.toNat_smod_64`. -/
theorem shift_shl (a b : Val) :
    encode ((Binop.shl.denote a b).getD 0) = aluEval .lsl (encode a) (encode b) := by
  simp only [Binop.denote, Option.getD, encode, aluEval]
  rw [Int64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', Asm.toNat_smod_64]

/-- **`ashr` (arithmetic) correspondence.** -/
theorem shift_ashr (a b : Val) :
    encode ((Binop.ashr.denote a b).getD 0) = aluEval .asr (encode a) (encode b) := by
  simp only [Binop.denote, Option.getD, encode, aluEval]
  rw [Int64.toBitVec_shiftRight, BitVec.sshiftRight_eq', Asm.toNat_smod_64]

/-- **`lshr` (logical) correspondence.** Goes through `UInt64 >>>` (masks by `% 64`); equal by
    `BitVec.toNat_umod`. -/
theorem shift_lshr (a b : Val) :
    encode ((Binop.lshr.denote a b).getD 0) = aluEval .lsr (encode a) (encode b) := by
  simp only [Binop.denote, Option.getD, encode, aluEval]
  rw [show ((a.toUInt64 >>> b.toUInt64).toInt64).toBitVec = (a.toUInt64 >>> b.toUInt64).toBitVec from rfl,
      UInt64.toBitVec_shiftRight, BitVec.ushiftRight_eq', BitVec.toNat_umod]
  rfl

end TacToAsm

end BaseLanguage
