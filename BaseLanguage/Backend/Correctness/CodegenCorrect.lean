-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.TacToAsm

namespace BaseLanguage

/-!
# `CodegenCorrect` — correctness of the `TacToAsm` instruction selection

The semantic core of the TAC→ARM64 code generator (`BaseLanguage/Backend/TacToAsm.lean`): the **ALU instruction-selection
correspondence** — for each arithmetic/bitwise/division `Binop`, the modelled AArch64 instruction the
codegen picks computes exactly the IR value, under the encoding `encode = Int64.toBitVec`. Because `Int64`
*is* a `BitVec 64` (its `+,-,*,&&&,|||,^^^,/` are defined as the corresponding `BitVec` operations), every
one of these is a **definitional** equality (`rfl`) — the homomorphism that makes the model faithful to the
IR for these operators, kernel-checked, standard-3 axioms.

## Status of the full simulation

The whole-program simulation theorem — *`Asm.run (codegen P)` from `initState P σ₀` reproduces
`Semantics` execution of `P`, preserving the frame↔store relation and observable outcome* — is **proved**
as `codegen_simulates` (`CodegenForward.lean`). Its computational core (this file's ALU correspondence) is
joined by: the shift correspondence (`shl/lshr/ashr`, via the `smod 64 ↔ %64` `BitVec` bridge
`toNat_smod_64`, `CodegenBinop.lean`); the comparison correspondence (`eq…leu`), which is **definitional** —
`cmp; cset .c` leaves exactly `encode (Binop.denote .c va vb)` by `rfl`, with **no** `subFlags`/`Cond.holds`
flag-identity proof needed; and the fixed-block control-flow induction (`CodegenForward`). The whole chain
is `sorry`-free. As an independent end-to-end sanity check, `codegen` also agrees with `Semantics` on every
variable across the sample battery (straight-line, branches, loops, `div`/`mod`, shifts, comparisons), and
the produced native binaries print byte-identical output to the reference text backend.
-/

namespace TacToAsm

open Tac Asm

/-! ## ALU instruction-selection correspondence (verified, `rfl`, standard-3) -/

/-- `add` ↦ `ADD`. -/
theorem alu_add (a b : Val) : aluEval .add (encode a) (encode b) = encode (a + b) := rfl
/-- `sub` ↦ `SUB`. -/
theorem alu_sub (a b : Val) : aluEval .sub (encode a) (encode b) = encode (a - b) := rfl
/-- `mul` ↦ `MUL`. -/
theorem alu_mul (a b : Val) : aluEval .mul (encode a) (encode b) = encode (a * b) := rfl
/-- `and` ↦ `AND`. -/
theorem alu_and (a b : Val) : aluEval .and_ (encode a) (encode b) = encode (a &&& b) := rfl
/-- `or` ↦ `ORR`. -/
theorem alu_or (a b : Val) : aluEval .orr (encode a) (encode b) = encode (a ||| b) := rfl
/-- `xor` ↦ `EOR`. -/
theorem alu_xor (a b : Val) : aluEval .eor (encode a) (encode b) = encode (a ^^^ b) := rfl
/-- `div` ↦ `SDIV`. Holds **unconditionally** — both `Int64./` and `BitVec.sdiv` return `0` on a zero
    divisor (the codegen's `cbz → faultPc` guard is what realises the IR's separate `Faulting`, D24). -/
theorem alu_div (a b : Val) : aluEval .sdiv (encode a) (encode b) = encode (a / b) := rfl

/-- **`mod` ↦ `SDIV;MSUB`.** The codegen's `sdiv x11,a,b; msub x9,x11,b,a` sequence computes `x9 :=
    a - (a sdiv b)*b`, which is exactly the IR's `mod` denotation, written in the
    architecture's truncated-remainder form `a - a/b*b` (`Binop.denote .mod`). Definitional. -/
theorem mod_msub (a b : Val) :
    (encode a - aluEval .sdiv (encode a) (encode b) * encode b) = encode (a - a / b * b) := rfl

end TacToAsm

end BaseLanguage
