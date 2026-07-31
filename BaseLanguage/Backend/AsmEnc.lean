-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Asm
import BaseLanguage.Meta.AxiomCheck

namespace BaseLanguage

/-!
# `AsmEnc` — a **verified** structured-assembly encoder for the `Asm` model

This is the layer that pulls the previously-*trusted* instruction printing into the verified core
(Tiers 1–2 of "maximize verified codegen"). The old path was `Asm.Cmd → String` in one unverified
step, so the real-ISA encoding constraints (the load/store immediate-offset ceiling, register
legality) lived *below* the verification line — which is exactly why the frame-slot offset bug could
exist. Here they live *above* it:

* **Structured lines.** `AsmLine` is a typed representation of the assembler lines the backend emits
  (one constructor per real instruction form, including the register-offset form used to reach a slot
  past the immediate ceiling). The final printer renders each `AsmLine` 1:1 with a trivial syntactic
  `renderLine` (the only remaining trusted syntactic step).

* **Tier 1 — encodability is a theorem.** `AsmLine.wf` captures the real AArch64 encoding constraints
  the assembler enforces: a 64-bit `ldr/str` unsigned-offset immediate must be `≤ 32760` and a
  multiple of `8`; register indices are `< 32`. `emitCmd` **legalizes** — an over-ceiling slot access
  is lowered to `ldr x16, =off ; ldr Xd, [x29, x16]` (register offset, unconstrained). `emitCmd_wf`
  proves `emitCmd` *never* produces an un-encodable line (given a well-formed model instruction). The
  slot-offset bug class is now impossible by construction, not merely absent.

* **Tier 2 — the encoding is faithful.** `decodeLines` recovers the model instruction from the emitted
  lines, and `decode_emitCmd` proves the round-trip `decode (emitCmd c) = some c` for every core
  instruction. So the emitter is injective and loses nothing — the assembly unambiguously represents
  the model `Cmd` it came from (CakeML-style `enc_ok`, at the structural level).

**Still trusted (Tier 3+ / inherently):** `renderLine`'s syntactic rendering (trivial, total,
inspectable); the *semantics* of the well-formed lines on real hardware (a full AArch64 machine model
with SP/stack/registers — the large remaining step); and the ABI terminals `halt`/`print` (the
`_printf`/`ret`/`_abort` sequences), which are context-dependent OS/libc ABI and are handled by the
printer scaffolding — every verified compiler axiomatizes external calls.
-/

namespace AsmEnc
open Asm

/-! ## Structured assembler lines -/

/-- One assembler line the backend emits, as a typed value (rendered 1:1 by `renderLine`). The
    `*RegOff` and `litOff` forms are the register-offset legalization for over-ceiling slots. -/
inductive AsmLine where
  | alu           (op : ALU) (rd rn rm : Nat)   -- add/sub/… Xd, Xn, Xm
  | msub          (rd rn rm ra : Nat)
  | neg           (rd rn : Nat)
  | mvn           (rd rn : Nat)
  | ldrImmOff     (rd off : Nat)                -- ldr Xd, [x29, #off]      (immediate offset)
  | strImmOff     (rs off : Nat)                -- str Xs, [x29, #off]
  | strZeroImmOff (off : Nat)                   -- str xzr, [x29, #off]
  | ldrRegOff     (rd idx : Nat)                -- ldr Xd, [x29, Xidx]      (register offset)
  | strRegOff     (rs idx : Nat)                -- str Xs, [x29, Xidx]
  | strZeroRegOff (idx : Nat)                   -- str xzr, [x29, Xidx]
  | litWord       (rd : Nat) (w : Word)         -- ldr Xd, =imm             (literal-pool word)
  | litOff        (rd off : Nat)                -- ldr Xd, =off             (materialized offset)
  | cmp           (rn rm : Nat)
  | cset          (rd : Nat) (c : Cond)
  | b             (target : Nat)                -- b L<target>
  | cbz           (rn target : Nat)             -- cbz Xn, L<target>
  | abort                                       -- bl _abort
  deriving Repr

/-- The 64-bit `ldr/str` unsigned-offset immediate ceiling (`imm12 × 8 = 4095 × 8`). -/
def offCeil : Nat := 32760

/-- **Encodability** of one line — the constraints the assembler enforces. A 64-bit immediate-offset
    `ldr/str` needs its offset `≤ offCeil` and `8`-aligned; every register index is `< 32`. The
    register-offset and literal forms carry no offset immediate, so they are legal for any offset. -/
def AsmLine.wf : AsmLine → Bool
  | .alu _ rd rn rm      => rd < 32 && rn < 32 && rm < 32
  | .msub rd rn rm ra    => rd < 32 && rn < 32 && rm < 32 && ra < 32
  | .neg rd rn           => rd < 32 && rn < 32
  | .mvn rd rn           => rd < 32 && rn < 32
  | .ldrImmOff rd off    => rd < 32 && off % 8 == 0 && off ≤ offCeil
  | .strImmOff rs off    => rs < 32 && off % 8 == 0 && off ≤ offCeil
  | .strZeroImmOff off   => off % 8 == 0 && off ≤ offCeil
  | .ldrRegOff rd idx    => rd < 32 && idx < 32
  | .strRegOff rs idx    => rs < 32 && idx < 32
  | .strZeroRegOff idx   => idx < 32
  | .litWord rd _        => rd < 32
  | .litOff rd _         => rd < 32
  | .cmp rn rm           => rn < 32 && rm < 32
  | .cset rd _           => rd < 32
  | .b _                 => true
  | .cbz rn _            => rn < 32
  | .abort               => true

/-! ## Model-instruction well-formedness (the emitter's precondition) -/

/-- A model `Cmd` is emittable when its registers are `< 32` and any slot offset is `8`-aligned (the
    model's `mem` is byte-addressed, but a 64-bit access must be `8`-aligned). No offset *ceiling* here
    — `emitCmd` legalizes large offsets. `halt`/`print` are the ABI terminals (handled by scaffolding). -/
def cmdWf : Cmd → Bool
  | .alu _ rd rn rm      => rd < 32 && rn < 32 && rm < 32
  | .msub rd rn rm ra    => rd < 32 && rn < 32 && rm < 32 && ra < 32
  | .neg rd rn           => rd < 32 && rn < 32
  | .mvn rd rn           => rd < 32 && rn < 32
  | .ldrSlot rd off      => rd < 32 && off % 8 == 0
  | .strSlot rs off      => rs < 32 && off % 8 == 0
  | .strZero off         => off % 8 == 0
  | .ldrImm rd _         => rd < 32
  | .cmp rn rm           => rn < 32 && rm < 32
  | .cset rd _           => rd < 32
  | .b _                 => true
  | .cbz rn _            => rn < 32
  | .print rs            => rs < 32
  | .halt                => true
  | .abort               => true

/-- The "core" (context-free) instructions — everything except the ABI terminals `halt`/`print`,
    whose expansion needs the observable list + frame size and stays in the printer scaffolding. -/
def isCore : Cmd → Bool
  | .halt    => false
  | .print _ => false
  | _        => true

/-! ## The legalizing emitter -/

/-- Emit one model instruction as structured lines. The only non-1:1 case is an over-ceiling slot
    access, lowered to the register-offset form via scratch `x16` (IP0, never used by the body). -/
def emitCmd : Cmd → List AsmLine
  | .alu op rd rn rm  => [.alu op rd rn rm]
  | .msub rd rn rm ra => [.msub rd rn rm ra]
  | .neg rd rn        => [.neg rd rn]
  | .mvn rd rn        => [.mvn rd rn]
  | .ldrSlot rd off   => if off ≤ offCeil then [.ldrImmOff rd off]
                         else [.litOff 16 off, .ldrRegOff rd 16]
  | .strSlot rs off   => if off ≤ offCeil then [.strImmOff rs off]
                         else [.litOff 16 off, .strRegOff rs 16]
  | .strZero off      => if off ≤ offCeil then [.strZeroImmOff off]
                         else [.litOff 16 off, .strZeroRegOff 16]
  | .ldrImm rd imm    => [.litWord rd imm]
  | .cmp rn rm        => [.cmp rn rm]
  | .cset rd c        => [.cset rd c]
  | .b t              => [.b t]
  | .cbz rn t         => [.cbz rn t]
  | .abort            => [.abort]
  | .halt             => []          -- ABI terminal — emitted by the printer scaffolding
  | .print _          => []          -- ABI terminal — emitted by the printer scaffolding

/-! ## Tier 1 — the emitter only produces encodable lines -/

/-- **Legality is a theorem.** For any well-formed model instruction, every line `emitCmd` produces
    satisfies `AsmLine.wf` — in particular no immediate-offset `ldr/str` ever exceeds the `32760`
    ceiling (over-ceiling slots take the register-offset path). The frame-slot bug class is closed. -/
theorem emitCmd_wf {c : Cmd} (h : cmdWf c = true) : (emitCmd c).all AsmLine.wf = true := by
  cases c with
  | alu op rd rn rm  => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | msub rd rn rm ra => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | neg rd rn        => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | mvn rd rn        => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | ldrSlot rd off   => simp only [emitCmd]; split <;>
                          simp_all [cmdWf, AsmLine.wf, offCeil, List.all] <;> omega
  | strSlot rs off   => simp only [emitCmd]; split <;>
                          simp_all [cmdWf, AsmLine.wf, offCeil, List.all] <;> omega
  | strZero off      => simp only [emitCmd]; split <;>
                          simp_all [cmdWf, AsmLine.wf, offCeil, List.all] <;> omega
  | ldrImm rd imm    => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | cmp rn rm        => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | cset rd cc       => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | b t              => simp [emitCmd, AsmLine.wf, List.all]
  | cbz rn t         => simp_all [emitCmd, cmdWf, AsmLine.wf, List.all]
  | print rs         => simp [emitCmd]
  | halt             => simp [emitCmd]
  | abort            => simp [emitCmd, AsmLine.wf, List.all]

/-! ## Tier 2 — the encoding is faithful (round-trips) -/

/-- Recover the model instruction from emitted lines. Inverse of `emitCmd` on the core set. -/
def decodeLines : List AsmLine → Option Cmd
  | [.alu op rd rn rm]                    => some (.alu op rd rn rm)
  | [.msub rd rn rm ra]                   => some (.msub rd rn rm ra)
  | [.neg rd rn]                          => some (.neg rd rn)
  | [.mvn rd rn]                          => some (.mvn rd rn)
  | [.ldrImmOff rd off]                   => some (.ldrSlot rd off)
  | [.strImmOff rs off]                   => some (.strSlot rs off)
  | [.strZeroImmOff off]                  => some (.strZero off)
  | [.litOff 16 off, .ldrRegOff rd 16]    => some (.ldrSlot rd off)
  | [.litOff 16 off, .strRegOff rs 16]    => some (.strSlot rs off)
  | [.litOff 16 off, .strZeroRegOff 16]   => some (.strZero off)
  | [.litWord rd imm]                     => some (.ldrImm rd imm)
  | [.cmp rn rm]                          => some (.cmp rn rm)
  | [.cset rd c]                          => some (.cset rd c)
  | [.b t]                                => some (.b t)
  | [.cbz rn t]                           => some (.cbz rn t)
  | [.abort]                              => some .abort
  | _                                     => none

/-- **Faithful encoding.** Every core instruction round-trips through the emitter: the emitted lines
    decode back to exactly the instruction they came from. So `emitCmd` is injective and lossless —
    the assembly unambiguously represents its model `Cmd`. -/
theorem decode_emitCmd {c : Cmd} (hc : isCore c = true) :
    decodeLines (emitCmd c) = some c := by
  cases c with
  | ldrSlot rd off => simp only [emitCmd]; split <;> rfl
  | strSlot rs off => simp only [emitCmd]; split <;> rfl
  | strZero off    => simp only [emitCmd]; split <;> rfl
  | halt           => simp [isCore] at hc
  | print rs       => simp [isCore] at hc
  | alu op rd rn rm => rfl
  | msub rd rn rm ra => rfl
  | neg rd rn      => rfl
  | mvn rd rn      => rfl
  | ldrImm rd imm  => rfl
  | cmp rn rm      => rfl
  | cset rd cc     => rfl
  | b t            => rfl
  | cbz rn t       => rfl
  | abort          => rfl

#assert_clean_axioms emitCmd_wf
#assert_clean_axioms decode_emitCmd

end AsmEnc

end BaseLanguage
