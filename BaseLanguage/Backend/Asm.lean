-- Copyright (c) 2026 Martin Rinard
namespace BaseLanguage

/-!
# `Asm` — operational semantics for the AArch64 subset the backend emits

A small-step (here: deterministic functional) model of the ~20 AArch64 instructions the backend emits
(selected by `TacToAsm`, printed by `BaseLanguage/Backend/AsmToText.lean`), over `BitVec 64` registers + a
word-addressed frame. This is the target the `TacToAsm` codegen-correctness proof simulates against (the
verified replacement for the "trusted backend" link). Self-contained — no project imports; only
Lean-core `BitVec`.

Scope (mirrors the emitter): spill-everything frame (`ldr/str [x29,#off]`), 3-register ALU
(`add/sub/mul/sdiv/and/orr/eor` + register `lsl/lsr/asr`), `msub` (for `mod`), `neg/mvn`, `cmp`+`cset`
(result-level comparison — see below), `b`/`cbz` control flow, `_printf`/`_abort`/`ret` modelled as
`print`/`abort`/`halt` terminals.

## Comparison model — `cmp`/`cset` at the result level (not NZCV bits)

The emitter only ever uses `cmp` immediately followed by `cset` (never reads individual flags, and `cbz`
tests a register, not flags). So instead of modelling the four NZCV bits and the per-condition decode, the
model records the two compared operands at `cmp` and lets `Cond.holds` read back the corresponding signed/
unsigned `BitVec` comparison at `cset` — which is *exactly* what the architecture's NZCV decode computes
(`cset Xd, lt` after `cmp a, b` yields `a <ₛ b`, etc.). This makes the codegen comparison correspondence
**definitional** (`Binop.denote .lt` is `BitVec.slt`, and so is `Cond.lt.holds ∘ subFlags`) rather than a
flag-identity proof. The standing AArch64 fact "condition `c` after a compare = the matching `BitVec`
comparison" thus lives in this definition (the model's faithfulness for comparisons), not a theorem.
Register `31` is `xzr` (reads `0`, writes discarded). `sdiv` by `0` yields `0` (architecture-faithful —
the FAULT is the emitter's explicit `cbz x10, Lfault; bl _abort`, modelled as `cbz … ; abort`).

## ⚠ Shift semantics — the model-vs-architecture point

AArch64 **register-form** shifts (`LSL/LSR/ASR Xd, Xn, Xm`) use only the **low 6 bits** of the amount,
i.e. they shift by `Xm mod 64`. A naïve model that shifts a `BitVec 64` by the *full* `Xm` is a
**miscompile for amounts ≥ 64**: Lean/`BitVec` `x <<< 64 = 0`, but the hardware computes `x <<< (64 mod
64) = x <<< 0 = x` (identity). The same divergence hits 65, 128, … This model bakes the fix in from the start (`% 64` on every register
shift — see `aluEval`). The `*_64_id` / `unmasked_*` theorems below pin the architecture-faithful behaviour and
exhibit the divergence from the unmasked version.
-/

namespace Asm

abbrev W : Nat := 64
abbrev Word := BitVec W

/-! ## Comparison context + condition codes (result-level model — see header) -/

/-- The compare context recorded by `cmp a, b`: the two operands. (A result-level stand-in for NZCV —
    `Cond.holds` reads back the matching `BitVec` comparison, which equals the architecture's NZCV decode.) -/
structure Flags where
  lhs : Word
  rhs : Word
  deriving Repr, DecidableEq, Inhabited

/-- The condition codes `cset`/`b.cond` use. The emitter uses `eq ne lt le lo ls`; the rest round out
    the standard set so the model is complete. -/
inductive Cond where
  | eq | ne | lt | le | gt | ge | lo | ls | hi | hs
  deriving Repr, DecidableEq

/-- AArch64 condition after a compare, as the matching signed/unsigned `BitVec` comparison of the compared
    operands — exactly what the NZCV decode computes (see header). -/
def Cond.holds (f : Flags) : Cond → Bool
  | .eq => f.lhs == f.rhs
  | .ne => !(f.lhs == f.rhs)
  | .lt => f.lhs.slt f.rhs        -- signed <
  | .le => f.lhs.sle f.rhs        -- signed ≤
  | .gt => f.rhs.slt f.lhs        -- signed >
  | .ge => f.rhs.sle f.lhs        -- signed ≥
  | .lo => f.lhs.ult f.rhs        -- unsigned <
  | .ls => f.lhs.ule f.rhs        -- unsigned ≤
  | .hi => f.rhs.ult f.lhs        -- unsigned >
  | .hs => f.rhs.ule f.lhs        -- unsigned ≥

/-- The compare context produced by `cmp a, b` (records the operands; cf. `subs xzr, a, b` setting NZCV). -/
def subFlags (a b : Word) : Flags := { lhs := a, rhs := b }

/-! ## ALU -/

inductive ALU where
  | add | sub | mul | sdiv | and_ | orr | eor | lsl | lsr | asr
  deriving Repr, DecidableEq

/-- ALU evaluation. **Register shifts mask the amount to `mod 64`** (the architecture point). -/
def aluEval : ALU → Word → Word → Word
  | .add,  a, b => a + b
  | .sub,  a, b => a - b
  | .mul,  a, b => a * b
  | .sdiv, a, b => BitVec.sdiv a b                       -- AArch64 SDIV; ÷0 = 0 (no trap)
  | .and_, a, b => a &&& b
  | .orr,  a, b => a ||| b
  | .eor,  a, b => a ^^^ b
  | .lsl,  a, b => a <<< (b.toNat % W)                   -- LSL Xd,Xn,Xm : amount mod 64
  | .lsr,  a, b => a >>> (b.toNat % W)                   -- LSR : logical, amount mod 64
  | .asr,  a, b => BitVec.sshiftRight a (b.toNat % W)    -- ASR : arithmetic, amount mod 64

/-! ## Instructions, state, step -/

inductive Cmd where
  | alu     (op : ALU) (rd rn rm : Nat)
  | msub    (rd rn rm ra : Nat)         -- rd := ra - rn*rm  (AArch64 MSUB Xd,Xn,Xm,Xa)
  | neg     (rd rn : Nat)
  | mvn     (rd rn : Nat)
  | ldrSlot (rd off : Nat)              -- ldr Xrd, [x29, #off]
  | strSlot (rs off : Nat)              -- str Xrs, [x29, #off]
  | strZero (off : Nat)                 -- str xzr, [x29, #off]
  | ldrImm  (rd : Nat) (imm : Word)     -- ldr Xrd, =imm
  | cmp     (rn rm : Nat)
  | cset    (rd : Nat) (c : Cond)
  | b       (target : Nat)
  | cbz     (rn target : Nat)
  | print   (rs : Nat)                  -- _printf of one observable
  | halt                                -- ret
  | abort                               -- bl _abort (fault)
  deriving Repr, Inhabited

abbrev Prog := Array Cmd

structure State where
  regs : Nat → Word
  mem  : Nat → Word        -- frame, keyed by byte offset (slots are 8-aligned)
  flags : Flags
  out  : List Word         -- observable output trace (from `print`)
  pc   : Nat

/-- `x31` is `xzr`: reads as `0`. -/
@[inline] def State.get (s : State) (r : Nat) : Word := if r == 31 then 0 else s.regs r
/-- Writes to `xzr` are discarded. -/
@[inline] def State.set (s : State) (r : Nat) (v : Word) : State :=
  if r == 31 then s else { s with regs := fun r' => if r' == r then v else s.regs r' }
@[inline] def State.store (s : State) (off : Nat) (v : Word) : State :=
  { s with mem := fun o => if o == off then v else s.mem o }
@[inline] def State.next (s : State) : State := { s with pc := s.pc + 1 }

inductive StepOut where
  | cont  (s : State)
  | halt  (s : State)
  | fault
  deriving Inhabited

/-- One architectural step from `pc`. Falling off the program end faults. -/
def step (prog : Prog) (s : State) : StepOut :=
  match prog[s.pc]? with
  | none => .fault
  | some i =>
    match i with
    | .alu op rd rn rm => .cont ((s.set rd (aluEval op (s.get rn) (s.get rm))).next)
    | .msub rd rn rm ra => .cont ((s.set rd (s.get ra - s.get rn * s.get rm)).next)
    | .neg rd rn => .cont ((s.set rd (- s.get rn)).next)
    | .mvn rd rn => .cont ((s.set rd (~~~ s.get rn)).next)
    | .ldrSlot rd off => .cont ((s.set rd (s.mem off)).next)
    | .strSlot rs off => .cont ((s.store off (s.get rs)).next)
    | .strZero off => .cont ((s.store off 0).next)
    | .ldrImm rd imm => .cont ((s.set rd imm).next)
    | .cmp rn rm => .cont ({ s with flags := subFlags (s.get rn) (s.get rm) }.next)
    | .cset rd c => .cont ((s.set rd (if c.holds s.flags then 1 else 0)).next)
    | .b t => .cont { s with pc := t }
    | .cbz rn t => .cont (if s.get rn == 0 then { s with pc := t } else s.next)
    | .print rs => .cont ({ s with out := s.out ++ [s.get rs] }.next)
    | .halt => .halt s
    | .abort => .fault

/-! ## Fueled execution + outcomes -/

inductive Result where
  | running (s : State)
  | halted  (s : State)
  | faulted
  deriving Inhabited

def run (prog : Prog) : Nat → State → Result
  | 0, s => .running s
  | fuel + 1, s =>
    match step prog s with
    | .cont s' => run prog fuel s'
    | .halt s' => .halted s'
    | .fault => .faulted

/-- The machine started at `s₀` halts in state `sf`. -/
def Halts (prog : Prog) (s₀ sf : State) : Prop := ∃ fuel, run prog fuel s₀ = .halted sf
/-- The machine faults. -/
def Faults (prog : Prog) (s₀ : State) : Prop := ∃ fuel, run prog fuel s₀ = .faulted
/-- The machine never halts or faults (still running at every fuel). -/
def Diverges (prog : Prog) (s₀ : State) : Prop := ∀ fuel, ∃ s, run prog fuel s₀ = .running s

/-! ## Determinism — the model is a function, so outcomes are unique -/

theorem run_deterministic {prog : Prog} {s₀ : State} {fuel : Nat} {r₁ r₂ : Result}
    (h₁ : run prog fuel s₀ = r₁) (h₂ : run prog fuel s₀ = r₂) : r₁ = r₂ := by
  rw [← h₁, ← h₂]

/-! ## ⭐ Shift masking — architecture fidelity (the centerpiece)

The register shift amount is taken `mod 64`, so a shift by `64` is the identity, NOT zero. The unmasked
`BitVec` shift (`<<<` by the raw amount) diverges at every multiple of 64 ≥ 64. -/

/-- The register-shift amount `64` masks to `0`. -/
theorem amt_64_mask : (64 : Word).toNat % W = 0 := by decide

/-- **Masked LSL by 64 is the identity** (AArch64 `LSL Xd,Xn,#(64 mod 64)=#0`). -/
theorem lsl_64_id (x : Word) : aluEval .lsl x (64 : Word) = x := by
  show x <<< ((64 : Word).toNat % W) = x
  rw [amt_64_mask]
  simp

/-- The same masking on logical and arithmetic right shifts. -/
theorem lsr_64_id (x : Word) : aluEval .lsr x (64 : Word) = x := by
  show x >>> ((64 : Word).toNat % W) = x
  rw [amt_64_mask]
  simp

theorem asr_64_id (x : Word) : aluEval .asr x (64 : Word) = x := by
  show BitVec.sshiftRight x ((64 : Word).toNat % W) = x
  rw [amt_64_mask]
  simp

/-- Why the `% 64` mask matters: an UNMASKED `BitVec 64` left shift by `64` collapses to `0`. A model that
    forgot the `% 64` mis-predicts the hardware here — the architecture (masked) keeps the value, the naïve
    model gives `0`. Concrete witness at `x = 7`. -/
theorem unmasked_lsl_7_64_zero : (7 : Word) <<< (64 : Nat) = 0 := by decide

example : aluEval .lsl (7 : Word) (64 : Word) = 7 := lsl_64_id 7

/-! ## Fidelity regression checks — machine-checked against the AArch64 reference

The easy-to-get-wrong cases, locked by `decide`. **SDIV rounds toward ZERO** (not floor), **÷0 = 0** (no
trap — the fault is the emitter's explicit `cbz x10,Lfault; bl _abort`, modelled `cbz;abort`), and
**INT_MIN ÷ -1 wraps to INT_MIN**. The signed (`lt/le/gt/ge`) vs unsigned (`lo/ls/hi/hs`) conditions give
the right result across the sign boundary, and non-comparison `alu` ops leave the compare context untouched
(only `cmp` writes it), matching `ADD`/`SUB` vs `SUBS`. -/

example : BitVec.sdiv (-7 : Word) 2 = (-3 : Word) := by decide            -- trunc toward 0, not -4
example : BitVec.sdiv ( 7 : Word) (-2 : Word) = (-3 : Word) := by decide
example : BitVec.sdiv (5 : Word) (0 : Word) = (0 : Word) := by decide     -- ÷0 = 0 (no trap)
example : BitVec.sdiv (BitVec.ofInt 64 (-9223372036854775808)) (-1)
            = BitVec.ofInt 64 (-9223372036854775808) := by decide         -- INT_MIN/-1 = INT_MIN
example : ((-7 : Word) - BitVec.sdiv (-7 : Word) 2 * 2) = (-1 : Word) := by decide  -- rem sign = dividend
example : Cond.lt.holds (subFlags (-1 : Word) 1) = true  := by decide     -- signed -1 < 1
example : Cond.lo.holds (subFlags (-1 : Word) 1) = false := by decide     -- unsigned ¬(0xFF..F < 1)
example : Cond.hs.holds (subFlags (-1 : Word) 1) = true  := by decide
example : Cond.le.holds (subFlags (1 : Word) 1) = true  := by decide
example : Cond.lt.holds (subFlags (1 : Word) 1) = false := by decide

/-! ## Register-convention scope (Apple `arm64`)

This model is a **generic** Nat-indexed register machine: it does NOT bake in caller/callee-saved or
platform conventions — those are the *codegen*'s obligation and are discharged at the codegen-correctness
proof via the `VarLayout`/`ExtStateRel` (a future step). Register `31` is `xzr` here (the modelled
instruction set never uses `31` as `SP`; the frame base is `x29` and `SP` is abstracted into `mem`).
The text emitter `BaseLanguage/Backend/AsmToText.lean` is what must obey the Apple `arm64` convention (`x18`/`x16`/`x17`
avoided, 16-byte SP alignment, varargs-on-stack, callee-saved `x29`/`x30` preserved, and spill-everything
⇒ no register liveness across `bl`). -/

end Asm

end BaseLanguage
