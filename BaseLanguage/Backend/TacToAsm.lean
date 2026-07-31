-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.Backend.Asm

namespace BaseLanguage

/-!
# `TacToAsm` (namespace `TacToAsm`) — the TAC→ARM64 translation into the verified `Asm` model

Lowers the IR (`Program`) to `Asm.Prog` (modelled AArch64 instructions), the target of the
operational semantics in `BaseLanguage/Backend/Asm.lean`. It produces *modelled* instructions, so its
correctness is a simulation theorem (`BaseLanguage/Backend/Correctness/CodegenForward.lean`,
`codegen_simulates`) rather than review. A thin
**unverified** printer (`BaseLanguage/Backend/AsmToText.lean`) turns the modelled program into assembler text
for `clang`.

## Layout — fixed-size blocks (chosen for verifiability)

Each IR node `i` compiles to a **fixed `B`-instruction block** at model pc `i*B`, padded with unreachable
`abort`s. So `nodePc i = i*B` is trivially injective and branch targets are `succ*B` — no prefix-sum
bookkeeping. A dedicated fault block at `numNodes*B` (an `abort`) is the `div`/`mod`-by-zero trap target,
matching the IR's `Faulting`. Storage is spill-everything: each `Var` lives in frame slot
`slotOff` (defined here; reused by the text backend), and `encode = Int64.toBitVec` (a `BitVec 64`
homomorphism — verified in `CodegenCorrect`), so the model ALU matches `Binop.denote`.
-/

namespace TacToAsm

open Tac Semantics

/-! ## Variable layout (frame slots)

Spill-everything storage shared by the code generator and the text backend: each `Var` gets an
8-byte frame slot at `[x29, #(16 + 8·idx)]`, above the saved `fp`/`lr`. `collectVars` fixes the
order (instructions in code order, then `obs`), so `slotOff` is a stable index. -/

def memV (vs : List Var) (v : Var) : Bool := vs.any (fun u => decide (u = v))
def addVar (vs : List Var) (v : Var) : List Var := if memV vs v then vs else vs ++ [v]
def idxV (vs : List Var) (v : Var) : Nat := vs.findIdx (fun u => decide (u = v))
def slotOff (vs : List Var) (v : Var) : Nat := 16 + 8 * idxV vs v

def atomVars (vs : List Var) : Atom → List Var
  | .var v => addVar vs v
  | .imm _ => vs
def exprVars (vs : List Var) : Expr → List Var
  | .atom a    => atomVars vs a
  | .una _ a   => atomVars vs a
  | .bin _ a b => atomVars (atomVars vs a) b
def instrVars (vs : List Var) : Cmd → List Var
  | .assign x e _ => exprVars (addVar vs x) e
  | .ifz x _ _    => addVar vs x
  | .noop _       => vs
  | .halt         => vs
def collectVars (P : Program) : List Var :=
  P.obs.foldl addVar (P.code.toList.foldl instrVars [])

/-- Fixed block size: ≥ the longest single-node block (`mod` = 7 instrs). -/
def B : Nat := 8

/-- Variable→frame-slot byte offset. -/
abbrev slot (vs : List Var) (v : Var) : Nat := slotOff vs v

/-- The IR value `↔` machine word: `Int64` *is* a `BitVec 64`. -/
@[inline] def encode (n : Val) : Asm.Word := n.toBitVec

/-- Load an atom into register `r`. -/
def loadAtom (vs : List Var) (r : Nat) : Atom → List Asm.Cmd
  | .var v => [.ldrSlot r (slot vs v)]
  | .imm n => [.ldrImm r (encode n)]

def unArm : Unop → List Asm.Cmd
  | .neg => [.neg 9 9]
  | .not => [.mvn 9 9]

/-- Binop on `x9` (left) / `x10` (right) → `x9`. `div`/`mod` guard the divisor with `cbz → faultPc`. -/
def binArm (faultPc : Nat) : Binop → List Asm.Cmd
  | .add  => [.alu .add 9 9 10]
  | .sub  => [.alu .sub 9 9 10]
  | .mul  => [.alu .mul 9 9 10]
  | .div  => [.cbz 10 faultPc, .alu .sdiv 9 9 10]
  | .mod  => [.cbz 10 faultPc, .alu .sdiv 11 9 10, .msub 9 11 10 9]
  | .and  => [.alu .and_ 9 9 10]
  | .or   => [.alu .orr 9 9 10]
  | .xor  => [.alu .eor 9 9 10]
  | .shl  => [.alu .lsl 9 9 10]
  | .lshr => [.alu .lsr 9 9 10]
  | .ashr => [.alu .asr 9 9 10]
  | .eq   => [.cmp 9 10, .cset 9 .eq]
  | .ne   => [.cmp 9 10, .cset 9 .ne]
  | .lt   => [.cmp 9 10, .cset 9 .lt]
  | .le   => [.cmp 9 10, .cset 9 .le]
  | .ltu  => [.cmp 9 10, .cset 9 .lo]
  | .leu  => [.cmp 9 10, .cset 9 .ls]

/-- Evaluate an expression into `x9`. -/
def emitExpr (vs : List Var) (faultPc : Nat) : Expr → List Asm.Cmd
  | .atom a    => loadAtom vs 9 a
  | .una op a  => loadAtom vs 9 a ++ unArm op
  | .bin op a b => loadAtom vs 9 a ++ loadAtom vs 10 b ++ binArm faultPc op

/-- The real instructions of node `i`'s block (before padding). -/
def blockFor (vs : List Var) (faultPc : Nat) : Cmd → List Asm.Cmd
  | .assign x e next => emitExpr vs faultPc e ++ [.strSlot 9 (slot vs x), .b (next * B)]
  | .ifz x a b       => [.ldrSlot 9 (slot vs x), .cbz 9 (a * B), .b (b * B)]
  | .noop next       => [.b (next * B)]
  | .halt            => [.halt]

/-- Pad a block to exactly `B` instructions with unreachable `abort`s. -/
def pad (l : List Asm.Cmd) : List Asm.Cmd :=
  l ++ List.replicate (B - l.length) .abort

/-- **The code generator.** `numNodes` fixed-size blocks + a trailing fault block. -/
def codegen (P : Program) : Asm.Prog :=
  let vs := collectVars P
  let n := P.code.size
  let faultPc := n * B
  let body := (List.range n).flatMap (fun i => pad (blockFor vs faultPc (P.code[i]!)))
  (body ++ pad [.abort]).toArray

/-! ## Initial machine state for an IR store -/

/-- The frame initialised so each var's slot holds its `encode`d value; pc at the entry block. -/
def initState (P : Program) (σ : Store) : Asm.State :=
  let vs := collectVars P
  { regs := fun _ => 0
    mem := fun off =>
      match vs.find? (fun v => slot vs v == off) with
      | some v => encode (σ v)
      | none   => 0
    flags := default, out := [], pc := P.entry * B }

end TacToAsm

end BaseLanguage
