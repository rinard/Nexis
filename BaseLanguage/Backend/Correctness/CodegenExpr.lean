-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Correctness.CodegenSim
import BaseLanguage.Backend.Correctness.CodegenCorrect
import BaseLanguage.IR.TAC

namespace BaseLanguage

/-!
# `CodegenExpr` — expression-eval correctness (item 1 of the forward simulation)

The model-stepping core for `CodegenForward`: small lemmas about `State` updates and a one-fuel `run`
step, then `loadAtom_correct` — running a `loadAtom` instruction leaves `encode (evalAtom σ a)` in the
target register, frame unchanged. This is the base case of the expression induction; the recursive
`emitExpr_correct` (una/bin over the `CodegenCorrect` ALU lemmas, incl. the div/mod `cbz` fall-through)
builds directly on it.
-/

namespace Asm

/-! ## State-update + single-step lemmas -/

theorem get_set_same (s : State) (r : Nat) (x : Word) (hr : r ≠ 31) : (s.set r x).get r = x := by
  simp [State.set, State.get, hr]

theorem get_set_ne (s : State) (r r' : Nat) (x : Word) (h : r' ≠ r) :
    (s.set r x).get r' = s.get r' := by
  simp only [State.set, State.get]
  split
  · rfl
  · split
    · rfl
    · simp [h]

theorem set_mem (s : State) (r : Nat) (x : Word) : (s.set r x).mem = s.mem := by
  simp only [State.set]; split <;> rfl

theorem set_pc (s : State) (r : Nat) (x : Word) : (s.set r x).pc = s.pc := by
  simp only [State.set]; split <;> rfl

theorem next_get (s : State) (r : Nat) : (s.next).get r = s.get r := by
  simp [State.next, State.get]

theorem next_mem (s : State) : (s.next).mem = s.mem := rfl
theorem next_pc (s : State) : (s.next).pc = s.pc + 1 := rfl

/-- One `cont` step peels one unit of fuel. -/
theorem run_one_cont {prog : Prog} {s s' : State} (n : Nat) (h : step prog s = .cont s') :
    run prog (n + 1) s = run prog n s' := by
  simp only [run, h]

end Asm

namespace TacToAsm

open Tac Semantics

/-- **`loadAtom` correctness (item-1 base case).** With the load instruction at the current pc and the
    frame holding the store, running one step leaves `encode (evalAtom σ a)` in register `r`, advancing the
    pc by one and leaving the frame untouched. -/
theorem loadAtom_correct {prog : Asm.Prog} {vs : List Var} {r : Nat} {a : Atom}
    {σ : Store} {s : Asm.State} (_hr : r ≠ 31)
    (hi : prog[s.pc]? = (loadAtom vs r a)[0]?)
    (hmem : ∀ v, s.mem (slot vs v) = encode (σ v)) :
    Asm.run prog 1 s = .running ((s.set r (encode (evalAtom σ a))).next) := by
  cases a with
  | var v =>
    have hi' : prog[s.pc]? = some (.ldrSlot r (slot vs v)) := hi
    have hstep : Asm.step prog s = .cont ((s.set r (encode (σ v))).next) := by
      simp only [Asm.step, hi', hmem v]
    rw [Asm.run_one_cont 0 hstep]
    rfl
  | imm n =>
    have hi' : prog[s.pc]? = some (.ldrImm r (encode n)) := hi
    have hstep : Asm.step prog s = .cont ((s.set r (encode n)).next) := by
      simp only [Asm.step, hi']
    rw [Asm.run_one_cont 0 hstep]
    rfl

end TacToAsm

end BaseLanguage
