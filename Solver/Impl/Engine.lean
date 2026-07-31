-- Copyright (c) 2026 Martin Rinard
import Solver.Impl.Core

/-!
# `Solver.Impl.Engine` — the naive Kleene fixpoint primitives

The raw whole-array Jacobi/Kleene engine `solveMust`/`solveMay` (and the `top`/`bot`
seeds), parameterized by a transfer `g`. Chosen for verifiability; the efficient worklist
(`Solver/Impl/Worklist.lean`) is proven **equal** to it, so all correctness transfers by rewrite.
-/

namespace Solver

open BaseLanguage Tac Semantics

variable {n : Nat}

/-! ## Seeds and the staged solve -/

def topSeed (P : Program) : Array (ESet n) := Array.ofFn (n := P.size) (fun _ => topV n)
def botSeed (P : Program) : Array (ESet n) := Array.ofFn (n := P.size) (fun _ => 0)

theorem topSeed_size (P : Program) : (topSeed P : Array (ESet n)).size = P.size := Array.size_ofFn
theorem botSeed_size (P : Program) : (botSeed P : Array (ESet n)).size = P.size := Array.size_ofFn

def solveMust (P : Program) (g : Array (ESet n) → Node → ESet n) : Array (ESet n) :=
  iterToFix (mustStep P g) (measM P (topSeed P : Array (ESet n)) + 1) (topSeed P)

def solveMay (P : Program) (g : Array (ESet n) → Node → ESet n) : Array (ESet n) :=
  iterToFix (mayStep P g) (measV P (botSeed P : Array (ESet n)) + 1) (botSeed P)

/-- The must-solution has the right length and is a genuine fixpoint of its round operator. -/
theorem solveMust_size (P : Program) (g : Array (ESet n) → Node → ESet n) :
    (solveMust P g).size = P.size :=
  iterToFix_invariant (mustStep P g) (fun a => a.size = P.size)
    (fun x _ => mustStep_size P g x) _ _ (topSeed_size P)

theorem solveMust_fixed (P : Program) (g : Array (ESet n) → Node → ESet n) :
    mustStep P g (solveMust P g) = solveMust P g :=
  iterToFix_fixed' (mustStep P g) (fun a => a.size = P.size) (measM P)
    (fun x _ => mustStep_size P g x)
    (fun _ hx hne => measM_lt hx hne)
    _ (topSeed P) (topSeed_size P) (Nat.lt_succ_self _)

theorem solveMay_size (P : Program) (g : Array (ESet n) → Node → ESet n) :
    (solveMay P g).size = P.size :=
  iterToFix_invariant (mayStep P g) (fun a => a.size = P.size)
    (fun x _ => mayStep_size P g x) _ _ (botSeed_size P)

theorem solveMay_fixed (P : Program) (g : Array (ESet n) → Node → ESet n) :
    mayStep P g (solveMay P g) = solveMay P g :=
  iterToFix_fixed' (mayStep P g) (fun a => a.size = P.size) (measV P)
    (fun x _ => mayStep_size P g x)
    (fun _ hx hne => measV_lt hx hne)
    _ (botSeed P) (botSeed_size P) (Nat.lt_succ_self _)

/-! ## Per-node fixpoint equations -/

theorem solveMust_eq (P : Program) (g : Array (ESet n) → Node → ESet n) {nd : Node}
    (h : nd < P.size) :
    gA (solveMust P g) nd = gA (solveMust P g) nd &&& g (solveMust P g) nd := by
  have hf := solveMust_fixed P g
  calc gA (solveMust P g) nd
      = gA (mustStep P g (solveMust P g)) nd := by rw [hf]
    _ = gA (solveMust P g) nd &&& g (solveMust P g) nd := gA_step_must h

theorem solveMay_eq (P : Program) (g : Array (ESet n) → Node → ESet n) {nd : Node}
    (h : nd < P.size) :
    gA (solveMay P g) nd = gA (solveMay P g) nd ||| g (solveMay P g) nd := by
  have hf := solveMay_fixed P g
  calc gA (solveMay P g) nd
      = gA (mayStep P g (solveMay P g)) nd := by rw [hf]
    _ = gA (solveMay P g) nd ||| g (solveMay P g) nd := gA_step_may h

end Solver
