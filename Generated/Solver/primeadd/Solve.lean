-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PrimeAdd.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.primeadd.PrimeAddDefs
import analyses.primeadd.PrimeAddDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.PrimeAdd
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def gT (P : Program) : MTC Node :=
  .union (.union .var (.const (fun (n, _) => obsGen P n))) (.inter (.gather (allDefs P) (fun (n, _) z => below P n z)) (.gate (fun (n, _) => primes P n) (fun (n, _) => allDefs P)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure PrimeAddBitvec (P : Program) where
  g : Node → BVNode P

def solve (P : Program) : PrimeAddBitvec P :=
  let arr_g := solveMTCMF P (listNode P) (gT P) (∅)
  let f_g : Node → BVNode P := fun n => if n < P.size then gA (arr_g) n else 0
  { g := f_g }

theorem gWf (P : Program) : MTC.Wf (listNode P) (gT P) :=
  ⟨⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (obsGen_sub P n x hx)⟩, ⟨fun x hx => Std.HashSet.mem_toList.mpr hx, ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (primes_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (allDefs_sub P x hx)⟩⟩⟩
def gSol (P : Program) : Node → Defs := decFNode P (solve P).g
theorem g_correct (P : Program) (wf : WellFormed P) :
    MTCSpecMF P (listNode P) (gT P) (∅) (gSol P) ∧
    ∀ h, MTCSpecMF P (listNode P) (gT P) (∅) h → ∀ n, ∀ x ∈ gSol P n, x ∈ h n :=
  resMTCMF_correct wf (listNode_nodup P) (gWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.PrimeAdd
