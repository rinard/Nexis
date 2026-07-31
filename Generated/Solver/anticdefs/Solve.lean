-- Copyright (c) 2026 Martin Rinard
-- GENERATED from AnticDefs.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.AnticDefs
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def anticT (P : Program) : MTC Node :=
  .union (.const (fun (n, _) => genDefs P n)) (.inter .var (.const (fun (n, _) => transpDefs P n)))
def anticHi (P : Program) : Node → Defs := fun n => (genDefs P n).union (transpDefs P n)
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure AnticDefsBitvec (P : Program) where
  antic : Node → BVNode P

def solve (P : Program) : AnticDefsBitvec P :=
  let arr_antic := solveMTCBM P (listNode P) (anticT P) (anticHi P) (∅)
  let f_antic : Node → BVNode P := fun n => if n < P.size then gA (arr_antic) n else encode (listNode P) (anticHi P n)
  { antic := f_antic }

theorem anticWf (P : Program) : MTC.Wf (listNode P) (anticT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genDefs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpDefs_sub P n x hx)⟩⟩
def anticSol (P : Program) : Node → Defs := decFNode P (solve P).antic
theorem antic_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBM P (listNode P) (anticT P) (anticHi P) (∅) (anticSol P) ∧
    ∀ h, MTCSpecBM P (listNode P) (anticT P) (anticHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ anticSol P n :=
  resMTCBM_correct (hi := anticHi P) (sd := ∅) wf (listNode_nodup P) (anticWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.AnticDefs
