-- Copyright (c) 2026 Martin Rinard
-- GENERATED from BwdChain.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.bwdchain.BwdChainDefs
import analyses.bwdchain.BwdChainDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (1 ghost(s)). -/
namespace BaseLanguage.Analyses.BwdChain
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listNode (P : Program) : List Node := (allDefs P).toList
theorem listNode_nodup (P : Program) : (listNode P).Nodup := (allDefs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def gT (P : Program) : MTC Node :=
  .union (.union (.const (fun (n, _) => genDefs P n)) (.inter .var (.const (fun (n, _) => transpDefs P n)))) (.const (fun (n, _) => extraN P n))
def gHi (P : Program) : Node → Defs := fun n => ceilN P n
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthNode (P : Program) : Nat := (listNode P).length
abbrev BVNode (P : Program) := BitVec (widthNode P)
def decodeNode (P : Program) (bv : BVNode P) : Defs := decode (listNode P) bv
@[noinline] def decFNode (P : Program) (f : Node → BVNode P) : Node → Defs := fun n => decodeNode P (f n)

structure BwdChainBitvec (P : Program) where
  g : Node → BVNode P

def solve (P : Program) : BwdChainBitvec P :=
  let arr_g := solveMTCBM P (listNode P) (gT P) (gHi P) (∅)
  let f_g : Node → BVNode P := fun n => if n < P.size then gA (arr_g) n else encode (listNode P) (gHi P n)
  { g := f_g }

theorem gWf (P : Program) : MTC.Wf (listNode P) (gT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (genDefs_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (transpDefs_sub P n x hx)⟩⟩, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (extraN_sub P n x hx)⟩
def gSol (P : Program) : Node → Defs := decFNode P (solve P).g
theorem g_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBM P (listNode P) (gT P) (gHi P) (∅) (gSol P) ∧
    ∀ h, MTCSpecBM P (listNode P) (gT P) (gHi P) (∅) h → ∀ n, ∀ x ∈ h n, x ∈ gSol P n :=
  resMTCBM_correct (hi := gHi P) (sd := ∅) wf (listNode_nodup P) (gWf P) (fun x hx => absurd hx Std.HashSet.not_mem_empty)

end BaseLanguage.Analyses.BwdChain
