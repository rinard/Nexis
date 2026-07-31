-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PDCE.gsl by `lake exe gen` — do not edit.
import analyses.pdce.PdceDefs
import analyses.pdce.PdceDefsSub
import Solver
import Solver.Impl.Term
/-! The `Solve` target (2 ghost(s)). -/
namespace BaseLanguage.Analyses.PDCE
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listVar (P : Program) : List Var := (allVars P).toList
theorem listVar_nodup (P : Program) : (listVar P).Nodup := (allVars P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def listAsgn (P : Program) : List Asgn := (allAsgns P).toList
theorem listAsgn_nodup (P : Program) : (listAsgn P).Nodup := (allAsgns P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def πT (P : Program) : MTC Var :=
  .union (.gate (fun (n, _) => defVars P n) (fun (n, _) => rhsVars P n)) (.diffc .var (fun (n, _) => defVars P n))
def ηT (P : Program) : MTC Asgn :=
  .union (.const (fun (n, _) => born P n)) (.inter .var (.const (fun (n, _) => pass P n)))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthVar (P : Program) : Nat := (listVar P).length
abbrev BVVar (P : Program) := BitVec (widthVar P)
def decodeVar (P : Program) (bv : BVVar P) : Variables := decode (listVar P) bv
@[noinline] def decFVar (P : Program) (f : Node → BVVar P) : Node → Variables := fun n => decodeVar P (f n)

def widthAsgn (P : Program) : Nat := (listAsgn P).length
abbrev BVAsgn (P : Program) := BitVec (widthAsgn P)
def decodeAsgn (P : Program) (bv : BVAsgn P) : Assignments := decode (listAsgn P) bv
@[noinline] def decFAsgn (P : Program) (f : Node → BVAsgn P) : Node → Assignments := fun n => decodeAsgn P (f n)

structure PDCEBitvec (P : Program) where
  π : Node → BVVar P
  η : Node → BVAsgn P

def solve (P : Program) : PDCEBitvec P :=
  let arr_π := solveMTCB P (listVar P) (πT P) (condVars P) (liveSeed P)
  let f_π : Node → BVVar P := fun n => if n < P.size then gA (arr_π) n else encode (listVar P) ((condVars P) n)
  let arr_η := solveMTC P (listAsgn P) (ηT P) (sinkSeed P)
  let f_η : Node → BVAsgn P := fun n => (arr_η)[n]?.getD (topV (widthAsgn P))
  { π := f_π, η := f_η }

theorem πWf (P : Program) : MTC.Wf (listVar P) (πT P) :=
  ⟨⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx), fun (n, _) x hx => Std.HashSet.mem_toList.mpr (rhsVars_sub P n x hx)⟩, ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (defVars_sub P n x hx)⟩⟩
def πSol (P : Program) : Node → Variables := decFVar P (solve P).π
theorem π_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listVar P) (πT P) (condVars P) (liveSeed P) (πSol P) ∧
    ∀ h, MTCSpecB P (listVar P) (πT P) (condVars P) (liveSeed P) h → ∀ n, ∀ x ∈ πSol P n, x ∈ h n :=
  resMTCB_correct (lo := condVars P) (sd := liveSeed P) wf (listVar_nodup P) (πWf P)
    (fun n x hx => Std.HashSet.mem_toList.mpr (condVars_sub P n x hx))
    (fun x hx => Std.HashSet.mem_toList.mpr (liveSeed_sub P x hx))

theorem ηWf (P : Program) : MTC.Wf (listAsgn P) (ηT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (born_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (pass_sub P n x hx)⟩⟩
def ηSol (P : Program) : Node → Assignments := decFAsgn P (solve P).η
theorem η_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listAsgn P) (ηT P) (sinkSeed P) (ηSol P) ∧
    ∀ h, MTCSpec P (listAsgn P) (ηT P) (sinkSeed P) h → ∀ n, ∀ x ∈ h n, x ∈ ηSol P n :=
  resMTC_correct wf (listAsgn_nodup P) (ηWf P) (fun x hx => Std.HashSet.mem_toList.mpr (sinkSeed_sub P x hx))

end BaseLanguage.Analyses.PDCE
