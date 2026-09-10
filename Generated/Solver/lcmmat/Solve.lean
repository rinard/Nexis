-- Copyright (c) 2026 Martin Rinard
-- GENERATED from LcmMat.gsl by `lake exe gen` — do not edit.
import analyses.lcmmat.LcmMatDefs
import analyses.lcmmat.LcmMatDefsSub
import Solver
import Solver.Impl.Term
import Solver.Impl.Transfer
/-! The `Solve` target (7 ghost(s)). -/
namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

def listExpr (P : Program) : List Expr := (allExprs P).toList
theorem listExpr_nodup (P : Program) : (listExpr P).Nodup := (allExprs P).distinct_toList.imp (fun h => beq_eq_false_iff_ne.mp h)

def πₐT (P : Program) : MTC Expr :=
  .union (.const (fun (n, _) => ue P n)) (.inter .var (.const (fun (n, _) => pass P n)))
def πₐHi (P : Program) : Node → Assignments := fun n => (ue P n).union (pass P n)
def ηₐT (P : Program) : MTC Expr :=
  .union (.const (fun (n, _) => de P n)) (.inter .var (.const (fun (n, _) => pass P n)))
def ηₚT (P : Program) (πₐ ηₐ : Node → Assignments) : MTC Expr :=
  .union (.const (fun (n, n') => earliest P πₐ ηₐ n n')) (.diffc .var (fun (n, _) => ue P n))
def πᵤT (P : Program) (latN : Node → Assignments) (latE : Node → Node → Assignments) : MTC Expr :=
  .diffc .var (fun (n, n') => (latN n').union (latE n n'))
def πᵤLo (P : Program) (latN : Node → Assignments) : Node → Assignments := fun n => (ue P n).sdiff (latN n)
def ηₘT (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments) : MTC Expr :=
  .union (.const (fun (n, n') => matPlace P πₐ ηₐ ηₚ τₚ τᵤ n n')) (.diffc .var (fun (n, _) => notPass P n))
/-! ## Executable bundle — the memoized `solve` (one fixpoint Array per ghost). -/

def widthExpr (P : Program) : Nat := (listExpr P).length
abbrev BVExpr (P : Program) := BitVec (widthExpr P)
def decodeExpr (P : Program) (bv : BVExpr P) : Assignments := decode (listExpr P) bv
@[noinline] def decFExpr (P : Program) (f : Node → BVExpr P) : Node → Assignments := fun n => decodeExpr P (f n)

structure LcmMatBitvec (P : Program) where
  πₐ : Node → BVExpr P
  ηₐ : Node → BVExpr P
  ηₚ : Node → BVExpr P
  τₚ : Node → BVExpr P
  πᵤ : Node → BVExpr P
  τᵤ : Node → BVExpr P
  ηₘ : Node → BVExpr P

def solve (P : Program) : LcmMatBitvec P :=
  let arr_πₐ := solveMTCBM P (listExpr P) (πₐT P) (πₐHi P) (haltSeed P)
  let f_πₐ : Node → BVExpr P := fun n => if n < P.size then gA (arr_πₐ) n else encode (listExpr P) (πₐHi P n)
  let d_πₐ := decFExpr P f_πₐ
  let arr_ηₐ := solveMTC P (listExpr P) (ηₐT P) (entrySeed P)
  let f_ηₐ : Node → BVExpr P := fun n => (arr_ηₐ)[n]?.getD (topV (widthExpr P))
  let d_ηₐ := decFExpr P f_ηₐ
  let arr_ηₚ := solveMTC P (listExpr P) (ηₚT P (d_πₐ) (d_ηₐ)) (entrySeed P)
  let f_ηₚ : Node → BVExpr P := fun n => (arr_ηₚ)[n]?.getD (topV (widthExpr P))
  let d_ηₚ := decFExpr P f_ηₚ
  let f_τₚ : Node → BVExpr P := tMeet P (listExpr P) (f_ηₚ)
  let d_τₚ := decFExpr P f_τₚ
  let arr_πᵤ := solveMTCB P (listExpr P) (πᵤT P (latestNode P (d_ηₚ) (d_τₚ)) (latestEdge P (d_πₐ) (d_ηₐ) (d_ηₚ))) (πᵤLo P (latestNode P (d_ηₚ) (d_τₚ))) ∅
  let f_πᵤ : Node → BVExpr P := fun n => if n < P.size then gA (arr_πᵤ) n else encode (listExpr P) (πᵤLo P (latestNode P (d_ηₚ) (d_τₚ)) n)
  let d_πᵤ := decFExpr P f_πᵤ
  let f_τᵤ : Node → BVExpr P := tJoin P (listExpr P) (f_πᵤ)
  let d_τᵤ := decFExpr P f_τᵤ
  let arr_ηₘ := solveMTC P (listExpr P) (ηₘT P (d_πₐ) (d_ηₐ) (d_ηₚ) (d_τₚ) (d_τᵤ)) (entrySeed P)
  let f_ηₘ : Node → BVExpr P := fun n => (arr_ηₘ)[n]?.getD (topV (widthExpr P))
  { πₐ := f_πₐ, ηₐ := f_ηₐ, ηₚ := f_ηₚ, τₚ := f_τₚ, πᵤ := f_πᵤ, τᵤ := f_τᵤ, ηₘ := f_ηₘ }

theorem πₐWf (P : Program) : MTC.Wf (listExpr P) (πₐT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (ue_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (pass_sub P n x hx)⟩⟩
def πₐSol (P : Program) : Node → Assignments := decFExpr P (solve P).πₐ
theorem πₐ_correct (P : Program) (wf : WellFormed P) :
    MTCSpecBM P (listExpr P) (πₐT P) (πₐHi P) (haltSeed P) (πₐSol P) ∧
    ∀ h, MTCSpecBM P (listExpr P) (πₐT P) (πₐHi P) (haltSeed P) h → ∀ n, ∀ x ∈ h n, x ∈ πₐSol P n :=
  resMTCBM_correct (hi := πₐHi P) (sd := haltSeed P) wf (listExpr_nodup P) (πₐWf P) (fun x hx => Std.HashSet.mem_toList.mpr (haltSeed_sub P x hx))

theorem πₐSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (πₐSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((πₐ_correct P wf).1.2.2.2 n x hx)

theorem ηₐWf (P : Program) : MTC.Wf (listExpr P) (ηₐT P) :=
  ⟨fun (n, _) x hx => Std.HashSet.mem_toList.mpr (de_sub P n x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (pass_sub P n x hx)⟩⟩
def ηₐSol (P : Program) : Node → Assignments := decFExpr P (solve P).ηₐ
theorem ηₐ_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listExpr P) (ηₐT P) (entrySeed P) (ηₐSol P) ∧
    ∀ h, MTCSpec P (listExpr P) (ηₐT P) (entrySeed P) h → ∀ n, ∀ x ∈ h n, x ∈ ηₐSol P n :=
  resMTC_correct wf (listExpr_nodup P) (ηₐWf P) (fun x hx => Std.HashSet.mem_toList.mpr (entrySeed_sub P x hx))

theorem ηₐSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (ηₐSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((ηₐ_correct P wf).1.2.2 n x hx)

theorem ηₚWf (P : Program) (πₐ ηₐ : Node → Assignments) (hπₐ : ∀ n, (πₐ n).Subset (allExprs P)) (hηₐ : ∀ n, (ηₐ n).Subset (allExprs P)) : MTC.Wf (listExpr P) (ηₚT P πₐ ηₐ) :=
  ⟨fun (n, n') x hx => Std.HashSet.mem_toList.mpr (earliest_sub P πₐ ηₐ hπₐ hηₐ n n' x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (ue_sub P n x hx)⟩⟩
def ηₚSol (P : Program) : Node → Assignments := decFExpr P (solve P).ηₚ
theorem ηₚ_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listExpr P) (ηₚT P (πₐSol P) (ηₐSol P)) (entrySeed P) (ηₚSol P) ∧
    ∀ h, MTCSpec P (listExpr P) (ηₚT P (πₐSol P) (ηₐSol P)) (entrySeed P) h → ∀ n, ∀ x ∈ h n, x ∈ ηₚSol P n :=
  resMTC_correct wf (listExpr_nodup P) (ηₚWf P (πₐSol P) (ηₐSol P) (πₐSol_sub P wf) (ηₐSol_sub P wf)) (fun x hx => Std.HashSet.mem_toList.mpr (entrySeed_sub P x hx))

theorem ηₚSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (ηₚSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((ηₚ_correct P wf).1.2.2 n x hx)

def τₚSol (P : Program) : Node → Assignments := decFExpr P (solve P).τₚ
theorem τₚ_correct (P : Program) (wf : WellFormed P) :
    MeetSpec P (listExpr P) ((solve P).ηₚ) (τₚSol P) ∧
    ∀ σ, MeetSpec P (listExpr P) ((solve P).ηₚ) σ → ∀ n, ∀ x ∈ σ n, x ∈ τₚSol P n :=
  resMeet_correct (univ := listExpr P) wf (listExpr_nodup P) ((solve P).ηₚ)

theorem τₚSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (τₚSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((τₚ_correct P wf).1.2 n x hx)

theorem πᵤWf (P : Program) (latN : Node → Assignments) (latE : Node → Node → Assignments) (hlatN : ∀ n, (latN n).Subset (allExprs P)) (hlatE : ∀ i j, (latE i j).Subset (allExprs P)) : MTC.Wf (listExpr P) (πᵤT P latN latE) :=
  ⟨by trivial, fun (n, n') x hx => Std.HashSet.mem_toList.mpr (union_sub (hlatN n') (hlatE n n') x hx)⟩
def πᵤLatN (P : Program) : Node → Assignments := latestNode P (ηₚSol P) (τₚSol P)
def πᵤLatE (P : Program) : Node → Node → Assignments := latestEdge P (πₐSol P) (ηₐSol P) (ηₚSol P)
theorem πᵤLatN_sub (P : Program) (wf : WellFormed P) (n : Node) : (πᵤLatN P n).Subset (allExprs P) :=
  latestNode_sub P (ηₚSol P) (τₚSol P) (ηₚSol_sub P wf) (τₚSol_sub P wf) n
theorem πᵤLatE_sub (P : Program) (wf : WellFormed P) (i j : Node) : (πᵤLatE P i j).Subset (allExprs P) :=
  latestEdge_sub P (πₐSol P) (ηₐSol P) (ηₚSol P) (πₐSol_sub P wf) (ηₐSol_sub P wf) (ηₚSol_sub P wf) i j
def πᵤSol (P : Program) : Node → Assignments := decFExpr P (solve P).πᵤ
theorem πᵤ_correct (P : Program) (wf : WellFormed P) :
    MTCSpecB P (listExpr P) (πᵤT P (πᵤLatN P) (πᵤLatE P)) (πᵤLo P (πᵤLatN P)) ∅ (πᵤSol P) ∧
    ∀ h, MTCSpecB P (listExpr P) (πᵤT P (πᵤLatN P) (πᵤLatE P)) (πᵤLo P (πᵤLatN P)) ∅ h → ∀ n, ∀ x ∈ πᵤSol P n, x ∈ h n :=
  resMTCB_correct (lo := πᵤLo P (πᵤLatN P)) (sd := ∅) wf (listExpr_nodup P)
    (πᵤWf P (πᵤLatN P) (πᵤLatE P) (πᵤLatN_sub P wf) (πᵤLatE_sub P wf))
    (fun n x hx => Std.HashSet.mem_toList.mpr (ue_sub P n x (Assignments.mem_sdiff.mp hx).1))
    (fun x hx => absurd hx Std.HashSet.not_mem_empty)

theorem πᵤSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (πᵤSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((πᵤ_correct P wf).1.2.2.2 n x hx)

def τᵤSol (P : Program) : Node → Assignments := decFExpr P (solve P).τᵤ
theorem τᵤ_correct (P : Program) (wf : WellFormed P) :
    JoinSpec P (listExpr P) ((solve P).πᵤ) (τᵤSol P) ∧
    ∀ σ, JoinSpec P (listExpr P) ((solve P).πᵤ) σ → ∀ n, ∀ x ∈ τᵤSol P n, x ∈ σ n :=
  resJoin_correct (univ := listExpr P) wf (listExpr_nodup P) ((solve P).πᵤ)

theorem τᵤSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (τᵤSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((τᵤ_correct P wf).1.2 n x hx)

theorem ηₘWf (P : Program) (πₐ ηₐ ηₚ τₚ τᵤ : Node → Assignments) (hπₐ : ∀ n, (πₐ n).Subset (allExprs P)) (hηₐ : ∀ n, (ηₐ n).Subset (allExprs P)) (hηₚ : ∀ n, (ηₚ n).Subset (allExprs P)) (hτₚ : ∀ n, (τₚ n).Subset (allExprs P)) (hτᵤ : ∀ n, (τᵤ n).Subset (allExprs P)) : MTC.Wf (listExpr P) (ηₘT P πₐ ηₐ ηₚ τₚ τᵤ) :=
  ⟨fun (n, n') x hx => Std.HashSet.mem_toList.mpr (matPlace_sub P πₐ ηₐ ηₚ τₚ τᵤ hπₐ hηₐ hηₚ hτₚ hτᵤ n n' x hx), ⟨by trivial, fun (n, _) x hx => Std.HashSet.mem_toList.mpr (notPass_sub P n x hx)⟩⟩
def ηₘSol (P : Program) : Node → Assignments := decFExpr P (solve P).ηₘ
theorem ηₘ_correct (P : Program) (wf : WellFormed P) :
    MTCSpec P (listExpr P) (ηₘT P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P)) (entrySeed P) (ηₘSol P) ∧
    ∀ h, MTCSpec P (listExpr P) (ηₘT P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P)) (entrySeed P) h → ∀ n, ∀ x ∈ h n, x ∈ ηₘSol P n :=
  resMTC_correct wf (listExpr_nodup P) (ηₘWf P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P) (πₐSol_sub P wf) (ηₐSol_sub P wf) (ηₚSol_sub P wf) (τₚSol_sub P wf) (τᵤSol_sub P wf)) (fun x hx => Std.HashSet.mem_toList.mpr (entrySeed_sub P x hx))

theorem ηₘSol_sub (P : Program) (wf : WellFormed P) (n : Node) : (ηₘSol P n).Subset (allExprs P) :=
  fun x hx => Std.HashSet.mem_toList.mp ((ηₘ_correct P wf).1.2.2 n x hx)

end BaseLanguage.Analyses.LcmMat
