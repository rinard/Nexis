-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMayCeil.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.fwdmayceil.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdMayCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure FwdMayCeil (P : Program) (fmc : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) (fmcT P) (fmc c.node), x ∈ fmcHi P c'.node → x ∈ fmc c'.node
  floor : ∀ n, ∀ x ∈ fmcLo P n, x ∈ fmc n
  check : ∀ n, ∀ x ∈ fmc n, x ∈ fmcHi P n
  seed : ∀ x ∈ (∅ : Exprs), x ∈ fmcHi P P.entry → x ∈ fmc P.entry
  within : ∀ n, (fmc n).Subset (allExprs P)

theorem fmc_iff_flow (P : Program) (h : Node → Exprs) :
    FwdMayCeil P h ↔ MTCSpecMFC P (listExpr P) (fmcT P) (fmcLo P) (fmcHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem fmcSol_valid (P : Program) (wf : WellFormed P) : FwdMayCeil P (fmcSol P) :=
  (fmc_iff_flow P _).mpr (fmc_correct P wf).1
theorem fmc_least (P : Program) (wf : WellFormed P) :
    ∀ g, FwdMayCeil P g → ∀ n, (fmcSol P n).Subset (g n) :=
  fun g hg n x hx => (fmc_correct P wf).2 g ((fmc_iff_flow P g).mp hg) n x hx

#assert_clean_axioms fmcSol_valid
#assert_clean_axioms fmc_least

end BaseLanguage.Analyses.FwdMayCeil
