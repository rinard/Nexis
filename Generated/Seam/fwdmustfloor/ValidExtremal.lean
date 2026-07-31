-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdMustFloor.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.fwdmustfloor.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdMustFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure FwdMustFloor (P : Program) (fmf : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ fmf c'.node, x ∈ MTC.evs (c.node, c'.node) (fmfT P) (fmf c.node) ∨ x ∈ fmfLo P c'.node
  floor : ∀ n, ∀ x ∈ fmfLo P n, x ∈ fmf n
  check : ∀ n, ∀ x ∈ fmf n, x ∈ fmfHi P n
  seed : ∀ x ∈ fmf P.entry, x ∈ (∅ : Exprs) ∨ x ∈ fmfLo P P.entry
  within : ∀ n, (fmf n).Subset (allExprs P)

theorem fmf_iff_flow (P : Program) (h : Node → Exprs) :
    FwdMustFloor P h ↔ MTCSpecC P (listExpr P) (fmfT P) (fmfLo P) (fmfHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem fmfSol_valid (P : Program) (wf : WellFormed P) : FwdMustFloor P (fmfSol P) :=
  (fmf_iff_flow P _).mpr (fmf_correct P wf).1
theorem fmf_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, FwdMustFloor P g → ∀ n, (g n).Subset (fmfSol P n) :=
  fun g hg n x hx => (fmf_correct P wf).2 g ((fmf_iff_flow P g).mp hg) n x hx

#assert_clean_axioms fmfSol_valid
#assert_clean_axioms fmf_greatest

end BaseLanguage.Analyses.FwdMustFloor
