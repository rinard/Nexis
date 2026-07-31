-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdCeil.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.fwdceil.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdCeil
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure FwdCeil (P : Program) (fc : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ fc c'.node, x ∈ MTC.evs (c.node, c'.node) (fcT P) (fc c.node) ∨ x ∈ fcLo P c'.node
  floor : ∀ n, ∀ x ∈ fcLo P n, x ∈ fc n
  check : ∀ n, ∀ x ∈ fc n, x ∈ fcHi P n
  seed : ∀ x ∈ fc P.entry, x ∈ (∅ : Exprs) ∨ x ∈ fcLo P P.entry
  within : ∀ n, (fc n).Subset (allExprs P)

theorem fc_iff_flow (P : Program) (h : Node → Exprs) :
    FwdCeil P h ↔ MTCSpecC P (listExpr P) (fcT P) (fcLo P) (fcHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem fcSol_valid (P : Program) (wf : WellFormed P) : FwdCeil P (fcSol P) :=
  (fc_iff_flow P _).mpr (fc_correct P wf).1
theorem fc_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, FwdCeil P g → ∀ n, (g n).Subset (fcSol P n) :=
  fun g hg n x hx => (fc_correct P wf).2 g ((fc_iff_flow P g).mp hg) n x hx

#assert_clean_axioms fcSol_valid
#assert_clean_axioms fc_greatest

end BaseLanguage.Analyses.FwdCeil
