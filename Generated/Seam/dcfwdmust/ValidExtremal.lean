-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMust.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcfwdmust.DcFwdMustDefs
import analyses.dcfwdmust.DcFwdMustDefsSub
import Generated.Solver.dcfwdmust.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcFwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DcFwdMust (P : Program) (df : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ df c'.node, x ∈ MTC.evs (c.node, c'.node) (dfT P) (df c.node) ∨ x ∈ dfLo P c'.node
  floor : ∀ n, ∀ x ∈ dfLo P n, x ∈ df n
  check : ∀ n, ∀ x ∈ df n, x ∈ dfHi P n
  seed : ∀ x ∈ df P.entry, x ∈ (∅ : Exprs) ∨ x ∈ dfLo P P.entry
  within : ∀ n, (df n).Subset (allExprs P)

theorem df_iff_flow (P : Program) (h : Node → Exprs) :
    DcFwdMust P h ↔ MTCSpecC P (listExpr P) (dfT P) (dfLo P) (dfHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem dfSol_valid (P : Program) (wf : WellFormed P) : DcFwdMust P (dfSol P) :=
  (df_iff_flow P _).mpr (df_correct P wf).1
theorem df_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, DcFwdMust P g → ∀ n, (g n).Subset (dfSol P n) :=
  fun g hg n x hx => (df_correct P wf).2 g ((df_iff_flow P g).mp hg) n x hx

#assert_clean_axioms dfSol_valid
#assert_clean_axioms df_greatest

end BaseLanguage.Analyses.DcFwdMust
