-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcFwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcfwdmay.DcFwdMayDefs
import analyses.dcfwdmay.DcFwdMayDefsSub
import Generated.Solver.dcfwdmay.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcFwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DcFwdMay (P : Program) (dm : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) (dmT P) (dm c.node), x ∈ dmHi P c'.node → x ∈ dm c'.node
  floor : ∀ n, ∀ x ∈ dmLo P n, x ∈ dm n
  check : ∀ n, ∀ x ∈ dm n, x ∈ dmHi P n
  seed : ∀ x ∈ (∅ : Exprs), x ∈ dmHi P P.entry → x ∈ dm P.entry
  within : ∀ n, (dm n).Subset (allExprs P)

theorem dm_iff_flow (P : Program) (h : Node → Exprs) :
    DcFwdMay P h ↔ MTCSpecMFC P (listExpr P) (dmT P) (dmLo P) (dmHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem dmSol_valid (P : Program) (wf : WellFormed P) : DcFwdMay P (dmSol P) :=
  (dm_iff_flow P _).mpr (dm_correct P wf).1
theorem dm_least (P : Program) (wf : WellFormed P) :
    ∀ g, DcFwdMay P g → ∀ n, (dmSol P n).Subset (g n) :=
  fun g hg n x hx => (dm_correct P wf).2 g ((dm_iff_flow P g).mp hg) n x hx

#assert_clean_axioms dmSol_valid
#assert_clean_axioms dm_least

end BaseLanguage.Analyses.DcFwdMay
