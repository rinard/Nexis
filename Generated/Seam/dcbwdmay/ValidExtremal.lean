-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMay.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcbwdmay.DcBwdMayDefs
import analyses.dcbwdmay.DcBwdMayDefsSub
import Generated.Solver.dcbwdmay.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcBwdMay
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DcBwdMay (P : Program) (dy : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) (dyT P) (dy c'.node), x ∈ dyHi P c.node → x ∈ dy c.node
  floor : ∀ n, ∀ x ∈ dyLo P n, x ∈ dy n
  check : ∀ n, ∀ x ∈ dy n, x ∈ dyHi P n
  seed : ∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ (∅ : Exprs), x ∈ dyHi P c.node → x ∈ dy c.node
  within : ∀ n, (dy n).Subset (allExprs P)

theorem dy_iff_flow (P : Program) (h : Node → Exprs) :
    DcBwdMay P h ↔ MTCSpecBC P (listExpr P) (dyT P) (dyLo P) (dyHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem dySol_valid (P : Program) (wf : WellFormed P) : DcBwdMay P (dySol P) :=
  (dy_iff_flow P _).mpr (dy_correct P wf).1
theorem dy_least (P : Program) (wf : WellFormed P) :
    ∀ g, DcBwdMay P g → ∀ n, (dySol P n).Subset (g n) :=
  fun g hg n x hx => (dy_correct P wf).2 g ((dy_iff_flow P g).mp hg) n x hx

#assert_clean_axioms dySol_valid
#assert_clean_axioms dy_least

end BaseLanguage.Analyses.DcBwdMay
