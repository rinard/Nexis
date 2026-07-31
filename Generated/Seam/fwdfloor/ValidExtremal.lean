-- Copyright (c) 2026 Martin Rinard
-- GENERATED from FwdFloor.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.fwdfloor.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.FwdFloor
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure FwdFloor (P : Program) (ff : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ MTC.evs (c.node, c'.node) (ffT P) (ff c.node), x ∈ ffHi P c'.node → x ∈ ff c'.node
  floor : ∀ n, ∀ x ∈ ffLo P n, x ∈ ff n
  check : ∀ n, ∀ x ∈ ff n, x ∈ ffHi P n
  seed : ∀ x ∈ (∅ : Exprs), x ∈ ffHi P P.entry → x ∈ ff P.entry
  within : ∀ n, (ff n).Subset (allExprs P)

theorem ff_iff_flow (P : Program) (h : Node → Exprs) :
    FwdFloor P h ↔ MTCSpecMFC P (listExpr P) (ffT P) (ffLo P) (ffHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem ffSol_valid (P : Program) (wf : WellFormed P) : FwdFloor P (ffSol P) :=
  (ff_iff_flow P _).mpr (ff_correct P wf).1
theorem ff_least (P : Program) (wf : WellFormed P) :
    ∀ g, FwdFloor P g → ∀ n, (ffSol P n).Subset (g n) :=
  fun g hg n x hx => (ff_correct P wf).2 g ((ff_iff_flow P g).mp hg) n x hx

#assert_clean_axioms ffSol_valid
#assert_clean_axioms ff_least

end BaseLanguage.Analyses.FwdFloor
