-- Copyright (c) 2026 Martin Rinard
-- GENERATED from DcBwdMust.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.dcbwdmust.DcBwdMustDefs
import analyses.dcbwdmust.DcBwdMustDefsSub
import Generated.Solver.dcbwdmust.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.DcBwdMust
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure DcBwdMust (P : Program) (db : Node → Exprs) : Prop where
  predict : ∀ c c', Step P c c' → ∀ x ∈ db c.node, x ∈ MTC.evs (c.node, c'.node) (dbT P) (db c'.node) ∨ x ∈ dbLo P c.node
  floor : ∀ n, ∀ x ∈ dbLo P n, x ∈ db n
  check : ∀ n, ∀ x ∈ db n, x ∈ dbHi P n
  seed : ∀ c : Config, P.fetch c.node = some .halt → ∀ x ∈ db c.node, x ∈ (∅ : Exprs) ∨ x ∈ dbLo P c.node
  within : ∀ n, (db n).Subset (allExprs P)

theorem db_iff_flow (P : Program) (h : Node → Exprs) :
    DcBwdMust P h ↔ MTCSpecBMC P (listExpr P) (dbT P) (dbLo P) (dbHi P) (∅) h := by
  constructor
  · intro hs
    exact ⟨hs.predict, hs.floor, hs.check, hs.seed, fun n x hx => Std.HashSet.mem_toList.mpr (hs.within n x hx)⟩
  · intro hf
    exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, fun n x hx => Std.HashSet.mem_toList.mp (hf.2.2.2.2 n x hx)⟩

theorem dbSol_valid (P : Program) (wf : WellFormed P) : DcBwdMust P (dbSol P) :=
  (db_iff_flow P _).mpr (db_correct P wf).1
theorem db_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, DcBwdMust P g → ∀ n, (g n).Subset (dbSol P n) :=
  fun g hg n x hx => (db_correct P wf).2 g ((db_iff_flow P g).mp hg) n x hx

#assert_clean_axioms dbSol_valid
#assert_clean_axioms db_greatest

end BaseLanguage.Analyses.DcBwdMust
