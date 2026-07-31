-- Copyright (c) 2026 Martin Rinard
-- GENERATED from MaybeAssign.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import Generated.Solver.maybeassign.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.MaybeAssign
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure MaybeAssign (P : Program) (ma : Node → Vars) : Prop where
  update : ∀ c c', Step P c c' → ((genVars P c.node).union ((ma c.node).inter (transpGenVars P c.node))).Subset (ma c'.node)
  seed   : Vars.Subset (∅) (ma P.entry)
  within : ∀ n, (ma n).Subset (allGenVars P)

theorem ma_iff_flow (P : Program) (h : Node → Vars) :
    MaybeAssign P h ↔ MTCSpecMF P (listVar P) (maT P) (∅) h := by
  constructor
  · intro hs
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hs.update c c' hstep x hx
    · intro x hx; exact hs.seed x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mpr (hs.within n x hx)
  · intro hf
    refine ⟨?_, ?_, ?_⟩
    · intro c c' hstep x hx; exact hf.1 c c' hstep x hx
    · intro x hx; exact hf.2.1 x hx
    · intro n x hx; exact Std.HashSet.mem_toList.mp (hf.2.2 n x hx)

theorem maSol_valid (P : Program) (wf : WellFormed P) : MaybeAssign P (maSol P) :=
  (ma_iff_flow P _).mpr (ma_correct P wf).1
theorem ma_least (P : Program) (wf : WellFormed P) :
    ∀ g, MaybeAssign P g → ∀ n, (maSol P n).Subset (g n) :=
  fun g hg n x hx => (ma_correct P wf).2 g ((ma_iff_flow P g).mp hg) n x hx

#assert_clean_axioms maSol_valid
#assert_clean_axioms ma_least

end BaseLanguage.Analyses.MaybeAssign
