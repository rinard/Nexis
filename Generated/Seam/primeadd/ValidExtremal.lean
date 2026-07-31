-- Copyright (c) 2026 Martin Rinard
-- GENERATED from PrimeAdd.gsl by `lake exe gen` — do not edit.
import BaseLanguage.IR.Locals
import BaseLanguage.IR.LocalsSub
import analyses.primeadd.PrimeAddDefs
import analyses.primeadd.PrimeAddDefsSub
import Generated.Solver.primeadd.Solve
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.PrimeAdd
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std BaseLanguage.Tac.Locals
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

structure PrimeAdd (P : Program) (g : Node → Defs) : Prop where
  update : ∀ c c', Step P c c' → Defs.Subset ((((((g c.node)).union (obsGen P c.node))).union ((((MTC.gatherS (allDefs P) (fun z => below P c.node z) (g c.node))).filter (fun y => ((if (g c.node).toList.any (fun w => (primes P c.node).contains w) then allDefs P else (∅ : Defs))).contains y))))) (g c'.node)
  seed   : Defs.Subset (∅) (g P.entry)
  within : ∀ n, (g n).Subset (allDefs P)

theorem g_iff_flow (P : Program) (h : Node → Defs) :
    PrimeAdd P h ↔ MTCSpecMF P (listNode P) (gT P) (∅) h := by
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

theorem gSol_valid (P : Program) (wf : WellFormed P) : PrimeAdd P (gSol P) :=
  (g_iff_flow P _).mpr (g_correct P wf).1
theorem g_least (P : Program) (wf : WellFormed P) :
    ∀ g, PrimeAdd P g → ∀ n, (gSol P n).Subset (g n) :=
  fun g hg n x hx => (g_correct P wf).2 g ((g_iff_flow P g).mp hg) n x hx

#assert_clean_axioms gSol_valid
#assert_clean_axioms g_least

end BaseLanguage.Analyses.PrimeAdd
