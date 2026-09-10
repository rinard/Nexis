-- Copyright (c) 2026 Martin Rinard
import Seam.pdce.Adapter
import Seam.pdcefault.Adapter
import BaseLanguage.PDCE.Divergence
import BaseLanguage.PDCE.FaultPreservation

/-!
# `PDCE.Mode` — selecting between the two verified PDCE modes

| mode             | halt | faults        | divergence | sinks / eliminates            |
|------------------|------|---------------|------------|-------------------------------|
| `classic`        | ✅   | **not** preserved | ✅      | every assignment              |
| `preserveFaults` | ✅   | ✅            | ✅         | all but possibly-faulting ones |

`runPdce_safe_preserves_all` states the `preserveFaults` row as a single theorem: all three outcomes of the
base language are preserved, halting runs together with their observable store.

Unlike LCM's two modes — which re-aim one field of *one* solved bundle — PDCE's two modes run **two
analyses**. The reason is structural, and worth stating plainly: LCM's fix only ever *removes* insertions,
a subset operation, and every `Anticipated`/`Sink` clause is an upper bound, so filtering a ghost preserves
validity for free. PDCE's fix must additionally *keep* a computation the classical analysis would delete,
and evaluating it correctly requires its operands to be live — a **lower** bound on `π`, which is a least
fixpoint. A lower bound cannot be imposed by filtering; it makes the solution grow. Hence
`analyses/pdcefault/PdceFault.gsl`: the classical specification with its liveness floor widened from
`condVars` to `condVars ∪ faultingRhsVars`, and nothing else changed.

The classical mode keeps faint liveness and its full elimination power; the fault-preserving mode pays for
fault preservation in optimization strength, on exactly the programs that can fault.
-/

namespace BaseLanguage.Analyses.PDCE
open BaseLanguage.Tac BaseLanguage.Semantics

/-- Which PDCE mode the compiler runs. -/
inductive PdceMode where
  /-- The classical KRS sinking transform. Faults are out of scope. -/
  | classic
  /-- Sink and eliminate only fault-free assignments, so faults are preserved. -/
  | preserveFaults
  deriving DecidableEq, Repr, Inhabited

def PdceMode.ofString? : String → Option PdceMode
  | "classic" | "krs"               => some .classic
  | "safe" | "preserve-faults"      => some .preserveFaults
  | _                               => none

def PdceMode.name : PdceMode → String
  | .classic        => "classic"
  | .preserveFaults => "preserve-faults"

/-- The bundle a mode runs with. `classic` is the classical solver; `preserveFaults` is the solver for the
    widened-floor analysis, with its sinking filter aimed at `Expr.faultFree`. -/
def PdceMode.spec (mode : PdceMode) (P : Program) (wf : WellFormed P) : PdceSpec P :=
  match mode with
  | .classic        => pdceSolved P wf
  | .preserveFaults => pdceFaultSolved P wf

/-- **The mode-selecting PDCE pass.** -/
def runPdce (mode : PdceMode) (P : Program) (wf : WellFormed P) : Program :=
  transform P (mode.spec P wf)

theorem runPdce_wellFormed (mode : PdceMode) (P : Program) (wf : WellFormed P) :
    WellFormed (runPdce mode P wf) := transform_wellFormed (mode.spec P wf) wf

/-- **Both modes preserve halting behavior** — one instance of `transform_preserves_halt`, which holds for
    any valid bundle whatever its filter. -/
theorem runPdce_preserves_halt (mode : PdceMode) {P : Program} (wf : WellFormed P)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f) :
    ∃ d_f, Steps (runPdce mode P wf) ⟨(runPdce mode P wf).entry, σ⟩ d_f
         ∧ Final (runPdce mode P wf) d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v :=
  transform_preserves_halt (mode.spec P wf) wf hrun hfin

/-- **Both modes preserve divergence.** -/
theorem runPdce_preserves_diverges (mode : PdceMode) {P : Program} (wf : WellFormed P)
    {σ : Store} (hdiv : Diverges P ⟨P.entry, σ⟩) :
    Diverges (runPdce mode P wf) ⟨(runPdce mode P wf).entry, σ⟩ :=
  transform_preserves_diverges (mode.spec P wf) wf hdiv

/-- **The fault-preserving mode preserves faults.** The `keep`-only-fault-free hypothesis is discharged by
    the bundle itself, so this is unconditional in the mode: for every program and every store, a faulting
    source run gives a faulting transformed run. -/
theorem runPdce_preserves_faulting {P : Program} (wf : WellFormed P)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfault : Faulting P c_f) :
    ∃ df, Steps (runPdce .preserveFaults P wf) ⟨blockOff P (pdceFaultSolved P wf) P.entry, σ⟩ df
        ∧ Faulting (runPdce .preserveFaults P wf) df :=
  transform_preserves_faulting (pdceFaultSolved P wf) wf
    (pdceFaultSolved_keep_faultFree P wf) hrun hfault

/-- **The fault-preserving mode preserves every outcome the semantics can produce.** The dual of
    `LCM.runLcm_safe_preserves_all`: halting with the observable store, faulting, and divergence. The
    classical mode has the first and third conjuncts but not the second — it can sink a faulting
    assignment past a branch, or delete it outright when its result is faintly dead. -/
theorem runPdce_safe_preserves_all {P : Program} (wf : WellFormed P) {σ : Store} :
    let T := runPdce .preserveFaults P wf
    (∀ c_f, Steps P ⟨P.entry, σ⟩ c_f → Final P c_f →
        ∃ d_f, Steps T ⟨T.entry, σ⟩ d_f ∧ Final T d_f ∧ ∀ v ∈ P.obs, d_f.store v = c_f.store v)
  ∧ (∀ c_f, Steps P ⟨P.entry, σ⟩ c_f → Faulting P c_f →
        ∃ df, Steps T ⟨T.entry, σ⟩ df ∧ Faulting T df)
  ∧ (Diverges P ⟨P.entry, σ⟩ → Diverges T ⟨T.entry, σ⟩) :=
  ⟨fun _ hrun hfin => runPdce_preserves_halt _ wf hrun hfin,
   fun _ hrun hflt => runPdce_preserves_faulting wf hrun hflt,
   fun hdiv => runPdce_preserves_diverges _ wf hdiv⟩

end BaseLanguage.Analyses.PDCE
