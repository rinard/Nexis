-- Copyright (c) 2026 Martin Rinard
-- GENERATED from LCM.gsl by `lake exe gen` — do not edit.
import Generated.Seam.lcm.ValidExtremal
import BaseLanguage.Analysis.Augmented
import BaseLanguage.Meta.AxiomCheck
namespace BaseLanguage.Analyses.LCM
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std
set_option linter.unusedVariables false

/-! ## `πₐ` (`Anticipated`). -/

def πₐR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => ((π.sdiff (ue P c.node)).Subset π') ∧ (π.Subset ((ue P c.node).union (pass P c.node)))

theorem πₐ_drives (P : Program) (wf : WellFormed P) : Drives P (πₐR P) (πₐSol P) :=
  fun c c' hstep => ⟨(πₐSol_valid P wf).predict c c' hstep, (πₐSol_valid P wf).check c.node⟩

theorem πₐ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (πₐR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem πₐ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (πₐR P) ⟨c, πₐSol P c.node⟩ ⟨c', πₐSol P c'.node⟩ := progress (πₐ_drives P wf) hs

theorem πₐ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (πₐR P) ⟨c, πₐSol P c.node⟩ ⟨c', πₐSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (πₐR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (πₐ_drives P wf)

#assert_clean_axioms πₐ_drives
#assert_clean_axioms πₐ_progress

/-! ## `ηₐ` (`Available`). -/

def ηₐR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => π'.Subset ((de P c.node).union (π.inter (pass P c.node)))

theorem ηₐ_drives (P : Program) (wf : WellFormed P) : Drives P (ηₐR P) (ηₐSol P) :=
  fun c c' hstep => (ηₐSol_valid P wf).update c c' hstep

theorem ηₐ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (ηₐR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem ηₐ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (ηₐR P) ⟨c, ηₐSol P c.node⟩ ⟨c', ηₐSol P c'.node⟩ := progress (ηₐ_drives P wf) hs

theorem ηₐ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (ηₐR P) ⟨c, ηₐSol P c.node⟩ ⟨c', ηₐSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (ηₐR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (ηₐ_drives P wf)

#assert_clean_axioms ηₐ_drives
#assert_clean_axioms ηₐ_progress

/-! ## `ηₚ` (`Postponable`). -/

def ηₚR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => π'.Subset ((earliest P (πₐSol P) (ηₐSol P) c.node c'.node).union (π.sdiff (ue P c.node)))

theorem ηₚ_drives (P : Program) (wf : WellFormed P) : Drives P (ηₚR P) (ηₚSol P) :=
  fun c c' hstep => (ηₚSol_valid P wf).update c c' hstep

theorem ηₚ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (ηₚR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem ηₚ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (ηₚR P) ⟨c, ηₚSol P c.node⟩ ⟨c', ηₚSol P c'.node⟩ := progress (ηₚ_drives P wf) hs

theorem ηₚ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (ηₚR P) ⟨c, ηₚSol P c.node⟩ ⟨c', ηₚSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (ηₚR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (ηₚ_drives P wf)

#assert_clean_axioms ηₚ_drives
#assert_clean_axioms ηₚ_progress

/-! ## `τₚ` (`TauP`). -/

def τₚR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => Assignments.Subset π ((ηₚSol P) c'.node)

theorem τₚ_drives (P : Program) (wf : WellFormed P) : Drives P (τₚR P) (τₚSol P) :=
  fun c c' hstep => (τₚSol_valid P wf).predict c c' hstep

theorem τₚ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (τₚR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem τₚ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (τₚR P) ⟨c, τₚSol P c.node⟩ ⟨c', τₚSol P c'.node⟩ := progress (τₚ_drives P wf) hs

theorem τₚ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (τₚR P) ⟨c, τₚSol P c.node⟩ ⟨c', τₚSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (τₚR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (τₚ_drives P wf)

#assert_clean_axioms τₚ_drives
#assert_clean_axioms τₚ_progress

/-! ## `πᵤ` (`Used`). -/

def πᵤR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => (π'.Subset (π.union (((πᵤLatN P) c'.node).union ((πᵤLatE P) c.node c'.node)))) ∧ ((((ue P c.node).sdiff ((πᵤLatN P c.node)))).Subset π)

theorem πᵤ_drives (P : Program) (wf : WellFormed P) : Drives P (πᵤR P) (πᵤSol P) :=
  fun c c' hstep => ⟨(πᵤSol_valid P wf).predict c c' hstep, (πᵤSol_valid P wf).check c.node⟩

theorem πᵤ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (πᵤR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem πᵤ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (πᵤR P) ⟨c, πᵤSol P c.node⟩ ⟨c', πᵤSol P c'.node⟩ := progress (πᵤ_drives P wf) hs

theorem πᵤ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (πᵤR P) ⟨c, πᵤSol P c.node⟩ ⟨c', πᵤSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (πᵤR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (πᵤ_drives P wf)

#assert_clean_axioms πᵤ_drives
#assert_clean_axioms πᵤ_progress

/-! ## `τᵤ` (`UsedOut`). -/

def τᵤR (P : Program) : Config → Assignments → Config → Assignments → Prop :=
  fun c π c' π' => Assignments.Sup π ((πᵤSol P) c'.node)

theorem τᵤ_drives (P : Program) (wf : WellFormed P) : Drives P (τᵤR P) (τᵤSol P) :=
  fun c c' hstep => (τᵤSol_valid P wf).predict c c' hstep

theorem τᵤ_preservation (P : Program) (a a' : Aug Assignments) (h : AugStep P (τᵤR P) a a') :
    Step P a.cfg a'.cfg := preservation h

theorem τᵤ_progress (P : Program) (wf : WellFormed P) (c c' : Config) (hs : Step P c c') :
    AugStep P (τᵤR P) ⟨c, τᵤSol P c.node⟩ ⟨c', τᵤSol P c'.node⟩ := progress (τᵤ_drives P wf) hs

theorem τᵤ_bisim (P : Program) (wf : WellFormed P) :
    (∀ c c', Step P c c' → AugStep P (τᵤR P) ⟨c, τᵤSol P c.node⟩ ⟨c', τᵤSol P c'.node⟩) ∧
    (∀ a a' : Aug Assignments, AugStep P (τᵤR P) a a' → Step P a.cfg a'.cfg) :=
  bisim (τᵤ_drives P wf)

#assert_clean_axioms τᵤ_drives
#assert_clean_axioms τᵤ_progress

end BaseLanguage.Analyses.LCM
