-- Copyright (c) 2026 Martin Rinard
import Generated.Seam.constprop.ValidExtremal
import BaseLanguage.Pass.BranchFold
import BaseLanguage.Pass.ConstFold
/-!
# `generated/constprop/Adapter.lean` — instantiate the abstract `CPSpec` from the solver.

The sole point where branch-folding meets the generated constant-propagation solver. The generator emits
the clean clause predicate `ConstProp` + `cpSol_valid` + `cp_greatest` (in `constprop.ValidExtremal`,
via `cp_iff_flow`); `BranchFold.CPValid` is that predicate up to binder-explicitness, so the bridge is a
one-liner. Everything about branch-folding runs on the abstract `CPSpec` and never touches the solver.
-/
namespace BaseLanguage.Analyses.ConstProp
open BaseLanguage Tac Tac.Locals Semantics Pass Std

variable {P : Program}

/-- `ConstProp` (generated) ⟹ `CPValid` (the abstract clause predicate). -/
def cpValidOf {cp : Node → ConstPairs} (h : ConstProp P cp) : Pass.BranchFold.CPValid P cp where
  update := fun {_ _} hs => h.update _ _ hs
  seed   := h.seed
  within := h.within

/-- …and back, so the generated `cp_greatest` (over `ConstProp`) supplies `CPSpec.greatest`. -/
def cpClausesOf {cp : Node → ConstPairs} (h : Pass.BranchFold.CPValid P cp) : ConstProp P cp where
  update := fun _ _ hs => h.update hs
  seed   := h.seed
  within := h.within

/-- **The constant-propagation solution as an abstract `CPSpec`.** The only solver-dependent definition. -/
def cpSpec (P : Program) (wf : WellFormed P) : Pass.BranchFold.CPSpec P where
  sol      := cpSol P
  valid    := cpValidOf (cpSol_valid P wf)
  greatest := fun g hg => cp_greatest P wf g (cpClausesOf hg)

/-! ## The concrete branch-fold pass + its verification. -/

/-- **Branch-folding**, on the generated constant-propagation solution. -/
def branchFold (P : Program) (wf : WellFormed P) : Program := Pass.BranchFold.run P (cpSpec P wf)

theorem branchFold_wellFormed (wf : WellFormed P) : WellFormed (branchFold P wf) :=
  Pass.BranchFold.run_wellFormed (cpSpec P wf) wf

theorem branchFold_preserves_halt (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (branchFold P wf) ⟨(branchFold P wf).entry, σ⟩ df ∧ Final (branchFold P wf) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v :=
  Pass.BranchFold.preserves_halt (cpSpec P wf) hrun hfin

theorem branchFold_preserves_faults (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (branchFold P wf) ⟨(branchFold P wf).entry, σ⟩ df ∧ Faulting (branchFold P wf) df :=
  Pass.BranchFold.preserves_faults (cpSpec P wf) hrun hfault

theorem branchFold_preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (branchFold P wf) ⟨(branchFold P wf).entry, σ⟩ :=
  Pass.BranchFold.preserves_diverges (cpSpec P wf) wf hdiv

@[simp] theorem branchFold_entry (wf : WellFormed P) : (branchFold P wf).entry = P.entry := rfl
@[simp] theorem branchFold_obs (wf : WellFormed P) : (branchFold P wf).obs = P.obs := rfl

/-! ## Const-folding (the alternation) — substitute known constants into RHSs, then fold. -/

/-- **Const-folding**, on the generated constant-propagation solution. -/
def constFold (P : Program) (wf : WellFormed P) : Program := Pass.ConstFold.run P (cpSpec P wf)

theorem constFold_wellFormed (wf : WellFormed P) : WellFormed (constFold P wf) :=
  Pass.ConstFold.run_wellFormed (cpSpec P wf) wf

theorem constFold_preserves_halt (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (constFold P wf) ⟨(constFold P wf).entry, σ⟩ df ∧ Final (constFold P wf) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v :=
  Pass.ConstFold.preserves_halt (cpSpec P wf) hrun hfin

theorem constFold_preserves_faults (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (constFold P wf) ⟨(constFold P wf).entry, σ⟩ df ∧ Faulting (constFold P wf) df :=
  Pass.ConstFold.preserves_faults (cpSpec P wf) hrun hfault

theorem constFold_preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (constFold P wf) ⟨(constFold P wf).entry, σ⟩ :=
  Pass.ConstFold.preserves_diverges (cpSpec P wf) wf hdiv

@[simp] theorem constFold_entry (wf : WellFormed P) : (constFold P wf).entry = P.entry := rfl
@[simp] theorem constFold_obs (wf : WellFormed P) : (constFold P wf).obs = P.obs := rfl

end BaseLanguage.Analyses.ConstProp
