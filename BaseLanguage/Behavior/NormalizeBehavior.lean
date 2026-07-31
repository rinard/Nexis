-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Sim
import BaseLanguage.Behavior.Outcomes

namespace BaseLanguage
namespace Normalize

open Tac Semantics

/-!
# `Behavior/NormalizeBehavior.lean` — the normal-form pre-passes preserve fault & divergence

`normalize = prependEntry ∘ deDeg ∘ normalizeSelfRead`. Each pass is an IR→IR
**plus-simulation**: one source step is matched by ≥ 1 target steps to the *same successor node*,
re-establishing a store relation (identity for two passes, `AgreeF` — agreement off fresh temps —
for `normalizeSelfRead`). This module discharges the `StepSim` + fault-reflection obligations of the
generic engine `Behavior.Outcomes.{diverges,faultSteps}_of_stepsim`, and composes the three into
`normalize_preserves_diverge` / `normalize_preserves_faultSteps`. Nothing under `Normalize/` is edited —
this file only *uses* the audited `step_lift_*` / fetch lemmas.
-/

/-! ## `deDeg` — degenerate `ifz x z z` ↦ `noop z` (store-preserving, node-preserving) -/

variable {P : Program}

theorem deDeg_stepSim : StepSim P (deDeg P) (fun σT σ => σT = σ) := by
  intro c d σT _ hR hstep; subst hR
  exact ⟨d, d.store, step_lift_deDeg hstep, Steps.refl, rfl⟩

theorem deDeg_faultRefl {cf : Config} {σT : Store}
    (_ : cf.node < P.size) (hR : σT = cf.store) (hflt : Faulting P cf) :
    ∃ cf', Steps (deDeg P) ⟨cf.node, σT⟩ cf' ∧ Faulting (deDeg P) cf' := by
  subst hR; obtain ⟨x, e, next, hf, hev⟩ := hflt
  exact ⟨⟨cf.node, cf.store⟩, Steps.refl, x, e, next, by rw [deDeg_fetch, hf]; simp [deDegCmd], hev⟩

/-! ## `prependEntry` — fresh `noop` entry; old nodes verbatim -/

theorem prependEntry_stepSim : StepSim P (prependEntry P) (fun σT σ => σT = σ) := by
  intro c d σT hlt hR hstep; subst hR
  exact ⟨d, d.store, step_lift_prepend hlt hstep, Steps.refl, rfl⟩

theorem prependEntry_faultRefl {cf : Config} {σT : Store}
    (hlt : cf.node < P.size) (hR : σT = cf.store) (hflt : Faulting P cf) :
    ∃ cf', Steps (prependEntry P) ⟨cf.node, σT⟩ cf' ∧ Faulting (prependEntry P) cf' := by
  subst hR; obtain ⟨x, e, next, hf, hev⟩ := hflt
  exact ⟨⟨cf.node, cf.store⟩, Steps.refl, x, e, next, by rw [prependEntry_fetch_lt hlt]; exact hf, hev⟩

/-! ## `normalizeSelfRead` — split a self-reading compute through a fresh temp (`AgreeF` threading) -/

theorem selfread_stepSim :
    StepSim P (normalizeSelfRead P (freshN P)) (fun σT σ => AgreeF P σT σ) := by
  intro c d σT hlt hag hstep
  obtain ⟨σT', hsteps, hagf⟩ := selfread_step_sim hlt hag hstep
  -- selfread_step_sim already yields the ≥ 1-step run to `⟨d.node, σT'⟩`; re-expose its leading step.
  cases hstep with
  | @assign nd σ x e next v hf hv =>
      have hev : eval σT e = some v := by rw [eval_agree_at hag hf]; exact hv
      by_cases hsr : (isNumbered e && exprReadsVar e x) = true
      · rw [Bool.and_eq_true] at hsr
        have hmem : nd ∈ selfNodes P := mem_selfNodes_of P hlt hf hsr.1 hsr.2
        have hstep1 : Step (normalizeSelfRead P (freshN P))
            ⟨nd, σT⟩ ⟨normLabel P nd, σT.update (freshN P nd) v⟩ :=
          Step.assign (norm_fetch_self hmem hf) hev
        have hev2 : eval (σT.update (freshN P nd) v) (.atom (.var (freshN P nd))) = some v := by
          show some ((σT.update (freshN P nd) v) (freshN P nd)) = some v; rw [upd_self]
        have hstep2 : Step (normalizeSelfRead P (freshN P))
            ⟨normLabel P nd, σT.update (freshN P nd) v⟩
            ⟨next, (σT.update (freshN P nd) v).update x v⟩ :=
          Step.assign (norm_fetch_copy hmem hf) hev2
        refine ⟨_, (σT.update (freshN P nd) v).update x v, hstep1, steps_single hstep2, ?_⟩
        intro w hw
        show ((σT.update (freshN P nd) v).update x v) w = (σ.update x v) w
        by_cases hwx : w = x
        · subst hwx; rw [upd_self, upd_self]
        · rw [upd_ne hwx, upd_ne (hw nd), upd_ne hwx]; exact hag w hw
      · have hns : nd ∉ selfNodes P := by
          intro hmem
          obtain ⟨_, x', e', next', hf', hnum', hrd'⟩ := mem_selfNodes P hmem
          have heq : Cmd.assign x e next = .assign x' e' next' := Option.some.inj (hf.symm.trans hf')
          injection heq with hx he hn; subst hx; subst he; subst hn
          exact hsr (by rw [Bool.and_eq_true]; exact ⟨hnum', hrd'⟩)
        refine ⟨_, σT.update x v, Step.assign (norm_fetch_nonself hlt hns hf) hev, Steps.refl, ?_⟩
        intro w hw
        show (σT.update x v) w = (σ.update x v) w
        by_cases hwx : w = x
        · subst hwx; rw [upd_self, upd_self]
        · rw [upd_ne hwx, upd_ne hwx]; exact hag w hw
  | @ifzT nd σ x z nz hf hz =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      have hzt : σT x = 0 := by rw [hag x (read_nonfresh hf (by simp [instrUsedVars]))]; exact hz
      exact ⟨_, σT, Step.ifzT (norm_fetch_nonself hlt hns hf) hzt, Steps.refl, hag⟩
  | @ifzF nd σ x z nz hf hz =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      have hzt : σT x ≠ 0 := by rw [hag x (read_nonfresh hf (by simp [instrUsedVars]))]; exact hz
      exact ⟨_, σT, Step.ifzF (norm_fetch_nonself hlt hns hf) hzt, Steps.refl, hag⟩
  | @noop nd σ next hf =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      exact ⟨_, σT, Step.noop (norm_fetch_nonself hlt hns hf), Steps.refl, hag⟩

theorem selfread_faultRefl {cf : Config} {σT : Store}
    (hlt : cf.node < P.size) (hag : AgreeF P σT cf.store) (hflt : Faulting P cf) :
    ∃ cf', Steps (normalizeSelfRead P (freshN P)) ⟨cf.node, σT⟩ cf' ∧
      Faulting (normalizeSelfRead P (freshN P)) cf' := by
  obtain ⟨x, e, next, hf, hev⟩ := hflt
  have hev' : eval σT e = none := by rw [eval_agree_at hag hf]; exact hev
  by_cases hsr : (isNumbered e && exprReadsVar e x) = true
  · rw [Bool.and_eq_true] at hsr
    have hmem : cf.node ∈ selfNodes P := mem_selfNodes_of P hlt hf hsr.1 hsr.2
    exact ⟨⟨cf.node, σT⟩, Steps.refl, freshN P cf.node, e, normLabel P cf.node,
      norm_fetch_self hmem hf, hev'⟩
  · have hns : cf.node ∉ selfNodes P := by
      intro hmem
      obtain ⟨_, x', e', next', hf', hnum', hrd'⟩ := mem_selfNodes P hmem
      have heq : Cmd.assign x e next = .assign x' e' next' := Option.some.inj (hf.symm.trans hf')
      injection heq with hx he hn; subst hx; subst he; subst hn
      exact hsr (by rw [Bool.and_eq_true]; exact ⟨hnum', hrd'⟩)
    exact ⟨⟨cf.node, σT⟩, Steps.refl, x, e, next, norm_fetch_nonself hlt hns hf, hev'⟩

/-! ## Per-pass divergence / fault preservation -/

theorem deDeg_preserves_diverge (hwf : WellFormed P) {σ : Store}
    (hd : Diverges P ⟨P.entry, σ⟩) : Diverges (deDeg P) ⟨(deDeg P).entry, σ⟩ := by
  rw [deDeg_entry]; exact diverges_of_stepsim deDeg_stepSim hwf hwf.entry_lt rfl hd

theorem selfread_preserves_diverge (hwf : WellFormed P) {σ : Store}
    (hd : Diverges P ⟨P.entry, σ⟩) :
    Diverges (normalizeSelfRead P (freshN P))
      ⟨(normalizeSelfRead P (freshN P)).entry, σ⟩ :=
  diverges_of_stepsim selfread_stepSim hwf hwf.entry_lt AgreeF.rfl' hd

theorem prependEntry_preserves_diverge (hwf : WellFormed P) {σ : Store}
    (hd : Diverges P ⟨P.entry, σ⟩) :
    Diverges (prependEntry P) ⟨(prependEntry P).entry, σ⟩ := by
  have hcore := diverges_of_stepsim prependEntry_stepSim hwf hwf.entry_lt rfl hd
  rw [prependEntry_entry]
  exact diverges_step_back (step1_next_iff.mpr (Step.noop (prependEntry_fetch_size P))) hcore

theorem deDeg_preserves_faultSteps (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hs : Steps P ⟨P.entry, σ⟩ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps (deDeg P) ⟨(deDeg P).entry, σ⟩ cf' ∧ Faulting (deDeg P) cf' := by
  rw [deDeg_entry]
  exact faultSteps_of_stepsim deDeg_stepSim hwf deDeg_faultRefl hwf.entry_lt rfl hs hflt

theorem selfread_preserves_faultSteps (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hs : Steps P ⟨P.entry, σ⟩ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps (normalizeSelfRead P (freshN P))
        ⟨(normalizeSelfRead P (freshN P)).entry, σ⟩ cf' ∧
      Faulting (normalizeSelfRead P (freshN P)) cf' :=
  faultSteps_of_stepsim selfread_stepSim hwf selfread_faultRefl hwf.entry_lt AgreeF.rfl' hs hflt

theorem prependEntry_preserves_faultSteps (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hs : Steps P ⟨P.entry, σ⟩ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps (prependEntry P) ⟨(prependEntry P).entry, σ⟩ cf' ∧ Faulting (prependEntry P) cf' := by
  obtain ⟨cf', hcf', hflt'⟩ :=
    faultSteps_of_stepsim prependEntry_stepSim hwf prependEntry_faultRefl hwf.entry_lt rfl hs hflt
  refine ⟨cf', ?_, hflt'⟩
  rw [prependEntry_entry]
  exact steps_trans (steps_single (Step.noop (prependEntry_fetch_size P))) hcf'

/-! ## Composition — `normalize` preserves divergence and faults -/

/-- **`normalize` preserves divergence.** -/
theorem normalize_preserves_diverge (hwf : WellFormed P) {σ : Store}
    (hd : Diverges P ⟨P.entry, σ⟩) : Diverges (normalize P) ⟨(normalize P).entry, σ⟩ := by
  have hwf1 : WellFormed (normalizeSelfRead P (freshN P)) := normalize_wellFormed P (freshN P) hwf
  have hwf2 : WellFormed (deDeg (normalizeSelfRead P (freshN P))) := deDeg_wellFormed _ hwf1
  show Diverges (prependEntry (deDeg (normalizeSelfRead P (freshN P))))
        ⟨(prependEntry (deDeg (normalizeSelfRead P (freshN P)))).entry, σ⟩
  exact prependEntry_preserves_diverge hwf2
    (deDeg_preserves_diverge hwf1 (selfread_preserves_diverge hwf hd))

/-- **`normalize` preserves faults** (in composable `Steps`-into-`Faulting` form). -/
theorem normalize_preserves_faultSteps (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hs : Steps P ⟨P.entry, σ⟩ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps (normalize P) ⟨(normalize P).entry, σ⟩ cf' ∧ Faulting (normalize P) cf' := by
  have hwf1 : WellFormed (normalizeSelfRead P (freshN P)) := normalize_wellFormed P (freshN P) hwf
  have hwf2 : WellFormed (deDeg (normalizeSelfRead P (freshN P))) := deDeg_wellFormed _ hwf1
  obtain ⟨cf1, hs1, hflt1⟩ := selfread_preserves_faultSteps hwf hs hflt
  obtain ⟨cf2, hs2, hflt2⟩ := deDeg_preserves_faultSteps hwf1 hs1 hflt1
  show ∃ cf', Steps (prependEntry (deDeg (normalizeSelfRead P (freshN P))))
        ⟨(prependEntry (deDeg (normalizeSelfRead P (freshN P)))).entry, σ⟩ cf'
      ∧ Faulting (prependEntry (deDeg (normalizeSelfRead P (freshN P)))) cf'
  exact prependEntry_preserves_faultSteps hwf2 hs2 hflt2

end Normalize
end BaseLanguage
