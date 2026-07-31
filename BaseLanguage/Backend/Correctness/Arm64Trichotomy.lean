-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Asm

namespace BaseLanguage

/-!
# `Arm64Trichotomy` — the AArch64 model's behaviour is exactly {halts, diverges, faults}

Self-contained facts about `Asm.run` (a deterministic, total function), used to convert a *forward*
codegen simulation into the *backward* refinement (asm ⟹ ast). The three outcomes are **exhaustive**
(`outcome_exhaustive` — property 4) and **mutually exclusive**, and the halting state is **unique**. The
exclusions ride a one-line **stability** lemma: once `run` reports a terminal, more fuel doesn't change it.
-/

namespace Asm

/-! ## Stability: terminals are preserved by extra fuel -/

theorem run_halt_succ {prog : Prog} {sf : State} :
    ∀ (f : Nat) (s : State), run prog f s = .halted sf → run prog (f + 1) s = .halted sf := by
  intro f
  induction f with
  | zero => intro s h; simp [run] at h
  | succ k ih =>
    intro s h
    simp only [run] at h ⊢
    cases hstep : step prog s with
    | cont s' => simp only [hstep] at h ⊢; exact ih s' h
    | halt s' => simp only [hstep] at h ⊢; exact h
    | fault => simp only [hstep] at h; exact Result.noConfusion h

theorem run_fault_succ {prog : Prog} :
    ∀ (f : Nat) (s : State), run prog f s = .faulted → run prog (f + 1) s = .faulted := by
  intro f
  induction f with
  | zero => intro s h; simp [run] at h
  | succ k ih =>
    intro s h
    simp only [run] at h ⊢
    cases hstep : step prog s with
    | cont s' => simp only [hstep] at h ⊢; exact ih s' h
    | halt s' => simp only [hstep] at h; exact Result.noConfusion h
    | fault => simp only []

theorem run_halt_mono {prog : Prog} {sf : State} {f : Nat} {s : State}
    (h : run prog f s = .halted sf) : ∀ k, run prog (f + k) s = .halted sf := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact run_halt_succ (f + k) s ih

theorem run_fault_mono {prog : Prog} {f : Nat} {s : State}
    (h : run prog f s = .faulted) : ∀ k, run prog (f + k) s = .faulted := by
  intro k
  induction k with
  | zero => exact h
  | succ k ih => exact run_fault_succ (f + k) s ih

/-! ## Property 4 — the behaviour is one of the three -/

/-- **Every modelled program halts, diverges, or faults** (no fourth "stuck" outcome). -/
theorem outcome_exhaustive (prog : Prog) (s₀ : State) :
    (∃ sf, Halts prog s₀ sf) ∨ Diverges prog s₀ ∨ Faults prog s₀ := by
  apply Classical.byContradiction
  intro hcon
  apply hcon
  refine Or.inr (Or.inl ?_)
  intro fuel
  cases hr : run prog fuel s₀ with
  | running s => exact ⟨s, rfl⟩
  | halted sf => exact absurd (Or.inl ⟨sf, fuel, hr⟩) hcon
  | faulted => exact absurd (Or.inr (Or.inr ⟨fuel, hr⟩)) hcon

/-! ## Mutual exclusion + uniqueness (for the forward→backward conversion) -/

theorem halts_not_diverges {prog : Prog} {s₀ sf : State}
    (hh : Halts prog s₀ sf) (hd : Diverges prog s₀) : False := by
  obtain ⟨fuel, hf⟩ := hh
  obtain ⟨s, hr⟩ := hd fuel
  rw [hf] at hr; exact Result.noConfusion hr

theorem faults_not_diverges {prog : Prog} {s₀ : State}
    (hf : Faults prog s₀) (hd : Diverges prog s₀) : False := by
  obtain ⟨fuel, hff⟩ := hf
  obtain ⟨s, hr⟩ := hd fuel
  rw [hff] at hr; exact Result.noConfusion hr

theorem halts_not_faults {prog : Prog} {s₀ sf : State}
    (hh : Halts prog s₀ sf) (hf : Faults prog s₀) : False := by
  obtain ⟨f₁, h₁⟩ := hh
  obtain ⟨f₂, h₂⟩ := hf
  have e₁ := run_halt_mono h₁ f₂
  have e₂ := run_fault_mono h₂ f₁
  rw [Nat.add_comm] at e₂
  rw [e₁] at e₂; exact Result.noConfusion e₂

theorem halts_unique {prog : Prog} {s₀ sf₁ sf₂ : State}
    (h₁ : Halts prog s₀ sf₁) (h₂ : Halts prog s₀ sf₂) : sf₁ = sf₂ := by
  obtain ⟨f₁, e₁⟩ := h₁
  obtain ⟨f₂, e₂⟩ := h₂
  have a₁ := run_halt_mono e₁ f₂
  have a₂ := run_halt_mono e₂ f₁
  rw [Nat.add_comm] at a₂
  rw [a₁] at a₂; exact Result.halted.inj a₂

end Asm

end BaseLanguage
