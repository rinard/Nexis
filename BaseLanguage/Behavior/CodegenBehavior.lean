-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Correctness.CodegenForward
import BaseLanguage.Backend.Correctness.Arm64Trichotomy
import BaseLanguage.Behavior.Outcomes

namespace BaseLanguage

/-!
# `Behavior/CodegenBehavior.lean` — `codegen` preserves fault & divergence (IR → ARM64)

The backend `codegen` is a per-block plus-simulation: each IR `Step` is realised by ≥ 1 AArch64 steps
(`forward_step`), re-establishing `StateRel`. From that shape:

* **fault** — an IR `Faulting` config is an `assign` whose RHS is a `div`/`mod` by zero; its block runs
  `emitExpr`, whose `cbz` branches to the `abort` fault block (`emitExpr_correct`'s `none` case), so the
  machine `.faulted`s. `forward_fault` + `forward_steps` give `Asm.Faults`.
* **divergence** — each IR step costs ≥ 1 machine step (`forward_step_pos`), so an infinite IR run forces
  an infinite machine run, **with no measure**. Mirrors the IR `RunsFor` argument on `Asm.run`.

Only *uses* the audited backend simulation (`CodegenForward`/`CodegenEmit`); nothing there is edited.
-/

namespace TacToAsm

open Tac Semantics Asm

/-! ## Fault: an IR `Faulting` config drives the machine to `.faulted` -/

/-- **The faulting block faults the machine.** At a `Faulting` config (`assign x e next`, `eval … = none`),
    the block's `emitExpr e` reaches the `abort` fault block (`emitExpr_correct`, `none` branch). -/
theorem forward_fault {P : Program} {cf : Config} {s : Asm.State}
    (hrel : StateRel P cf s) (hflt : Semantics.Faulting P cf) :
    ∃ fuel, Asm.run (codegen P) fuel s = .faulted := by
  obtain ⟨x, e, next, hf, hev⟩ := hflt
  obtain ⟨hpc, hmem⟩ := hrel
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hemb := block_embeds P cf.node hnd
  rw [hcode] at hemb; simp only [blockFor] at hemb
  have hembE : Asm.Embeds (codegen P) s.pc (emitExpr (collectVars P) (P.code.size * B) e) := by
    rw [hpc]; exact hemb.append_left
  have hE := emitExpr_correct hembE (fault_abort P) hmem
  rw [hev] at hE
  exact ⟨_, hE⟩

/-- **Fault, whole-program.** An IR run into a `Faulting` config yields an `Asm.Faults`. -/
theorem forward_faults {P : Program} {c cf : Config} {s : Asm.State}
    (hrel : StateRel P c s) (hsteps : Steps P c cf) (hflt : Semantics.Faulting P cf) :
    Asm.Faults (codegen P) s := by
  obtain ⟨fuel1, s1, hr1, hrel1⟩ := forward_steps hrel hsteps
  obtain ⟨fuel2, hr2⟩ := forward_fault hrel1 hflt
  exact ⟨fuel1 + fuel2, by rw [Asm.run_running_add fuel1 fuel2 hr1]; exact hr2⟩

/-- **`codegen` preserves faults.** An IR run from the entry into a `Faulting` config ⟹ the machine
    faults from its initial state. -/
theorem codegen_faults {P : Program} {cf : Config}
    (hsteps : Steps P ⟨P.entry, Store.init⟩ cf) (hflt : Semantics.Faulting P cf) :
    Asm.Faults (codegen P) (initState P Store.init) :=
  forward_faults (initRel P) hsteps hflt

/-! ## Divergence: each IR step costs ≥ 1 machine step -/

/-- Each IR `Step` is realised by **≥ 1** machine steps (the block-case fuels are `1`/`2`/`3`/`≥ 2`). -/
theorem forward_step_pos {P : Program} {c c' : Config} {s : Asm.State}
    (hrel : StateRel P c s) (hstep : Step P c c') :
    ∃ fuel s', 1 ≤ fuel ∧ Asm.run (codegen P) fuel s = .running s' ∧ StateRel P c' s' := by
  cases hstep with
  | assign hf hev => obtain ⟨s', hr, hrel'⟩ := forward_assign hrel hf hev; exact ⟨_, s', by omega, hr, hrel'⟩
  | ifzT hf hz => obtain ⟨s', hr, hrel'⟩ := forward_ifzT hrel hf hz; exact ⟨2, s', by omega, hr, hrel'⟩
  | ifzF hf hz => obtain ⟨s', hr, hrel'⟩ := forward_ifzF hrel hf hz; exact ⟨3, s', by omega, hr, hrel'⟩
  | noop hf => obtain ⟨s', hr, hrel'⟩ := forward_noop hrel hf; exact ⟨1, s', by omega, hr, hrel'⟩

/-- **Downward closure of "still running".** (Terminals `.halted`/`.faulted` are stable — `run_*_mono`.) -/
theorem asm_running_le {prog : Prog} {s : State} {m n : Nat} (hle : m ≤ n)
    (h : ∃ s', Asm.run prog n s = .running s') : ∃ s', Asm.run prog m s = .running s' := by
  obtain ⟨sn, hn⟩ := h
  cases hm : Asm.run prog m s with
  | running sm => exact ⟨sm, rfl⟩
  | halted sf =>
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      rw [Asm.run_halt_mono hm k] at hn; exact absurd hn (by simp)
  | faulted =>
      obtain ⟨k, rfl⟩ := Nat.le.dest hle
      rw [Asm.run_fault_mono hm k] at hn; exact absurd hn (by simp)

/-- **The machine is still running after any `m` steps** when the IR diverges: each of the ≤ `m`
    underlying IR steps buys ≥ 1 machine step. -/
theorem asm_runsFor_of_diverges {P : Program} :
    ∀ (m : Nat) {c : Config} {s : Asm.State},
      StateRel P c s → Semantics.Diverges P c → ∃ s', Asm.run (codegen P) m s = .running s' := by
  intro m
  induction m with
  | zero => intro c s _ _; exact ⟨s, rfl⟩
  | succ k ih =>
      intro c s hrel hdiv
      obtain ⟨c₁, hstep, hdiv1⟩ := Semantics.diverges_step hdiv
      obtain ⟨fuel₀, s₁, hpos, hr, hrel1⟩ := forward_step_pos hrel hstep
      obtain ⟨s', hs'⟩ := ih hrel1 hdiv1
      refine asm_running_le (show k + 1 ≤ fuel₀ + k by omega) ⟨s', ?_⟩
      rw [Asm.run_running_add fuel₀ k hr]; exact hs'

/-- **`codegen` preserves divergence.** An infinite IR run ⟹ the machine runs forever. -/
theorem codegen_diverges {P : Program}
    (hdiv : Semantics.Diverges P ⟨P.entry, Store.init⟩) :
    Asm.Diverges (codegen P) (initState P Store.init) :=
  fun fuel => asm_runsFor_of_diverges fuel (initRel P) hdiv

end TacToAsm

end BaseLanguage
