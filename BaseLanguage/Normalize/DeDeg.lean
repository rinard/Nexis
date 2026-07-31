-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Constraints

/-!
# `Normalize.DeDeg` — the distinct-successors pre-pass

Rewrites every **degenerate** branch `ifz x z z → noop z`, so the result has duplicate-free successor
lists (`DistinctSuccs`). A trivial source-to-source instruction map; here we keep only the *structural*
facts the normal form needs (behaviour preservation is out of scope), all dataflow-free.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

/-- Rewrite a degenerate branch `ifz x z z` to `noop z`; carry everything else verbatim. -/
def deDegCmd : Cmd → Cmd
  | .ifz x z nz => if z = nz then .noop z else .ifz x z nz
  | other       => other

/-- **The distinct-successors pre-pass.** Same entry / observables; each instruction de-degenerated. -/
def deDeg (P : Program) : Program where
  entry := P.entry
  code  := P.code.map deDegCmd
  obs   := P.obs

@[simp] theorem deDeg_entry (P : Program) : (deDeg P).entry = P.entry := rfl

@[simp] theorem deDeg_size (P : Program) : (deDeg P).size = P.size := by
  show (P.code.map deDegCmd).size = P.code.size
  simp

/-- Fetch commutes with the per-instruction rewrite. -/
theorem deDeg_fetch (P : Program) (nd : Node) :
    (deDeg P).fetch nd = (P.fetch nd).map deDegCmd := by
  show (P.code.map deDegCmd)[nd]? = (P.code[nd]?).map deDegCmd
  rw [Array.getElem?_map]

/-- **Distinct successors** (definitionally `DistinctSuccs (deDeg P)`). -/
theorem deDeg_succList_nodup (P : Program) (nd : Node) : (succList (deDeg P) nd).Nodup := by
  rw [succList, deDeg_fetch]
  cases hf : P.fetch nd with
  | none => simp
  | some instr =>
      cases instr with
      | assign x e next => simp [deDegCmd, Cmd.succs]
      | ifz x z nz =>
          by_cases hzz : z = nz
          · subst hzz; simp [deDegCmd, Cmd.succs]
          · simp only [deDegCmd, if_neg hzz, Option.map_some, Option.elim, Cmd.succs]
            simp [hzz]
      | noop next => simp [deDegCmd, Cmd.succs]
      | halt => simp [deDegCmd, Cmd.succs]

theorem deDeg_distinctSuccs (P : Program) : DistinctSuccs (deDeg P) := deDeg_succList_nodup P

/-- **`deDeg` preserves `NoSelfRead`** — it rewrites only branches, never assignments. -/
theorem deDeg_noSelfRead (P : Program) (hns : NoSelfRead P) : NoSelfRead (deDeg P) := by
  intro nd x e next hf hnum
  rw [deDeg_fetch] at hf
  cases hpf : P.fetch nd with
  | none => rw [hpf] at hf; simp at hf
  | some instr =>
      rw [hpf] at hf; simp only [Option.map_some] at hf
      injection hf with hf
      cases instr with
      | assign x0 e0 next0 =>
          simp only [deDegCmd] at hf
          injection hf with hx he hn; subst hx; subst he; subst hn
          exact hns hpf hnum
      | ifz x1 z1 nz1 =>
          by_cases hzz : z1 = nz1
          · subst hzz; simp [deDegCmd] at hf
          · simp [deDegCmd, hzz] at hf
      | noop n1 => simp [deDegCmd] at hf
      | halt => simp [deDegCmd] at hf

/-- **Well-formedness is preserved** — every rewritten successor was a successor of the source. -/
theorem deDeg_wellFormed (P : Program) (hwf : WellFormed P) : WellFormed (deDeg P) where
  entry_lt := by rw [deDeg_entry, deDeg_size]; exact hwf.entry_lt
  succ_lt := by
    intro nd instr s hf hs
    rw [deDeg_size]
    rw [deDeg_fetch] at hf
    cases hpf : P.fetch nd with
    | none => rw [hpf] at hf; simp at hf
    | some instr0 =>
        rw [hpf] at hf; simp only [Option.map_some] at hf
        injection hf with hf; subst hf
        cases instr0 with
        | assign x e next =>
            simp only [deDegCmd, Cmd.succs, List.mem_singleton] at hs; subst hs
            exact hwf.succ_lt hpf (by simp [Cmd.succs])
        | ifz x z nz =>
            by_cases hzz : z = nz
            · subst hzz
              simp [deDegCmd, Cmd.succs] at hs; subst hs
              exact hwf.succ_lt hpf (by simp [Cmd.succs])
            · simp only [deDegCmd, if_neg hzz] at hs
              exact hwf.succ_lt hpf hs
        | noop next =>
            simp only [deDegCmd, Cmd.succs, List.mem_singleton] at hs; subst hs
            exact hwf.succ_lt hpf (by simp [Cmd.succs])
        | halt => simp [deDegCmd, Cmd.succs] at hs

/-! ## Reachability preservation (`deDeg` keeps every node's successor *set`) -/

/-- `deDeg` preserves an instruction's successor set (only the degenerate dedup `[z,z] → [z]`). -/
theorem deDegCmd_mem_succs (instr : Cmd) (nd : Node) :
    nd ∈ (deDegCmd instr).succs ↔ nd ∈ instr.succs := by
  cases instr with
  | assign x e next => simp [deDegCmd]
  | ifz x z nz =>
      by_cases hzz : z = nz
      · subst hzz; simp [deDegCmd, Cmd.succs]
      · simp [deDegCmd, hzz]
  | noop n => simp [deDegCmd]
  | halt => simp [deDegCmd]

/-- `deDeg` preserves a node's successor set. -/
theorem deDeg_mem_succList (P : Program) (p nd : Node) :
    nd ∈ succList (deDeg P) p ↔ nd ∈ succList P p := by
  unfold succList
  rw [deDeg_fetch]
  cases P.fetch p with
  | none => simp
  | some instr => simp only [Option.map_some, Option.elim]; exact deDegCmd_mem_succs instr nd

/-- A `List.any` over two lists with the same membership set agrees pointwise. -/
theorem any_congr_mem {α : Type _} (g : α → Bool) {l1 l2 : List α}
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1.any g = l2.any g := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hg⟩; exact ⟨x, (h x).mp hx, hg⟩
  · rintro ⟨x, hx, hg⟩; exact ⟨x, (h x).mpr hx, hg⟩

/-- `FReach` transfers into `deDeg P` (same entry; successor sets preserved). -/
theorem deDeg_freach (P : Program) {nd : Node} (hr : FReach P nd) : FReach (deDeg P) nd := by
  induction hr with
  | entry => rw [← deDeg_entry P]; exact FReach.entry
  | step _ hmem ih => exact FReach.step ih ((deDeg_mem_succList P _ _).mpr hmem)

/-- **`deDeg` preserves `AllReachable`.** -/
theorem deDeg_allReach (P : Program) (hr : AllReachable P) : AllReachable (deDeg P) := by
  intro nd hnd
  rw [deDeg_size] at hnd
  exact deDeg_freach P (hr nd hnd)

end Normalize
end BaseLanguage
