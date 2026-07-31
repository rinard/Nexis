-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.IR.Cfg

/-!
# `Solver.Impl.Graph` — the `Step ↔ realizable-edge` bridge

The ghost constraints quantify over the operational `Step P c c'`, but the worklist solver runs
over a finite CFG. This module supplies the bridge: a **realizability-filtered** successor list
`realizableSucc` such that a CFG edge is in it **iff** some actual machine step traverses it. The only
gap between the plain CFG and the step relation is an assignment whose right-hand side *always* faults
(`÷`/`mod` by a literal zero), which no store can step across; filtering those edges makes
`realizableSucc` exactly the set of step-realized successors, so extremality holds under `WellFormed`
alone (no further hypotheses leak into `solve_correct`).
-/

namespace Solver

open BaseLanguage Tac Semantics

/-- An expression that **faults under every store**: `÷`/`mod` by a literal zero. (A variable divisor
    `÷ v` faults only when `v = 0`, so *some* store steps across it; a literal nonzero divisor never
    faults.) These are exactly the assignment right-hand sides no machine step can evaluate. -/
def alwaysFaults : Expr → Bool
  | .bin .div _ (.imm k) => k == 0
  | .bin .mod _ (.imm k) => k == 0
  | _                    => false

/-- Some store evaluates `e` without faulting iff `e` is not an always-faulter. -/
theorem exists_eval_some_iff (e : Expr) :
    (∃ σ : Store, eval σ e ≠ none) ↔ alwaysFaults e = false := by
  cases e with
  | atom a => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval]⟩⟩
  | una op a => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval]⟩⟩
  | bin op a b =>
      cases op with
      | div =>
          cases b with
          | imm k =>
              simp only [alwaysFaults]
              constructor
              · rintro ⟨σ, hσ⟩
                simp only [eval, evalAtom, Binop.denote] at hσ
                by_cases hk : k == 0
                · simp [hk] at hσ
                · simpa using hk
              · intro hk
                refine ⟨Store.init, ?_⟩
                simp only [eval, evalAtom, Binop.denote]
                rw [if_neg (by simpa using hk)]
                simp
          | var v =>
              refine ⟨fun _ => rfl, fun _ => ⟨(fun _ => (1 : Val)), ?_⟩⟩
              simp only [eval, evalAtom, Binop.denote]
              rw [if_neg (by decide)]
              simp
      | mod =>
          cases b with
          | imm k =>
              simp only [alwaysFaults]
              constructor
              · rintro ⟨σ, hσ⟩
                simp only [eval, evalAtom, Binop.denote] at hσ
                by_cases hk : k == 0
                · simp [hk] at hσ
                · simpa using hk
              · intro hk
                refine ⟨Store.init, ?_⟩
                simp only [eval, evalAtom, Binop.denote]
                rw [if_neg (by simpa using hk)]
                simp
          | var v =>
              refine ⟨fun _ => rfl, fun _ => ⟨(fun _ => (1 : Val)), ?_⟩⟩
              simp only [eval, evalAtom, Binop.denote]
              rw [if_neg (by decide)]
              simp
      | add => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | sub => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | mul => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | and => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | or => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | xor => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | shl => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | lshr => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | ashr => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | eq => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | ne => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | lt => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | le => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | ltu => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩
      | leu => exact ⟨fun _ => rfl, fun _ => ⟨Store.init, by simp [eval, Binop.denote]⟩⟩

/-- The **realizable successors** of `nd`: CFG successors that some machine step actually traverses.
    Identical to `succList` except an always-faulting assignment has no realizable successor. -/
def realizableSucc (P : Program) (nd : Node) : List Node :=
  match P.fetch nd with
  | some (.assign _ e next) => if alwaysFaults e then [] else [next]
  | some (.ifz _ z nz)      => [z, nz]
  | some (.noop next)       => [next]
  | some .halt              => []
  | none                    => []

/-- **The bridge.** A node `m` is a realizable successor of `nd` iff some machine step goes `nd → m`. -/
theorem realizable_iff_step {P : Program} {nd m : Node} :
    (∃ σ σ' : Store, Step P ⟨nd, σ⟩ ⟨m, σ'⟩) ↔ m ∈ realizableSucc P nd := by
  unfold realizableSucc
  cases hf : P.fetch nd with
  | none =>
      constructor
      · rintro ⟨σ, σ', hstep⟩; cases hstep <;> simp_all
      · intro h; simp at h
  | some instr =>
      cases instr with
      | assign x e next =>
          simp only
          constructor
          · rintro ⟨σ, σ', hstep⟩
            cases hstep with
            | assign hf' hv =>
                rw [hf] at hf'; cases hf'
                have : alwaysFaults e = false :=
                  (exists_eval_some_iff e).mp ⟨σ, by rw [hv]; exact Option.some_ne_none _⟩
                rw [if_neg (by simp [this])]; simp
            | ifzT hf' _ => rw [hf] at hf'; simp at hf'
            | ifzF hf' _ => rw [hf] at hf'; simp at hf'
            | noop hf' => rw [hf] at hf'; simp at hf'
          · intro h
            by_cases hfa : alwaysFaults e
            · rw [if_pos hfa] at h; simp at h
            · rw [if_neg hfa] at h
              simp only [List.mem_singleton] at h
              subst h
              obtain ⟨σ, hσ⟩ := (exists_eval_some_iff e).mpr (by simpa using hfa)
              obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hσ
              exact ⟨σ, σ.update x v, .assign hf hv⟩
      | ifz x z nz =>
          simp only
          constructor
          · rintro ⟨σ, σ', hstep⟩
            cases hstep with
            | assign hf' _ => rw [hf] at hf'; simp at hf'
            | ifzT hf' _ => rw [hf] at hf'; cases hf'; simp
            | ifzF hf' _ => rw [hf] at hf'; cases hf'; simp
            | noop hf' => rw [hf] at hf'; simp at hf'
          · intro h
            simp only [List.mem_cons, List.not_mem_nil, or_false] at h
            rcases h with h | h
            · subst h; exact ⟨(fun _ => 0), (fun _ => 0), .ifzT hf rfl⟩
            · subst h; exact ⟨(fun _ => 1), (fun _ => 1), .ifzF hf (by decide)⟩
      | noop next =>
          simp only
          constructor
          · rintro ⟨σ, σ', hstep⟩
            cases hstep with
            | assign hf' _ => rw [hf] at hf'; simp at hf'
            | ifzT hf' _ => rw [hf] at hf'; simp at hf'
            | ifzF hf' _ => rw [hf] at hf'; simp at hf'
            | noop hf' => rw [hf] at hf'; cases hf'; simp
          · intro h
            simp only [List.mem_singleton] at h
            subst h
            exact ⟨Store.init, Store.init, .noop hf⟩
      | halt =>
          constructor
          · rintro ⟨σ, σ', hstep⟩; cases hstep <;> simp_all
          · intro h; simp at h

/-- Every realizable successor is a CFG successor (`realizableSucc ⊆ succList`). -/
theorem realizableSucc_subset_succList {P : Program} {nd m : Node}
    (h : m ∈ realizableSucc P nd) : m ∈ succList P nd := by
  unfold realizableSucc at h
  unfold succList
  cases hf : P.fetch nd with
  | none => rw [hf] at h; simp at h
  | some instr =>
      rw [hf] at h
      cases instr with
      | assign x e next =>
          simp only at h
          by_cases hfa : alwaysFaults e
          · rw [if_pos hfa] at h; simp at h
          · rw [if_neg hfa] at h
            simp only [List.mem_singleton] at h; subst h
            simp [Cmd.succs]
      | ifz x z nz => simpa [Cmd.succs] using h
      | noop next => simpa [Cmd.succs] using h
      | halt => simp at h

/-- A realizable successor is in range (under `WellFormed`). -/
theorem realizableSucc_lt {P : Program} (hwf : WellFormed P) {nd m : Node}
    (h : m ∈ realizableSucc P nd) : m < P.size := by
  obtain ⟨instr, hfetch, hmem⟩ := mem_succList (realizableSucc_subset_succList h)
  exact hwf.succ_lt hfetch hmem

/-- The **realizable predecessors** of `j`: in-range nodes with `j` as a realizable successor. -/
def realizablePred (P : Program) (j : Node) : List Node :=
  (List.range P.size).filter (fun i => decide (j ∈ realizableSucc P i))

theorem mem_realizablePred {P : Program} {j i : Node} :
    i ∈ realizablePred P j ↔ i < P.size ∧ j ∈ realizableSucc P i := by
  unfold realizablePred; rw [List.mem_filter, List.mem_range, decide_eq_true_eq]

/-- Whether `n` carries a `halt` (the backward-analysis seed nodes). -/
def isHalt (P : Program) (n : Node) : Bool := decide (P.fetch n = some .halt)

end Solver
