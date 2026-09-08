-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.ExecCount
import BaseLanguage.PDCE.OperationalLiveRange
/-! # Two-program register-pressure optimality (synchronized by original steps)

The live-range dual of `ExecCountTwoProgram`. `regOccOrig` runs `transform P S` under its own semantics
with fuel measured in *original* steps (one block per unit), so two transformed programs run with the same
`ks` are synchronized at original-node boundaries. At each visited block head it adds the register-occupancy
indicator for `x`, **verified operationally against the transformed store** — the contribution fires only
when `x` is register-occupied (`regOcc`) *and* the transformed program's register actually holds the source
value (`d.store x = c.store x`), which is the operational content of `transform_holds_regOcc` folded into a
count. `regOccOrig = pathVarLiveRange` (over the source run's nodes) folds it to the ghost measure; the
headline `transform_regOccOrig_le_any` then compares two real compiled programs via `pathVarLiveRange_le`.

This is the symmetric two-transformed-program explicit-trace theorem for the live-range axis — the
analogue of `transform_execCountOrig_le_any` on the register-pressure side. -/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
set_option linter.unusedVariables false

/-- Execute `transform P S`, summing the register-occupancy indicator of `x` at each visited block head,
    with fuel measured in ORIGINAL steps. `c` = source config (the clock), `d` = transformed config
    (invariant `Match P S c d`). The head contribution fires when `x` is register-occupied (`regOcc`) and
    the transformed store holds the source value (`d.store x = c.store x`) — genuinely reading the run.
    Each unit advances the transformed program by one block via its real `run`. -/
def regOccOrig (P : Program) (S : PdceSpec P) (x : Var) : Config → Config → Nat → Nat
  | _, _, 0      => 0
  | c, d, ks + 1 =>
      (if regOcc S.π S.ηK x c.node = true ∧ d.store x = c.store x then 1 else 0)
        + (match step1 P c with
           | .next c' =>
               regOccOrig P S x c'
                 (run (transform P S) d (blockFuelTo P S c.node c'.node)).1 ks
           | _ => 0)

/-- `pathVarLiveRange` peels its head node: the occupancy indicator at `n` plus the rest. -/
theorem pathVarLiveRange_cons {P : Program} (S : PdceSpec P) (x : Var) (n : Node) (rest : List Node) :
    pathVarLiveRange S x (n :: rest)
      = (if regOcc S.π S.ηK x n = true then 1 else 0) + pathVarLiveRange S x rest := by
  unfold pathVarLiveRange
  rw [List.filter_cons]
  by_cases h : regOcc S.π S.ηK x n = true
  · simp [h, Nat.add_comm]
  · simp [h]

/-- **The fold.** The original-fueled register-occupancy count of `transform P S` equals the source-side
    register-pressure measure `pathVarLiveRange` over the run's node-path. Prefix-general (any `ks`, no
    `Final`); the operational store-check is discharged by `Match` clause 2 (`transform_holds_regOcc`). -/
theorem regOccOrig_eq_pathVarLiveRange {P : Program} (S : PdceSpec P) (wf : WellFormed P) (x : Var) :
    ∀ (ks : Nat) {c d : Config}, Match P S c d →
      regOccOrig P S x c d ks = pathVarLiveRange S x (runNodes P c ks) := by
  intro ks
  induction ks with
  | zero => intro c d _; simp [regOccOrig, pathVarLiveRange, runNodes]
  | succ k ih =>
      intro c d hm
      -- The operational head contribution collapses to the ghost occupancy indicator (Match clause 2).
      have hhead : (if regOcc S.π S.ηK x c.node = true ∧ d.store x = c.store x then (1:Nat) else 0)
                    = (if regOcc S.π S.ηK x c.node = true then 1 else 0) := by
        by_cases hocc : regOcc S.π S.ηK x c.node = true
        · obtain ⟨hnode, hc2, _, _⟩ := hm
          obtain ⟨hlive, hnf⟩ := regOcc_iff.mp hocc
          have hval : d.store x = c.store x := hc2 x hlive hnf
          simp [hocc, hval]
        · simp [hocc]
      cases hstep : step1 P c with
      | next c' =>
          have hStep : Step P c c' := step1_next_iff.mp hstep
          obtain ⟨τF, hrun, hmatch, _⟩ := block_execCount S wf (default : Asgn) hm hStep
          simp only [regOccOrig, hstep, hrun]
          rw [ih hmatch, hhead]
          simp only [runNodes, hstep, pathVarLiveRange_cons]
      | halt =>
          simp only [regOccOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRange_cons]
          rw [hhead]; simp [pathVarLiveRange]
      | fault =>
          simp only [regOccOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRange_cons]
          rw [hhead]; simp [pathVarLiveRange]
      | stuck =>
          simp only [regOccOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRange_cons]
          rw [hhead]; simp [pathVarLiveRange]

/-- **Two-program register-pressure optimality, all prefixes.** Running BOTH compiled programs for the same
    `ks` original steps, the extremal transform occupies register `x` over a region no larger than the
    competitor's — the live-range analogue of `transform_execCountOrig_le_any`, and the honest operational
    (two-transformed-program) form of `pathVarLiveRange_le` / `transform_regPressure_le`. -/
theorem transform_regOccOrig_le_any {P : Program} (S S' : PdceSpec P) (hS : Extremal S)
    (wf : WellFormed P) (hkq : S'.keep = S.keep) (x : Var) (σ : Store) (ks : Nat) :
    regOccOrig P S  x ⟨P.entry, σ⟩ ⟨blockOff P S  P.entry, σ⟩ ks
      ≤ regOccOrig P S' x ⟨P.entry, σ⟩ ⟨blockOff P S' P.entry, σ⟩ ks := by
  rw [regOccOrig_eq_pathVarLiveRange S  wf x ks (match_init S  σ),
      regOccOrig_eq_pathVarLiveRange S' wf x ks (match_init S' σ)]
  exact transform_regPressure_le hS S' hkq x ⟨P.entry, σ⟩ ks

/-! ## Two-program HONEST register-pressure — the `regOccExt` fold (both disjuncts read the real store)

`regOccOrig` folds `regOcc`, which undercounts moved reads (`OperationalLiveRange` §"honest register
occupancy"). Here is the same operational two-program apparatus for the honest measure `regOccExt`: the head
indicator verifies **both** disjuncts against the transformed store — the materialized value (`Match`
clause 2) *and* the recoverability of each live in-flight assignment reading `x` (`Match` clause 3). The fold
`regOccExtOrig = pathVarLiveRangeExt` holds unconditionally; the two-program `≤` needs `NoMovedRead`. -/

private theorem list_any_congr {α} {p q : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = q a) → l.any p = l.any q
  | [], _ => rfl
  | a :: t, h => by
      rw [List.any_cons, List.any_cons, h a List.mem_cons_self,
          list_any_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- The honest operational head: `x` materialized-and-held (`regOcc`, store agrees) **or** the operand of a
    live in-flight assignment whose rhs the transformed store recomputes. Every disjunct genuinely reads `d`. -/
def regOccExtHead {P : Program} (S : PdceSpec P) (x : Var) (c d : Config) : Bool :=
  (regOcc S.π S.ηK x c.node && decide (d.store x = c.store x))
    || (S.ηK c.node).toList.any (fun a =>
          exprReadsVar a.rhs x && (S.π c.node).contains a.lhs
            && decide (eval d.store a.rhs = some (c.store a.lhs)))

/-- **The operational head collapses to the ghost `regOccExt`** — clause 2 discharges the first disjunct's
    store check, clause 3 the per-assignment recomputation check. So `regOccExtHead` reads the real store yet
    equals the static honest indicator. -/
theorem regOccExtHead_eq {P : Program} {S : PdceSpec P} {x : Var} {c d : Config}
    (hm : Match P S c d) : regOccExtHead S x c d = regOccExt S.π S.ηK x c.node := by
  obtain ⟨_, hc2, hc3, _⟩ := hm
  unfold regOccExtHead regOccExt heldForInFlight
  have h1 : (regOcc S.π S.ηK x c.node && decide (d.store x = c.store x))
            = regOcc S.π S.ηK x c.node := by
    by_cases hocc : regOcc S.π S.ηK x c.node = true
    · obtain ⟨hlive, hnf⟩ := regOcc_iff.mp hocc
      simp [hocc, hc2 x hlive hnf]
    · simp only [Bool.not_eq_true] at hocc; simp [hocc]
  have h2 : ((S.ηK c.node).toList.any (fun a =>
              exprReadsVar a.rhs x && (S.π c.node).contains a.lhs
                && decide (eval d.store a.rhs = some (c.store a.lhs))))
            = (S.ηK c.node).toList.any (fun a =>
              exprReadsVar a.rhs x && (S.π c.node).contains a.lhs) := by
    apply list_any_congr
    intro a ha
    by_cases hp : (exprReadsVar a.rhs x && (S.π c.node).contains a.lhs) = true
    · rw [Bool.and_eq_true] at hp
      have hrec : eval d.store a.rhs = some (c.store a.lhs) :=
        hc3 a.lhs a.rhs (Assignments.mem_toList.mp ha) (Std.HashSet.contains_iff_mem.mp hp.2)
      simp [hp.1, hp.2, hrec]
    · simp only [Bool.not_eq_true] at hp; simp [hp]
  rw [h1, h2]

/-- Honest occupancy fold: run `transform P S` (fuel in original steps), summing `regOccExtHead` at each
    block head. Structurally identical to `regOccOrig`, honest indicator. -/
def regOccExtOrig (P : Program) (S : PdceSpec P) (x : Var) : Config → Config → Nat → Nat
  | _, _, 0      => 0
  | c, d, ks + 1 =>
      (if regOccExtHead S x c d then 1 else 0)
        + (match step1 P c with
           | .next c' =>
               regOccExtOrig P S x c'
                 (run (transform P S) d (blockFuelTo P S c.node c'.node)).1 ks
           | _ => 0)

/-- `pathVarLiveRangeExt` peels its head node. -/
theorem pathVarLiveRangeExt_cons {P : Program} (S : PdceSpec P) (x : Var) (n : Node) (rest : List Node) :
    pathVarLiveRangeExt S x (n :: rest)
      = (if regOccExt S.π S.ηK x n then 1 else 0) + pathVarLiveRangeExt S x rest := by
  unfold pathVarLiveRangeExt
  rw [List.filter_cons]
  by_cases h : regOccExt S.π S.ηK x n = true
  · simp [h, Nat.add_comm]
  · simp [h]

/-- **The honest fold.** `regOccExtOrig` (operational, reads the transformed store at both disjuncts) equals
    the ghost honest measure `pathVarLiveRangeExt` over the run's node-path — **unconditionally** (no
    `NoMovedRead`). Prefix-general; the store checks collapse by `regOccExtHead_eq` (`Match` clauses 2+3). -/
theorem regOccExtOrig_eq_pathVarLiveRangeExt {P : Program} (S : PdceSpec P) (wf : WellFormed P) (x : Var) :
    ∀ (ks : Nat) {c d : Config}, Match P S c d →
      regOccExtOrig P S x c d ks = pathVarLiveRangeExt S x (runNodes P c ks) := by
  intro ks
  induction ks with
  | zero => intro c d _; simp [regOccExtOrig, pathVarLiveRangeExt, runNodes]
  | succ k ih =>
      intro c d hm
      have hhead : (if regOccExtHead S x c d then (1:Nat) else 0)
                    = (if regOccExt S.π S.ηK x c.node then 1 else 0) := by
        rw [regOccExtHead_eq hm]
      cases hstep : step1 P c with
      | next c' =>
          have hStep : Step P c c' := step1_next_iff.mp hstep
          obtain ⟨τF, hrun, hmatch, _⟩ := block_execCount S wf (default : Asgn) hm hStep
          simp only [regOccExtOrig, hstep, hrun]
          rw [ih hmatch, hhead]
          simp only [runNodes, hstep, pathVarLiveRangeExt_cons]
      | halt =>
          simp only [regOccExtOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRangeExt_cons]
          rw [hhead]; simp [pathVarLiveRangeExt]
      | fault =>
          simp only [regOccExtOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRangeExt_cons]
          rw [hhead]; simp [pathVarLiveRangeExt]
      | stuck =>
          simp only [regOccExtOrig, hstep, Nat.add_zero]
          simp only [runNodes, hstep, pathVarLiveRangeExt_cons]
          rw [hhead]; simp [pathVarLiveRangeExt]

/-- **Two-program HONEST register-pressure optimality, all prefixes.** Under `NoMovedRead` on the extremal
    `S`, running BOTH compiled programs for the same `ks` original steps, the extremal transform occupies
    register `x` — counted by the **honest** measure (materialized values *plus* operand-holds for in-flight
    assignments, each verified against the transformed store) — over a region no larger than any competitor's.
    The honest analogue of `transform_regOccOrig_le_any`, closing the moved-read undercount. -/
theorem transform_regOccExtOrig_le_any {P : Program} (S S' : PdceSpec P) (hS : Extremal S)
    (wf : WellFormed P) (hkq : S'.keep = S.keep) (x : Var) (h : NoMovedRead S x)
    (σ : Store) (ks : Nat) :
    regOccExtOrig P S  x ⟨P.entry, σ⟩ ⟨blockOff P S  P.entry, σ⟩ ks
      ≤ regOccExtOrig P S' x ⟨P.entry, σ⟩ ⟨blockOff P S' P.entry, σ⟩ ks := by
  rw [regOccExtOrig_eq_pathVarLiveRangeExt S  wf x ks (match_init S  σ),
      regOccExtOrig_eq_pathVarLiveRangeExt S' wf x ks (match_init S' σ)]
  exact transform_honestLiveRange_le hS S' hkq x h (runNodes P ⟨P.entry, σ⟩ ks)

end BaseLanguage.Analyses.PDCE
