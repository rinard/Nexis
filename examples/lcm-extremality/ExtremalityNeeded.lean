-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Mode
import BaseLanguage.IR.Pretty
import Seam.lcm.Adapter

/-!
# Why LCM correctness needs an *extremal* bundle, not merely a valid one

`LCM.transform_preserves_halt` assumes `Extremal S` as well as validity, while
`PDCE.transform_preserves_halt` needs only validity. That asymmetry is real, and this file exhibits it:
a bundle that satisfies **every** validity clause of **every** ghost, is provably **not** extremal, and
whose transform computes the wrong answer.

## Why a valid-but-not-extremal bundle exists at all

Look at the shapes of the ghost clauses (`Generated/Seam/lcm/ValidExtremal.lean`). Every clause of
`Anticipated`, `Available`, `Postponable` and `Transfer` is an **upper** bound on the ghost, and the only
lower bound anywhere is `Used.check`. So:

* collapsing `πₐ`, `ηₚ`, `τₚ` to `∅` satisfies all their clauses — these ghosts are constrained only from
  above, and extremality asks for the *greatest* solution, so `∅` is valid and maximally non-extremal;
* inflating `πᵤ`, `τᵤ` to the whole universe satisfies theirs — `Used.check` is a lower bound, which a
  larger set only makes easier, and extremality asks for the *least* solution.

Validity is therefore a genuinely weaker property than extremality, and the gap is not subtle.

## What goes wrong

The transform reads the bundle in two places that must agree:

* it **inserts** `t := e` where `e ∈ insertBefore`/`insertEdge`, both gated by `latestNode`/`latestEdge`,
  which are computed from `πₐ`, `ηₚ`, `τₚ`; and
* it **replaces** an original `x := e` by `x := t` where `e ∈ recoverable = πᵤ ∪ insertBefore`.

Extremality is what keeps those two in step. Collapse the first group and inflate the second, and the
transform replaces every numbered computation with a read of a temporary it never materialized. The
program below then reads an unwritten temporary and observes `0` where the source observes `7`.
-/

open BaseLanguage BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analyses.LCM

def va : Var := .orig "a"
def vb : Var := .orig "b"
def vy : Var := .orig "y"

/-- The tracked expression `a + b` (fault free, so nothing here turns on the divergence work). -/
def E : Expr := .bin .add (.var va) (.var vb)

/-- `0: noop → 1 ; 1: y := a + b → 2 ; 2: halt`, with `y` observable. -/
def P0 : Program :=
  { entry := 0
  , code  := #[ Cmd.noop 1, Cmd.assign vy E 2, Cmd.halt ]
  , obs   := [vy] }

theorem P0_wf : WellFormed P0 where
  entry_lt := by decide
  succ_lt := by
    intro n instr s hf hs
    show s < 3
    match n with
    | 0 =>
        rw [show P0.fetch 0 = some (Cmd.noop 1) from rfl] at hf
        injection hf with h; subst h
        simp only [Cmd.succs, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
          first | (subst hs; decide) | (rcases hs with rfl | rfl <;> decide)
    | 1 =>
        rw [show P0.fetch 1 = some (Cmd.assign vy E 2) from rfl] at hf
        injection hf with h; subst h
        simp only [Cmd.succs, List.mem_cons, List.not_mem_nil, or_false] at hs <;>
          first | (subst hs; decide) | (rcases hs with rfl | rfl <;> decide)
    | 2 =>
        rw [show P0.fetch 2 = some Cmd.halt from rfl] at hf
        injection hf with h; subst h
        simp only [Cmd.succs, List.not_mem_nil] at hs
    | (k+3) =>
        exfalso
        have hnone : P0.fetch (k+3) = none := by
          simp only [P0, Program.fetch]; exact Array.getElem?_eq_none (by simp)
        rw [hnone] at hf; simp at hf

/-- The solved bundle: valid **and** extremal. -/
def Sgood : LcmSpec P0 := lcmSolved P0 P0_wf

/-- **A valid bundle that is not extremal.** Each witness below discharges the ghost's clauses; every one
    of them is an upper bound satisfied by `∅`, or a lower bound satisfied by the universe. -/
def Sbad : LcmSpec P0 :=
  { Sgood with
    πₐ := fun _ => (∅ : Assignments)
    ηₚ := fun _ => (∅ : Assignments)
    τₚ := fun _ => (∅ : Assignments)
    πᵤ := fun _ => allExprs P0
    τᵤ := fun _ => allExprs P0
    isAnti  := ⟨fun _ _ _ e he => absurd (Assignments.mem_sdiff.mp he).1 Std.HashSet.not_mem_empty,
                fun _ e he => absurd he Std.HashSet.not_mem_empty,
                fun _ _ e he => absurd he Std.HashSet.not_mem_empty,
                fun _ e he => absurd he Std.HashSet.not_mem_empty⟩
    isPostp := ⟨fun _ _ _ e he => absurd he Std.HashSet.not_mem_empty,
                fun e he => absurd he Std.HashSet.not_mem_empty,
                fun _ e he => absurd he Std.HashSet.not_mem_empty⟩
    isTauP  := ⟨fun _ _ _ e he => absurd he Std.HashSet.not_mem_empty,
                fun _ e he => absurd he Std.HashSet.not_mem_empty⟩
    isUsed  := ⟨fun _ _ _ e he => Assignments.mem_union.mpr (Or.inl he),
                fun n e he => ue_mem_allExprs (Assignments.mem_sdiff.mp he).1,
                fun _ e he => he⟩
    isUsedOut := ⟨fun _ _ _ e he => he, fun _ e he => he⟩ }

/-- **`ue` is itself a valid `Anticipated`.** Locally computed expressions are anticipated where they are
    computed, and the `predict` obligation is vacuous because every element is killed at its own node. This
    gives a nonempty valid solution without evaluating any solver. -/
theorem ue_anticipated : Anticipated P0 (ue P0) where
  predict := fun _ _ _ e he =>
    absurd (Assignments.mem_sdiff.mp he).1 (Assignments.mem_sdiff.mp he).2
  check   := fun _ e he => Assignments.mem_union.mpr (Or.inl he)
  seed    := by
    intro c hfin e he
    unfold ue at he; rw [hfin] at he
    exact absurd he Std.HashSet.not_mem_empty
  within  := fun _ e he => ue_mem_allExprs he

/-- `a + b` is anticipated at the node that computes it. -/
theorem E_mem_ue : E ∈ ue P0 1 := by
  unfold ue
  rw [show P0.fetch 1 = some (Cmd.assign vy E 2) from rfl]
  exact Analysis.SetOps.mem_singleton.mpr rfl

/-- …and `Sbad` really is not extremal. `Extremal.πₐ` demands that *every* valid `Anticipated` be
    contained in `Sbad.πₐ = ∅`; `ue` is a valid one that is not. -/
theorem Sbad_not_extremal : ¬ Extremal Sbad := fun h =>
  absurd (h.πₐ (ue P0) ue_anticipated 1 E E_mem_ue) Std.HashSet.not_mem_empty

def Tgood : Program := transform P0 Sgood
def Tbad  : Program := transform P0 Sbad

/-- `a = 3`, `b = 4`, so the source observes `y = 7`. -/
def sigma0 : Store := fun v => if v = va then 3 else if v = vb then 4 else 0

def statusName : Status → String
  | .next _ => "running" | .halt => "halt" | .fault => "FAULT" | .stuck => "stuck"

def observe (Q : Program) : String :=
  let (c, st) := run Q ⟨Q.entry, sigma0⟩ 1000
  s!"{statusName st}, y = {c.store vy}"

#eval do
  IO.println "----- source -----"
  IO.println (ppProgram P0)
  IO.println s!"  observes: {observe P0}"
  IO.println "----- transform with the VALID and EXTREMAL bundle -----"
  IO.println (ppProgram Tgood)
  IO.println s!"  observes: {observe Tgood}"
  IO.println "----- transform with the VALID but NOT EXTREMAL bundle -----"
  IO.println (ppProgram Tbad)
  IO.println s!"  observes: {observe Tbad}   <-- WRONG: reads a temporary never materialized"
