-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.LCM.Mode
import BaseLanguage.IR.Pretty
import Seam.lcm.Adapter

/-!
# A concrete program on which classical LCM turns divergence into a fault

This is the witness for the gap `LCM/Divergence.lean` closes: a program that satisfies **every**
precondition the LCM correctness theorem assumes, diverges on a given input, and whose *classically*
optimized form **faults** on that same input.

## Why the classical algorithm permits this

Knoop–Rüthing–Steffen define down-safety over **terminating paths only**:

> "A placement is *down-safe*, iff every computation point `n` is an `n`-down-safe node, i.e. a
>  computation of `t` at `n` does not introduce a new value **on a terminating path starting in `n`**.
>  … an initialization `h := t` placed at the entry of node `n` is justified on **every terminating
>  path** by an original computation …"
>  — Knoop, Rüthing, Steffen, *Lazy Code Motion*, PLDI 1992, §3

and they assume the CFG has no unreachable-from-exit nodes at all:

> "Every node `n ∈ N` is assumed to lie on a path from `s` to `e`."

An infinite loop has no path to `e`, so it is outside their model; and on a non-terminating path the
down-safety obligation is *vacuously* satisfied. That vacuity is inherited exactly by the greatest-fixpoint
`Anticipated` (`πₐ`) ghost: its `check`/`predict` clauses are satisfiable all the way around a cycle whose
body never computes `e`. So KRS give no such counterexample — their safety notion cannot express it.

## The program

```
  0: noop → 1
  1: ifz c    c=0 → 2      c≠0 → 5
  2: noop → 3                          -- the arm that does NOT compute a/b
  3: ifz d    d=0 → 4      d≠0 → 6
  4: y := a/b → 7                      -- the only TERMINATING path computes a/b
  5: x := a/b → 3                      -- makes a/b available along the other arm
  6: noop → 6                          -- INFINITE LOOP; never computes a/b
  7: halt
```

`a/b` is down-safe at node 3 in precisely KRS's sense — the only terminating path from 3 is `3→4`, which
computes it. Node 5 supplies the availability that stops `a/b` being *postponable* past the join, so
`latest` fires at node 2's successor and LCM materializes `t0 := a/b` **before** the branch at node 3.

On `a=10, b=0, c=0, d≠0` the source runs `0→1→2→3→6→6→…` and never evaluates `a/b`. The classically
optimized program evaluates it at the hoisted point and divides by zero.

## Running it

```sh
lake env lean examples/lcm-divergence/DivergenceGap.lean
```

**Axioms.** This exhibit uses `native_decide` for one purely computational fact (`wellFormedb Pgap`), which
adds `ofReduceBool`. It is deliberately **not** part of the `BaseLanguage` library and not in
`defaultTargets`; every theorem in the library proper remains axiom-clean.
-/

open BaseLanguage BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analyses.LCM

def va : Var := .orig "a"
def vb : Var := .orig "b"
def vc : Var := .orig "c"
def vd : Var := .orig "d"
def vx : Var := .orig "x"
def vy : Var := .orig "y"

/-- The faulting expression: `div` is one of the only two partial operators in the IR. -/
def E : Expr := .bin .div (.var va) (.var vb)

def Pgap : Program :=
  { entry := 0
  , code  := #[ Cmd.noop 1, Cmd.ifz vc 2 5, Cmd.noop 3, Cmd.ifz vd 4 6,
                Cmd.assign vy E 7, Cmd.assign vx E 3, Cmd.noop 6, Cmd.halt ]
  , obs := [vx, vy] }

theorem Pgap_wf : WellFormed Pgap := wellFormedb_iff.mp (by native_decide)

/-- Every node is forward-reachable from the entry — so the program is not degenerate, and
    `normalize_wellNormalized` applies to it. -/
theorem Pgap_reach : AllReachable Pgap := by
  have h0 : FReach Pgap 0 := FReach.entry
  have h1 : FReach Pgap 1 := FReach.step h0 (by decide)
  have h2 : FReach Pgap 2 := FReach.step h1 (by decide)
  have h5 : FReach Pgap 5 := FReach.step h1 (by decide)
  have h3 : FReach Pgap 3 := FReach.step h2 (by decide)
  have h4 : FReach Pgap 4 := FReach.step h3 (by decide)
  have h6 : FReach Pgap 6 := FReach.step h3 (by decide)
  have h7 : FReach Pgap 7 := FReach.step h4 (by decide)
  intro nd h
  have hs : Pgap.size = 8 := by native_decide
  rw [hs] at h
  match nd, h with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | 3, _ => exact h3
  | 4, _ => exact h4
  | 5, _ => exact h5
  | 6, _ => exact h6
  | 7, _ => exact h7

/-- The normalized program: exactly the shape the compiler hands to LCM. -/
def N : Program := Normalize.normalize Pgap

/-- **LCM's precondition, discharged.** So the counterexample is not an out-of-scope program. -/
theorem N_wn : Normalize.WellNormalized N := Normalize.normalize_wellNormalized Pgap Pgap_wf Pgap_reach

def S    : LcmSpec N := lcmSolved N N_wn.wf
def Pcls : Program := runLcm .classic            N S
def Psaf : Program := runLcm .preserveDivergence N S

/-- `a=10`, `b=0` (zero divisor), `c=0` (take the non-computing arm), `d≠0` (enter the infinite loop). -/
def sigma0 : Store := fun v => if v = va then 10 else if v = vd then 1 else 0

def statusName : Status → String
  | .next _ => "diverges (still running)"
  | .halt   => "halt"
  | .fault  => "FAULT"
  | .stuck  => "stuck"

#eval do
  IO.println "----- normalized source N (WellNormalized, proved above) -----"
  IO.println (ppProgram N)
  IO.println "----- classic LCM: t0 := a / b is hoisted BEFORE the branch into the loop -----"
  IO.println (ppProgram Pcls)
  IO.println "----- divergence-preserving LCM -----"
  IO.println (ppProgram Psaf)
  IO.println s!"source              : {statusName (run N    ⟨N.entry,    sigma0⟩ 100000).2}"
  IO.println s!"classic             : {statusName (run Pcls ⟨Pcls.entry, sigma0⟩ 100000).2}"
  IO.println s!"preserve-divergence : {statusName (run Psaf ⟨Psaf.entry, sigma0⟩ 100000).2}"
  IO.println s!"safe output = source? {decide (Psaf == N)}"
