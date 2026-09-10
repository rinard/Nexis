-- Copyright (c) 2026 Martin Rinard
import Seam.lcmmat.Adapter
import BaseLanguage.LCM.Transform
import BaseLanguage.IR.Pretty

/-!
# The materialization gate, measured against the classical one

LCM's transform decides whether to rewrite an original `x := e` into `x := tₑ` by consulting the
**replace gate**, and `LCM.GateMode` chooses which ghost that gate reads. Both settings are shipped and
proved. The classical one reads the backward *demand* ghost `πᵤ`:

```
recoverable P S n = πᵤK(n) ∪ insertBefore(n)          -- S.gate = .demand
```

and that gate is why LCM's correctness proof needs `Extremal S` rather than validity: a valid but
too-large `πᵤ` admits a rewrite with no matching insertion, and the program then reads a temporary nothing
ever wrote (`examples/lcm-extremality/ExtremalityNeeded.lean`). Ruling that out needs a *lower* bound on a
*least* fixpoint — irreducibly second-order, expressible by no clause.

`analyses/lcmmat/LcmMat.gsl` adds a seventh ghost, `Materialized ηₘ`, whose governing clause is an *upper*
bound and therefore a consequence of validity. The other gate reads it:

```
recoverable P S n = ηₘK(n) ∪ insertBefore(n)          -- S.gate = .materialized
```

(`insertBefore` appears in both because `ηₘ` is indexed at block *entry*, before the entry chain runs, so
a temporary materialized by `insertBefore(n)` is not yet in `ηₘ(n)`.)

Soundness of each is settled in Lean: `transform_preserves_halt_demand` takes `Extremal S`,
`transform_preserves_halt_mat` does not, and `Seam/lcmmat/Sound.lean` shows the analysis-level half
directly. What Lean settles *separately* is that choosing `.materialized` costs no **optimization
power** — `demand_materialized` (`Correctness/MatchStep.lean`) proves the containment for an extremal
bundle. This file is the measurement behind that theorem: it evaluates both gates, node by node, on
three real programs, by running the *same* bundle through `withGate`.

The reverse containment failing is expected and harmless: `ηₘ` is a forward availability property and
`πᵤ` a backward demand property, so a temporary can be available where it is not demanded.

Run: `lake env lean examples/lcm-materialized/MatGate.lean`

**Axioms.** Eval-only — no theorem is stated here, and `WellFormed` is discharged by `native_decide`, so
this exhibit is deliberately outside the axiom-clean gate (unlike `ExtremalityNeeded.lean`). It measures;
it does not prove.
-/
open BaseLanguage BaseLanguage.Tac BaseLanguage.Semantics
open BaseLanguage.Analyses.LCM BaseLanguage.Analyses.LcmMat

def va : Var := .orig "a"
def vb : Var := .orig "b"
def vc : Var := .orig "c"
def vx : Var := .orig "x"
def vy : Var := .orig "y"
def E : Expr := .bin .add (.var va) (.var vb)

/-- Partial redundancy: `a+b` computed on one arm only, then used at the join. -/
def Pred : Program :=
  { entry := 0
  , code  := #[ Cmd.noop 1, Cmd.ifz vc 2 3, Cmd.assign vx E 3, Cmd.assign vy E 4, Cmd.halt ]
  , obs   := [vx, vy] }

/-- Loop-invariant computation inside a loop body. -/
def Ploop : Program :=
  { entry := 0
  , code  := #[ Cmd.noop 1, Cmd.ifz vc 2 4, Cmd.assign vx E 3, Cmd.noop 1, Cmd.halt ]
  , obs   := [vx] }

/-- Full redundancy: the same expression twice in a row. -/
def Pfull : Program :=
  { entry := 0
  , code  := #[ Cmd.noop 1, Cmd.assign vx E 2, Cmd.assign vy E 3, Cmd.halt ]
  , obs   := [vx, vy] }

def show' (nm : String) (P : Program) (wf : WellFormed P) : IO Unit := do
  let S := lcmMatSolved P wf
  IO.println s!"===== {nm} ({P.size} nodes) ====="
  let mut powerOk := true
  let mut strictlyBigger := false
  for n in List.range P.size do
    let cls := recoverable P (S.withGate .demand) n
    let mat := recoverable P (S.withGate .materialized) n
    let clsL := cls.toList
    let matL := mat.toList
    let sub  := clsL.all (fun e => mat.contains e)
    let sup  := matL.all (fun e => cls.contains e)
    if !sub then powerOk := false
    if !sup then strictlyBigger := true
    if !clsL.isEmpty || !matL.isEmpty then
      IO.println s!"  n={n}  demand={clsL.length}  mat={matL.length}  \
demand⊆mat={sub}  mat⊆demand={sup}"
  IO.println s!"  --> power preserved (demand ⊆ materialized everywhere): {powerOk}"
  IO.println s!"  --> materialized strictly larger somewhere: {strictlyBigger}"

#eval do
  show' "Pred  (partial redundancy)" Pred  (by native_decide)
  show' "Ploop (loop invariant)"     Ploop (by native_decide)
  show' "Pfull (full redundancy)"    Pfull (by native_decide)
