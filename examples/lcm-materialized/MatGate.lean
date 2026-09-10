-- Copyright (c) 2026 Martin Rinard
import Seam.lcmmat.Adapter
import BaseLanguage.LCM.Transform
import BaseLanguage.IR.Pretty

/-!
# The materialization gate, measured against the classical one

LCM's transform decides whether to rewrite an original `x := e` into `x := tₑ` by consulting the
**replace gate**

```
recoverable P S n = πᵤK(n) ∪ insertBefore(n)          -- BaseLanguage/LCM/Transform.lean
```

and that gate is why LCM's correctness proof assumes `Extremal S` rather than validity: a valid but
too-large `πᵤ` admits a rewrite with no matching insertion, and the program then reads a temporary nothing
ever wrote (`examples/lcm-extremality/ExtremalityNeeded.lean`). Ruling that out needs a *lower* bound on a
*least* fixpoint — irreducibly second-order, expressible by no clause.

`analyses/lcmmat/LcmMat.gsl` adds a seventh ghost, `Materialized ηₘ`, whose governing clause is an *upper*
bound and therefore a consequence of validity. The proposed gate reads it:

```
matRecoverable P S n = ηₘ(n) ∪ insertBefore(n)
```

(`insertBefore` appears in both because `ηₘ` is indexed at block *entry*, before the entry chain runs, so
a temporary materialized by `insertBefore(n)` is not yet in `ηₘ(n)`.)

Two open questions decide whether the swap is worth making, and this file measures both on real programs:

* **soundness** — is `matRecoverable ⊆` what the transform actually materializes? Not measured here; that
  is a lemma about the transform, not a set comparison.
* **optimization power** — is `recoverable ⊆ matRecoverable`? If the containment ever failed, the new gate
  would replace *less* than the classical one and the swap would cost optimization. The reverse containment
  failing is expected and harmless: `ηₘ` is a forward availability property and `πᵤ` a backward demand
  property, so a temporary can be available where it is not demanded.

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

/-- The proposed replace gate: availability of the temporary, plus what is born at this node. -/
def matRecoverable (P : Program) (S : LcmSpec P) (m : Node → Assignments) (n : Node) : Assignments :=
  Assignments.union (m n) (insertBefore P S n)

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
  let m := matAvail P
  IO.println s!"===== {nm} ({P.size} nodes) ====="
  let mut powerOk := true
  let mut strictlyBigger := false
  for n in List.range P.size do
    let cls := recoverable P S n
    let mat := matRecoverable P S m n
    let clsL := cls.toList
    let matL := mat.toList
    let sub  := clsL.all (fun e => mat.contains e)
    let sup  := matL.all (fun e => cls.contains e)
    if !sub then powerOk := false
    if !sup then strictlyBigger := true
    if !clsL.isEmpty || !matL.isEmpty then
      IO.println s!"  n={n}  classic={clsL.length}  mat={matL.length}  \
classic⊆mat={sub}  mat⊆classic={sup}"
  IO.println s!"  --> power preserved (classic ⊆ mat everywhere): {powerOk}"
  IO.println s!"  --> mat strictly larger somewhere: {strictlyBigger}"

#eval do
  show' "Pred  (partial redundancy)" Pred  (by native_decide)
  show' "Ploop (loop invariant)"     Ploop (by native_decide)
  show' "Pfull (full redundancy)"    Pfull (by native_decide)
