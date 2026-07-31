-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Domain

/-!
# `PDCE.PdceDefs` — the PDCE node-local sets (pure Lean).

The authored inputs to the generator: node-local defs (born/allAsgns/rhsVars/defVars/condVars/
kills/pass/allVars/liveSeed/sinkSeed) + the `Greatest`/`Least` extremality helpers. These are the
irreducibly-authored part of PDCE — the program set-operations the generator cannot synthesize.

`gen` (`GenGeneral`) parses `Pdce.gsl` and emits `Solver/pdce/Solve.lean` + `Seam/pdce/ValidExtremal.lean`
from these defs: the ghost predicates `Live`/`Sink`, the solver, and the uniform
`PDCEResult`/`Valid`/`Extremal` interface are all GENERATED. The `PdceSpec` validity bundle that the
verified transform consumes is a thin adapter over that interface, authored downstream in `PdceAdapter.lean`.
Cross-domain: `Assignments = HashSet Asgn`, plus `Variables`.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-! ## §2  Node-locals.  (Comments marked `-- define:` show the equivalent `define` DSL clause
    each `def` implements.) -/

section
variable (P : Program)
local notation:max "cmd " n:max => P.fetch n

-- define: born (n) : Assignments match cmd n with | (x := e) => {⟨x, e⟩} | _ => ∅
def born (n : Node) : Assignments :=
  match cmd n with
  | some (Cmd.assign x e _) => Assignments.singleton ⟨x, e⟩
  | _                       => ∅

-- define: allAsgns : Assignments := ⋃ n, born n
def allAsgns : Assignments :=
  (List.range P.size).foldl (fun acc n => acc.union (born P n)) ∅

def useV (n : Node) : List Var   := match cmd n with | some i => instrUsedVars i | none => []
def defV (n : Node) : Option Var := match cmd n with | some i => instrDefVar  i | none => none
def usedVars (n : Node) : Variables := Variables.ofList (useV P n)

-- define: rhsVars (n) : Variables match cmd n with | (_ := _) => usedVars n | _ => ∅
def rhsVars (n : Node) : Variables :=
  match cmd n with
  | some (Cmd.assign _ _ _) => usedVars P n
  | _                       => ∅

def defVars (n : Node) : Variables :=
  match defV P n with | some x => Variables.singleton x | none => Variables.empty

-- define: condVars (n) : Variables match cmd n with | ifz _ => usedVars n | _ => ∅
def condVars (n : Node) : Variables :=
  match cmd n with
  | some (Cmd.ifz _ _ _) => usedVars P n
  | _                    => ∅

def kills (n : Node) (a : Asgn) : Bool :=
  (useV P n).contains a.lhs || (defV P n == some a.lhs)
    || (match defV P n with | some w => exprReadsVar a.rhs w | none => false)

def pass (n : Node) : Assignments := (allAsgns P).filter (fun a => ! kills P n a)

-- define: allVars : Variables := ⟨Variables.ofList P.obs⟩ ∪ ⋃ n, usedVars n ∪ defVars n
def allVars : Variables :=
  (Variables.ofList P.obs).union
    ((List.range P.size).foldl
      (fun acc n => acc.union ((usedVars P n).union (defVars P n))) ∅)

def liveSeed : Variables := Variables.ofList P.obs
def sinkSeed (P : Program) : Assignments := Assignments.empty
end

/-! ## Extremality helpers (used by the optimality developments). -/

def Greatest {γ : Type} (sub : γ → γ → Prop) (S : (Node → γ) → Prop) (g : Node → γ) : Prop :=
  S g ∧ ∀ g', S g' → ∀ n, sub (g' n) (g n)
def Least {γ : Type} (sub : γ → γ → Prop) (S : (Node → γ) → Prop) (g : Node → γ) : Prop :=
  S g ∧ ∀ g', S g' → ∀ n, sub (g n) (g' n)

end BaseLanguage.Analyses.PDCE
