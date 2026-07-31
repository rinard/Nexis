-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
/-! Authored `Defs` for `live` (bwd·may · gate). Carries its own node-locals (over `Tac.Vars`) so the
    gate emitter's short-name references resolve — the standalone bwd·may/gate reference analysis. -/
namespace BaseLanguage.Analyses.Live
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Std

section
variable (P : Program)

def useV (n : Node) : List Var   := match P.fetch n with | some i => instrUsedVars i | none => []
def defV (n : Node) : Option Var := match P.fetch n with | some i => instrDefVar  i | none => none
def usedVars (n : Node) : Vars := Vars.ofList (useV P n)
def rhsVars (n : Node) : Vars :=
  match P.fetch n with | some (Cmd.assign _ _ _) => usedVars P n | _ => Vars.empty
def defVars (n : Node) : Vars :=
  match defV P n with | some x => Vars.singleton x | none => Vars.empty
def condVars (n : Node) : Vars :=
  match P.fetch n with | some (Cmd.ifz _ _ _) => usedVars P n | _ => Vars.empty
def needed (n : Node) (liveSucc : Vars) : Vars :=
  match defV P n with
  | some x => if liveSucc.has x then rhsVars P n else Vars.empty
  | none   => Vars.empty
def allVars : Vars :=
  (Vars.ofList P.obs).union
    ((List.range P.size).foldl (fun acc n => acc.union ((usedVars P n).union (defVars P n))) ∅)
def liveSeed : Vars := Vars.ofList P.obs
end

-- The `Live` clause predicate is now GENERATED (meets-form gate) into `Seam/live/ValidExtremal.lean` by
-- `gen`; this file authors only the node-local defs it reads.
end BaseLanguage.Analyses.Live
