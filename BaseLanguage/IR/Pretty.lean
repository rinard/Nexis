-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

/-!
# `Tac.Pretty` — human-readable dump of the CFG IR (`Program`)

An **unverified** printer for the three-address IR, used by `prophecyc --show-opt` to show a program
before and after the LCM/PDCE optimizations. One line per CFG node (`L<i>: <cmd>  → <succ>`), with the
entry marked `>` and the observable set listed at the end. Compiler temporaries print as `t<i>` (the
`AsmToText.varName` convention); original source variables print by name.
-/

namespace BaseLanguage
namespace Tac

def ppVar : Var → String
  | .orig s => s
  | .tmp i  => s!"t{i}"

def ppAtom : Atom → String
  | .var x => ppVar x
  | .imm n => toString n

def ppUnop : Unop → String
  | .neg => "-" | .not => "~"

def ppBinop : Binop → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .and => "&" | .or  => "|" | .xor => "^"
  | .shl => "<<" | .lshr => ">>" | .ashr => ">>>"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .ltu => "<u" | .leu => "<=u"

def ppExpr : Expr → String
  | .atom a     => ppAtom a
  | .una op a   => s!"{ppUnop op}{ppAtom a}"
  | .bin op a b => s!"{ppAtom a} {ppBinop op} {ppAtom b}"

def ppCmd : Cmd → String
  | .assign x e next => s!"{ppVar x} := {ppExpr e}    → L{next}"
  | .ifz x z nz      => s!"ifz {ppVar x}    zero → L{z}   nonzero → L{nz}"
  | .noop next       => s!"noop    → L{next}"
  | .halt            => "halt"

/-- Render a whole `Program` as a multi-line CFG listing. -/
def ppProgram (P : Program) : String :=
  let nodes := (List.range P.code.size).map (fun i =>
    let mark := if i == P.entry then ">" else " "
    s!"{mark} L{i}: {ppCmd (P.code[i]!)}")
  let obs := s!"obs = [{String.intercalate ", " (P.obs.map ppVar)}]"
  String.intercalate "\n" (s!"entry = L{P.entry}" :: nodes ++ ["", obs])

end Tac
end BaseLanguage
