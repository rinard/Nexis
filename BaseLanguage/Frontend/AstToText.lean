-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Frontend.Ast

namespace BaseLanguage

/-!
# `AstToText` — unparser: surface AST (`Ast.Stmt`) → source text

The inverse of `TextToAst.parse` for the parseable language subset: it pretty-prints an `Ast.Stmt`
to source text that `TextToAst.parse` reads back to the same AST. Expressions are printed with
**precedence-aware** parenthesization (parens only where the structure requires them); statements
are indented two spaces per nesting level.

Every `Binop`/`Unop` has surface syntax — bitwise `& | ^ ~`, shifts `<< >> >>>`, and signed and
unsigned comparisons — so `parse (emitText s)` round-trips any AST `s` the parser produces (variables
all source (`.orig`) names, `imm` literals non-negative). A hand-built *negative* `imm` atom prints as
`-n` and re-parses as `neg (imm n)` — the same value, which is what the test suite checks (round-trip
up to evaluation, `roundVar`).
-/

namespace AstToText
open Tac Ast

/-- Operator token. -/
def binSym : Binop → String
  | .add => "+"  | .sub => "-"  | .mul => "*"   | .div => "/"  | .mod => "%"
  | .and => "&"  | .or  => "|"  | .xor => "^"
  | .shl => "<<" | .lshr => ">>" | .ashr => ">>>"
  | .eq  => "==" | .ne  => "!=" | .lt  => "<"   | .le  => "<="
  | .ltu => "<u" | .leu => "<=u"

/-- Binding precedence (higher binds tighter), matching `TextToAst`'s grammar ladder exactly:
    `|` < `^` < `&` < comparison < shift < `+ -` < `* / %`. -/
def binPrec : Binop → Nat
  | .or  => 1 | .xor => 2 | .and => 3
  | .eq | .ne | .lt | .le | .ltu | .leu => 4
  | .shl | .lshr | .ashr => 5
  | .add | .sub => 6
  | .mul | .div | .mod => 7

/-- Comparisons are non-associative: their operands print one level tighter, so a nested comparison
    gets parenthesized (the grammar allows only one comparison per `cmp`). -/
def isCmp : Binop → Bool
  | .eq | .ne | .lt | .le | .ltu | .leu => true
  | _ => false

def unSym : Unop → String
  | .neg => "-" | .not => "~"

def varName : Var → String
  | .orig s => s
  | .tmp i  => s!"t{i}"

def atomStr : Atom → String
  | .var x => varName x
  | .imm n => toString n.toInt

/-- Parenthesize iff the surrounding context binds tighter than this expression. -/
@[inline] def parenIf (b : Bool) (s : String) : String := if b then "(" ++ s ++ ")" else s

/-- Print an expression for a context of binding precedence `ctx` (unary binds at 8, atoms at 9, so
    they never need parentheses). Left operands recurse at the operator's precedence, right operands
    at one higher — matching the parser's left-associativity / non-associative comparison. -/
def exprP (ctx : Nat) : Ast.Expr → String
  | .atom a     => atomStr a
  | .una op e   => parenIf (ctx > 8) (unSym op ++ exprP 8 e)
  | .bin op a b =>
      let p := binPrec op
      let lctx := if isCmp op then p + 1 else p
      parenIf (ctx > p) (exprP lctx a ++ " " ++ binSym op ++ " " ++ exprP (p + 1) b)

/-- An expression as source text (no enclosing parentheses). -/
def exprText (e : Ast.Expr) : String := exprP 0 e

def indent (n : Nat) : String := String.ofList (List.replicate (2 * n) ' ')

/-- Print a statement at indentation depth `n`. -/
def stmtP (n : Nat) : Ast.Stmt → String
  | .skip       => indent n ++ "skip"
  | .assign x e => indent n ++ varName x ++ " := " ++ exprText e
  | .seq s₁ s₂  => stmtP n s₁ ++ ";\n" ++ stmtP n s₂
  | .ite c t e  =>
      indent n ++ "if " ++ exprText c ++ " {\n" ++ stmtP (n + 1) t ++ "\n" ++
      indent n ++ "} else {\n" ++ stmtP (n + 1) e ++ "\n" ++ indent n ++ "}"
  | .while c b  =>
      indent n ++ "while " ++ exprText c ++ " {\n" ++ stmtP (n + 1) b ++ "\n" ++ indent n ++ "}"

/-- **Emit the source text of a surface program.** -/
def emitText (s : Ast.Stmt) : String := stmtP 0 s

end AstToText

end BaseLanguage
