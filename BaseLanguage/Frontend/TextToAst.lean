-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Frontend.Ast

namespace BaseLanguage

/-!
# `TextToAst` — a recursive-descent parser from text to the surface AST (`Ast.Stmt`)

**Trusted / unverified** (parsers live in the TCB of verified compilers). The grammar covers **every**
`Tac.Binop`/`Unop`, so it is the exact surface counterpart of `AstToText` (the two round-trip).
Precedence runs loosest→tightest: `|`, `^`, `&`, comparison, shift, `+ -`, `* / %`, unary, atom.

```
stmt    := simple (';' simple)*
simple  := 'skip'
         | ident ':=' expr
         | 'if'    expr '{' stmt '}' ('else' '{' stmt '}')?   -- else-less `if` desugars to `else { skip }`
         | 'while' expr '{' stmt '}'
expr    := or
or      := xor   ('|' xor)*                          -- bitwise or
xor     := and   ('^' and)*                          -- bitwise xor
and     := cmp   ('&' cmp)*                           -- bitwise and
cmp     := shift (cmpop shift)?                       -- one comparison, non-associative
shift   := add   (('<<'|'>>'|'>>>') add)*             -- '<<' shl, '>>' logical (lshr), '>>>' arith (ashr)
add     := mul   (('+'|'-') mul)*
mul     := unary (('*'|'/'|'%') unary)*
unary   := ('-'|'~') unary | factor                  -- '-' negate, '~' bitwise not
factor  := ident | num | '(' expr ')'
cmpop   := '==' | '!=' | '<' | '<=' | '>' | '>='     -- signed
         | '<u' | '<=u' | '>u' | '>=u'               -- unsigned
```

The `>`-family swaps operands onto `lt`/`le`/`ltu`/`leu`. The `u`-suffixed comparisons are unsigned and
lexed as single tokens **when glued** (`a <u b`); a space (`a < u`) is signed `<` against a variable
named `u`. Truthiness is C-style (nonzero = true), matching `Ast.Stmt.ite`/`while`.
-/

namespace TextToAst
open Tac Ast

/-- Tokens. Keywords are recognised as `ident`s in the parser. -/
inductive Tok where
  | ident (s : String)
  | num   (n : Nat)
  | sym   (s : String)
  deriving DecidableEq, Repr, Inhabited

private def isIdentStart (c : Char) : Bool := c.isAlpha || c == '_'
private def isIdentCont  (c : Char) : Bool := c.isAlphanum || c == '_'

/-- Hand-rolled tokenizer over the character list. -/
partial def tokenize : List Char → List Tok
  | [] => []
  | c :: cs =>
    if c == '/' && (cs.head? == some '/') then tokenize (cs.dropWhile (· != '\n'))  -- `//` line comment
    else if c == ' ' || c == '\n' || c == '\t' || c == '\r' then tokenize cs
    else if c.isDigit then
      let (ds, rest) := (c :: cs).span (·.isDigit)
      .num (String.ofList ds).toNat! :: tokenize rest
    else if isIdentStart c then
      let (is, rest) := (c :: cs).span isIdentCont
      .ident (String.ofList is) :: tokenize rest
    else
      match c :: cs with
      | '=' :: '=' :: r        => .sym "==" :: tokenize r
      | ':' :: '=' :: r        => .sym ":=" :: tokenize r
      | '!' :: '=' :: r        => .sym "!=" :: tokenize r
      | '<' :: '=' :: 'u' :: r => .sym "<=u" :: tokenize r
      | '<' :: '=' :: r        => .sym "<=" :: tokenize r
      | '<' :: 'u' :: r        => .sym "<u" :: tokenize r
      | '<' :: '<' :: r        => .sym "<<" :: tokenize r
      | '>' :: '=' :: 'u' :: r => .sym ">=u" :: tokenize r
      | '>' :: '=' :: r        => .sym ">=" :: tokenize r
      | '>' :: 'u' :: r        => .sym ">u" :: tokenize r
      | '>' :: '>' :: '>' :: r => .sym ">>>" :: tokenize r
      | '>' :: '>' :: r        => .sym ">>" :: tokenize r
      | ch :: r                => .sym (String.ofList [ch]) :: tokenize r
      | []                     => []

/-- A parser: tokens in, `(result, leftover tokens)` out (`none` = parse error). -/
abbrev P (α : Type) := List Tok → Option (α × List Tok)

mutual
  partial def parseFactor : P Ast.Expr
    | .ident s :: r => some (.atom (.var (.orig s)), r)
    | .num n :: r   =>
        -- A bare literal is non-negative; reject `≥ 2^63` rather than silently wrapping through
        -- `Int64.ofNat` (negation is a separate unary op, so `Int64.minValue` is unwritable).
        if n < 2 ^ 63 then some (.atom (.imm (Int64.ofNat n)), r) else none
    | .sym "(" :: r =>
        match parseExpr r with
        | some (e, .sym ")" :: r') => some (e, r')
        | _ => none
    | _ => none

  partial def parseUnary : P Ast.Expr
    | .sym "-" :: r => (parseUnary r).map (fun (e, r') => (.una .neg e, r'))
    | .sym "~" :: r => (parseUnary r).map (fun (e, r') => (.una .not e, r'))
    | ts => parseFactor ts

  partial def parseMul : P Ast.Expr := fun ts =>
    (parseUnary ts).bind (fun (e, r) => mulTail e r)
  partial def mulTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "*" :: r => (parseUnary r).bind (fun (e2, r2) => mulTail (.bin .mul acc e2) r2)
    | .sym "/" :: r => (parseUnary r).bind (fun (e2, r2) => mulTail (.bin .div acc e2) r2)
    | .sym "%" :: r => (parseUnary r).bind (fun (e2, r2) => mulTail (.bin .mod acc e2) r2)
    | ts => some (acc, ts)

  partial def parseAdd : P Ast.Expr := fun ts =>
    (parseMul ts).bind (fun (e, r) => addTail e r)
  partial def addTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "+" :: r => (parseMul r).bind (fun (e2, r2) => addTail (.bin .add acc e2) r2)
    | .sym "-" :: r => (parseMul r).bind (fun (e2, r2) => addTail (.bin .sub acc e2) r2)
    | ts => some (acc, ts)

  partial def parseShift : P Ast.Expr := fun ts =>
    (parseAdd ts).bind (fun (e, r) => shiftTail e r)
  partial def shiftTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "<<"  :: r => (parseAdd r).bind (fun (e2, r2) => shiftTail (.bin .shl  acc e2) r2)
    | .sym ">>"  :: r => (parseAdd r).bind (fun (e2, r2) => shiftTail (.bin .lshr acc e2) r2)
    | .sym ">>>" :: r => (parseAdd r).bind (fun (e2, r2) => shiftTail (.bin .ashr acc e2) r2)
    | ts => some (acc, ts)

  /-- One optional, non-associative comparison on top of `shift`. The `>`-family swaps operands;
      `u`-suffixed forms are unsigned. -/
  partial def parseCmp : P Ast.Expr := fun ts =>
    (parseShift ts).bind (fun (e, r) =>
      match r with
      | .sym "=="  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .eq  e  e2, r3))
      | .sym "!="  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .ne  e  e2, r3))
      | .sym "<"   :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .lt  e  e2, r3))
      | .sym "<="  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .le  e  e2, r3))
      | .sym ">"   :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .lt  e2 e , r3))
      | .sym ">="  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .le  e2 e , r3))
      | .sym "<u"  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .ltu e  e2, r3))
      | .sym "<=u" :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .leu e  e2, r3))
      | .sym ">u"  :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .ltu e2 e , r3))
      | .sym ">=u" :: r2 => (parseShift r2).map (fun (e2, r3) => (.bin .leu e2 e , r3))
      | _ => some (e, r))

  partial def parseAnd : P Ast.Expr := fun ts =>
    (parseCmp ts).bind (fun (e, r) => andTail e r)
  partial def andTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "&" :: r => (parseCmp r).bind (fun (e2, r2) => andTail (.bin .and acc e2) r2)
    | ts => some (acc, ts)

  partial def parseXor : P Ast.Expr := fun ts =>
    (parseAnd ts).bind (fun (e, r) => xorTail e r)
  partial def xorTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "^" :: r => (parseAnd r).bind (fun (e2, r2) => xorTail (.bin .xor acc e2) r2)
    | ts => some (acc, ts)

  /-- Top of the expression grammar: bitwise-or, loosest-binding. -/
  partial def parseExpr : P Ast.Expr := fun ts =>
    (parseXor ts).bind (fun (e, r) => orTail e r)
  partial def orTail (acc : Ast.Expr) : P Ast.Expr
    | .sym "|" :: r => (parseXor r).bind (fun (e2, r2) => orTail (.bin .or acc e2) r2)
    | ts => some (acc, ts)
end

mutual
  partial def parseSimple : P Ast.Stmt
    | .ident "skip" :: r => some (.skip, r)
    | .ident "if" :: r =>
        match parseExpr r with
        | some (c, .sym "{" :: r2) =>
            match parseStmt r2 with
            | some (t, .sym "}" :: .ident "else" :: .sym "{" :: r3) =>
                match parseStmt r3 with
                | some (e, .sym "}" :: r4) => some (.ite c t e, r4)
                | _ => none
            | some (t, .sym "}" :: r3) => some (.ite c t .skip, r3)  -- else-less `if`: desugar to `skip`
            | _ => none
        | _ => none
    | .ident "while" :: r =>
        match parseExpr r with
        | some (c, .sym "{" :: r2) =>
            match parseStmt r2 with
            | some (b, .sym "}" :: r3) => some (.while c b, r3)
            | _ => none
        | _ => none
    | .ident x :: .sym ":=" :: r =>
        (parseExpr r).map (fun (e, r') => (.assign (.orig x) e, r'))
    | _ => none

  /-- Statement sequencing on `;` (a trailing `;` is tolerated). -/
  partial def parseStmt : P Ast.Stmt := fun ts =>
    (parseSimple ts).bind (fun (s, r) =>
      match r with
      | .sym ";" :: r2 =>
          match parseStmt r2 with
          | some (s2, r3) => some (.seq s s2, r3)
          | none => some (s, r2)            -- trailing ';'
      | _ => some (s, r))
end

/-- **Parse a program from text** (`none` on error or unconsumed input, after dropping trailing
    `;`). -/
def parse (src : String) : Option Ast.Stmt :=
  match parseStmt (tokenize src.toList) with
  | some (s, rest) => if rest.all (· == .sym ";") then some s else none
  | none => none

end TextToAst

end BaseLanguage
