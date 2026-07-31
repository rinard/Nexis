-- Copyright (c) 2026 Martin Rinard
import GenGeneral.IR

/-!
# `GenGeneral.Lex` — a positioned lexer for the `.gsl` surface

Scans source into `Token`s that each carry a 1-based `Pos` (line/column), so every parser diagnostic is
**located** (the totality contract). Comments (`-- … EOL`) are stripped;
each grammar symbol (`{ } ( ) [ ] : . , ∀ → ∪ ∩ ∖ ⊆ ∈ ∅ ∧ ∨ ∃`) is a standalone token; identifiers run
`letter { letter | digit | "'" }` (so `n'`/`avail'` lex as one token). No silent failure — an
unrecognised character is a located error.
-/

namespace GenGeneral

/-- A lexed token: its text plus the source position of its first character. -/
structure Token where
  text : String
  pos  : Pos
deriving Inhabited, Repr, BEq

/-- The single-character grammar symbols punched out as standalone tokens. -/
def symbolChars : List Char :=
  ['{', '}', '(', ')', '[', ']', ':', '.', ',', '∀', '→', '∪', '∩', '∖', '⊆', '∈', '∅', '∧', '∨', '∃']

private def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\''
    || (0x0370 ≤ c.val && c.val ≤ 0x03FF)   -- Greek and Coptic (π η τ …)
    || (0x2080 ≤ c.val && c.val ≤ 0x209C)   -- subscripts (ₐ ₑ ₚ …)
    || (0x1D62 ≤ c.val && c.val ≤ 0x1D6A)   -- phonetic subscripts (ᵢ ᵣ ᵤ ᵥ)

/-- Lex one line (0 comments already stripped) starting at `line`, columns 1-based. -/
private partial def lexLine (line : Nat) (cs : List Char) : Res (List Token) :=
  go 1 cs
where
  go (col : Nat) : List Char → Res (List Token)
    | [] => .ok []
    | c :: rest =>
      if c == ' ' || c == '\t' then
        go (col + 1) rest
      else if symbolChars.contains c then
        (·.cons { text := String.singleton c, pos := { line, col } }) <$> go (col + 1) rest
      else if isIdentChar c then
        let ident := c :: rest.takeWhile isIdentChar
        let n := ident.length
        (·.cons { text := String.ofList ident, pos := { line, col } }) <$> go (col + n) (rest.drop (n - 1))
      else
        err { line, col } s!"unexpected character '{c}'"

/-- Strip a `--` line comment (to EOL). -/
private def stripComment (cs : List Char) : List Char :=
  match cs with
  | [] => []
  | '-' :: '-' :: _ => []
  | c :: rest => c :: stripComment rest

/-- Lex the whole source. Lines are 1-based; comments removed; tokens carry positions. -/
def lex (src : String) : Res (List Token) := do
  let mut toks : List Token := []
  let mut line := 1
  for l in src.splitOn "\n" do
    toks := toks ++ (← lexLine line (stripComment l.toList))
    line := line + 1
  return toks

end GenGeneral
