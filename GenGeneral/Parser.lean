-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Lex

/-!
# `GenGeneral.Parser` — recursive-descent parser: tokens → surface AST

Parses the grammar (`docs/GENERAL-PIPELINE-EBNF.md`) into a positioned surface AST
(`GhostBlock`), reusing the `SetExpr` precedence core (`∩`/`∖` tighter than `∪`, all left-assoc) and
extending it with the `when`-guard grammar (`meets`/`∃…∈`/`⊆` compound atoms). **Total**: every function
returns `Res` — a value or a located `Err`, never a silent failure. The AST → `AnalysisIR` lowering is
`GenGeneral.Lower`.
-/

namespace GenGeneral

/-- Whether a token text is exactly one grammar symbol (so it cannot be an identifier). -/
def isSymbolText (s : String) : Bool := s.length == 1 && symbolChars.contains (s.toList.headD ' ')

/-! ## Surface AST -/

/-- A set expression (`SetExpr` in the EBNF). Leaves are `FamilyRef`s (name + placement params + node
    args); `∅` is `empty`. The parser does not resolve a leaf's kind (ghost vs family) — that is the
    symbol table's job in `Lower`. -/
inductive SetExpr where
  | ref   (r : FamilyRef)
  | empty
  | union (a b : SetExpr)
  | inter (a b : SetExpr)
  | diff  (a b : SetExpr)
deriving Inhabited, Repr, BEq

/-- A `when` guard (monotone in the incoming ghost). -/
inductive GuardE where
  | meets  (sng : SetExpr) (inRef : FamilyRef)                 -- gate:   sng meets in
  | img    (y : String) (inRef : FamilyRef) (rel : RelRef)     -- image:  ∃ y ∈ in. R(y,z)
  | subOf  (sub : SetExpr) (inRef : FamilyRef)                 -- gather: sub(z) ⊆ in
  | mem    (z : String) (inRef : FamilyRef)                    -- diagonal: z ∈ in
  | memC   (z : String) (src : SetExpr)                        -- constant: z ∈ source(n)
  | and    (a b : GuardE)
  | or     (a b : GuardE)
deriving Inhabited, Repr

/-- A parsed clause. `perEdge` records the quantifier form (`∀ n→n'` vs `∀ n`/none). A guarded condition
    carries its guard and the self side (set-level `SetExpr ⊆ Self`, or per-element `Elem ∈ Self`). -/
structure Clause where
  kw      : String
  perEdge : Bool := false
  lhs     : SetExpr := .empty
  rhs     : SetExpr := .empty
  guarded : Bool := false
  guardElem : String := ""        -- per-element guarded: the output element `z` (else "")
  guard   : Option GuardE := none
  pos     : Pos := {}
deriving Inhabited, Repr

/-- A parsed ghost block. -/
structure GhostBlock where
  dir     : String        -- history | prophecy
  name    : String
  carried : String
  dom     : String
  elem    : String := ""  -- element type from the mandatory `[Elem]` annotation (e.g. `Assignments[Expr]`)
  clauses : List Clause
  pos     : Pos := {}
deriving Inhabited, Repr

/-! ## Token-stream helpers -/

/-- Position to blame when the stream is at a given point (the head token, or a synthetic EOF). -/
def hdPos : List Token → Pos
  | t :: _ => t.pos
  | []     => { line := 0, col := 0 }

def hdText : List Token → String
  | t :: _ => t.text
  | []     => "<eof>"

/-- Consume a specific token or fail with a located error. -/
def expect (want : String) : List Token → Res (List Token)
  | t :: rest => if t.text == want then .ok rest else err t.pos s!"expected '{want}', found '{t.text}'"
  | []        => err {} s!"expected '{want}', found end of input"

/-- Consume an identifier (any token that is not a reserved symbol/keyword-position); returns it. -/
def expectIdent (what : String) : List Token → Res (String × List Token)
  | t :: rest =>
    if isSymbolText t.text then
      err t.pos s!"expected {what}, found symbol '{t.text}'"
    else .ok (t.text, rest)
  | [] => err {} s!"expected {what}, found end of input"

/-! ## Node-arg / reference parsing -/

/-- Parse a parenthesised comma-separated list of tokens `( a , b )` (already positioned at `(`). -/
partial def parseParenList : List Token → Res (List String × List Token)
  | t :: rest =>
    if t.text == "(" then go [] rest else err t.pos "expected '('"
  | [] => err {} "expected '(' , found end of input"
where
  go (acc : List String) : List Token → Res (List String × List Token)
    | t :: rest =>
      if t.text == ")" then .ok (acc.reverse, rest)
      else if t.text == "," then go acc rest
      else go (t.text :: acc) rest
    | [] => err {} "unterminated '(' — expected ')'"

/-- Parse a `Ref`: `identifier [ Params ] [ (NodeArg) ]`. Uses two-paren disambiguation — a
    first paren group followed by a second `(` is `Params` (foreign ghosts), the second is the node args;
    a single group is the node args. -/
def parseRef (nm : String) (ts : List Token) : Res (FamilyRef × List Token) := do
  match ts with
  | t :: _ =>
    if t.text == "(" then
      let (g1, r1) ← parseParenList ts
      match r1 with
      | u :: _ =>
        if u.text == "(" then
          let (g2, r2) ← parseParenList r1
          .ok ({ name := nm, params := g1, nodes := g2 }, r2)
        else .ok ({ name := nm, nodes := g1 }, r1)
      | [] => .ok ({ name := nm, nodes := g1 }, r1)
    else .ok ({ name := nm }, ts)
  | [] => .ok ({ name := nm }, ts)

/-! ## SetExpr precedence core (`∩`/`∖` tighter than `∪`; left-assoc) -/

mutual
partial def parseSetTerm : List Token → Res (SetExpr × List Token)
  | t :: rest =>
    if t.text == "∅" then .ok (.empty, rest)
    else if t.text == "(" then do
      let (e, r) ← parseSetExpr rest
      let r ← expect ")" r
      .ok (e, r)
    else if isSymbolText t.text then
      err t.pos s!"expected a set term, found '{t.text}'"
    else do
      let (r, rest') ← parseRef t.text rest
      .ok (.ref r, rest')
  | [] => err {} "expected a set term, found end of input"

partial def parseSetInter (ts : List Token) : Res (SetExpr × List Token) := do
  let (a, r) ← parseSetTerm ts
  go a r
where
  go (a : SetExpr) : List Token → Res (SetExpr × List Token)
    | op :: r' =>
      if op.text == "∩" then do let (b, r'') ← parseSetTerm r'; go (.inter a b) r''
      else if op.text == "∖" then do let (b, r'') ← parseSetTerm r'; go (.diff a b) r''
      else .ok (a, op :: r')
    | [] => .ok (a, [])

partial def parseSetExpr (ts : List Token) : Res (SetExpr × List Token) := do
  let (a, r) ← parseSetInter ts
  go a r
where
  go (a : SetExpr) : List Token → Res (SetExpr × List Token)
    | op :: r' =>
      if op.text == "∪" then do let (b, r'') ← parseSetInter r'; go (.union a b) r''
      else .ok (a, op :: r')
    | [] => .ok (a, [])
end

/-! ## Guard grammar -/

/-- Parse `Rel`: `identifier [ (NodeArg) ] ( Elem , Elem )`. -/
def parseRel : List Token → Res (RelRef × List Token)
  | t :: rest => do
    let (r1, after) ← parseRef t.text rest
    -- `parseRef` will have absorbed the first paren group as `nodes`; if a second group followed it was
    -- treated as node args. For a relation the element pair `(y,z)` is the *last* group; anything before
    -- it is the node index. `parseRef` already split node index (params) vs the trailing group (nodes).
    .ok ({ name := r1.name, nodes := r1.params }, after)
  | [] => err {} "expected a relation, found end of input"

mutual
partial def parseGuardAtom : List Token → Res (GuardE × List Token)
  | t :: rest =>
    if t.text == "(" then do
      let (g, r) ← parseGuard rest
      let r ← expect ")" r
      .ok (g, r)
    else if t.text == "∃" then do
      let (y, r0) ← expectIdent "an ∃-bound element" rest
      let r1 ← expect "∈" r0
      let (inNm, r2) ← expectIdent "the incoming ghost" r1
      let (inRef, r3) ← parseRef inNm r2
      let r4 ← expect "." r3
      let (rel, r5) ← parseRel r4
      .ok (.img y inRef rel, r5)
    else do
      -- SetExpr then an operator: `meets` (gate), `⊆` (gather), or `∈` (mem/constant).
      let (lhs, r) ← parseSetExpr (t :: rest)
      match r with
      | op :: r' =>
        if op.text == "meets" then do
          let (nm, r2) ← expectIdent "the incoming ghost" r'
          let (inRef, r3) ← parseRef nm r2
          .ok (.meets lhs inRef, r3)
        else if op.text == "⊆" then do
          let (nm, r2) ← expectIdent "the incoming ghost" r'
          let (inRef, r3) ← parseRef nm r2
          .ok (.subOf lhs inRef, r3)
        else if op.text == "∈" then do
          -- `z ∈ Ref`: diagonal if RHS is a bare ref, constant otherwise. `lhs` must be a single element.
          let z ← match lhs with
            | .ref r => .ok r.name
            | _      => err op.pos "the left of `∈` in a guard must be a single element, not a compound"
          let (nm, r2) ← expectIdent "a set" r'
          let (rhsRef, r3) ← parseRef nm r2
          if rhsRef.params.isEmpty && rhsRef.nodes.length ≤ 1 then
            .ok (.mem z rhsRef, r3)
          else .ok (.memC z (.ref rhsRef), r3)
        else err op.pos s!"expected 'meets', '⊆', or '∈' in a guard, found '{op.text}'"
      | [] => err {} "unterminated guard"
  | [] => err {} "expected a guard atom, found end of input"

partial def parseGuardAnd (ts : List Token) : Res (GuardE × List Token) := do
  let (a, r) ← parseGuardAtom ts
  go a r
where
  go (a : GuardE) : List Token → Res (GuardE × List Token)
    | op :: r' =>
      if op.text == "∧" || op.text == "and" then do let (b, r'') ← parseGuardAtom r'; go (.and a b) r''
      else .ok (a, op :: r')
    | [] => .ok (a, [])

partial def parseGuard (ts : List Token) : Res (GuardE × List Token) := do
  let (a, r) ← parseGuardAnd ts
  go a r
where
  go (a : GuardE) : List Token → Res (GuardE × List Token)
    | op :: r' =>
      if op.text == "∨" || op.text == "or" then do let (b, r'') ← parseGuardAnd r'; go (.or a b) r''
      else .ok (a, op :: r')
    | [] => .ok (a, [])
end

/-! ## Quantifier + clause body -/

/-- Drop a leading quantifier `∀ n→n' .` (per-edge) or `∀ n .` (per-config); report whether it was
    per-edge. The binder between `∀` and the terminating `.` must be exactly `n` or `n → n'` — any other
    shape (a missing `.`, a stray token, a mis-spelled endpoint) is a located error, not a silent accept. -/
def parseQuant : List Token → Res (Bool × List Token)
  | t :: rest =>
    if t.text == "∀" then
      if !(rest.any (·.text == ".")) then err t.pos "missing `.` terminating the `∀` quantifier"
      else
        let binder := (rest.takeWhile (·.text != ".")).map (·.text)
        let rest'  := (rest.dropWhile (·.text != ".")).drop 1
        match binder with
        | ["n"]            => .ok (false, rest')
        | ["n", "→", "n'"] => .ok (true, rest')
        | _ =>
          let shown := String.intercalate " " binder
          err t.pos s!"expected `∀ n.` (per-config) or `∀ n→n'.` (per-edge), found `∀ {shown}.`"
    else .ok (false, t :: rest)
  | [] => .ok (false, [])

/-- Parse one clause body (after the keyword `:`), given the keyword. -/
def parseClauseBody (kw : String) (pos : Pos) (ts : List Token) : Res Clause := do
  let (perEdge, ts) ← parseQuant ts
  let isGuarded := ts.any (·.text == "when")
  if isGuarded then
    -- `SetExpr ⊆ Self when Guard` or `Elem ∈ Self when Guard`
    let upto := ts.takeWhile (·.text != "when")
    let after := (ts.dropWhile (·.text != "when")).drop 1
    match upto with
    | t :: rest =>
      if rest.any (·.text == "∈") && !(rest.any (·.text == "⊆")) then do
        -- per-element `z ∈ Self`
        let z := t.text
        let r0 ← expect "∈" rest
        let (selfNm, r1) ← expectIdent "the carried ghost" r0
        let (selfRef, _) ← parseRef selfNm r1
        let (g, _) ← parseGuard after
        .ok { kw, perEdge, guarded := true, guardElem := z, guard := some g,
              rhs := .ref selfRef, pos }
      else do
        -- set-level `SetExpr ⊆ Self`
        let (lhs, r) ← parseSetExpr upto
        let r ← expect "⊆" r
        let (selfNm, r1) ← expectIdent "the carried ghost" r
        let (selfRef, _) ← parseRef selfNm r1
        let (g, _) ← parseGuard after
        .ok { kw, perEdge, guarded := true, lhs, rhs := .ref selfRef, guard := some g, pos }
    | [] => err pos "empty guarded clause"
  else do
    -- plain inclusion `A ⊆ B`
    let (lhs, r) ← parseSetExpr ts
    match r with
    | op :: r' =>
      if op.text == "⊆" then do
        let (rhs, _) ← parseSetExpr r'
        .ok { kw, perEdge, lhs, rhs, pos }
      else err op.pos s!"expected '⊆' in clause, found '{op.text}'"
    | [] =>
      -- a bare universe (`within U`, no explicit `⊆`) is `∅ ⊆ U` — permitted for `within` only; any other
      -- keyword missing its `⊆` is a located error (not silently accepted as `∅ ⊆ …`).
      if kw == "within" then .ok { kw, perEdge, lhs := .empty, rhs := lhs, pos }
      else err pos s!"clause `{kw}` requires a `⊆`; only `within` may be written as a bare universe"

/-! ## Ghost block + program -/

def clauseKeywords : List String := ["update", "predict", "always", "check", "seed", "within"]

/-- Collect the ghost body up to the matching `}` (handles nesting), returning (body, rest). -/
partial def collectBody (depth : Nat) (acc : List Token) : List Token → Res (List Token × List Token)
  | t :: r =>
    if t.text == "}" then
      if depth == 0 then .ok (acc.reverse, r) else collectBody (depth - 1) (t :: acc) r
    else if t.text == "{" then collectBody (depth + 1) (t :: acc) r
    else collectBody depth (t :: acc) r
  | [] => err {} "unterminated ghost body — expected '}'"

/-- Split a ghost body into clauses on the keyword tokens, parsing each. -/
def parseClauses (body : List Token) : Res (List Clause) := do
  -- group runs [kw : … ] (the `:` right after a keyword is dropped)
  let mut clauses : List Clause := []
  let mut curKw := ""
  let mut curPos : Pos := {}
  let mut cur : List Token := []
  let flush (kw : String) (pos : Pos) (toks : List Token) (cs : List Clause) : Res (List Clause) := do
    if kw == "" then .ok cs
    else return cs ++ [← parseClauseBody kw pos toks]
  for t in body do
    if clauseKeywords.contains t.text then
      clauses ← flush curKw curPos cur clauses
      curKw := t.text; curPos := t.pos; cur := []
    else if curKw != "" then
      -- drop the immediate `:` and any `;` separators
      if t.text != ":" && t.text != ";" then cur := cur ++ [t]
  clauses ← flush curKw curPos cur clauses
  .ok clauses

/-- Parse a `GhostSpec`: `Direction Name var : Dom { clauses }`; returns block + rest.
    `Name` is the predicate (e.g. `Anticipated`), `var` the carried ghost (e.g. `πₐ`). -/
def parseGhost : List Token → Res (GhostBlock × List Token)
  | dir :: nm :: c :: colon :: dom :: rest0 => do
    if dir.text != "history" && dir.text != "prophecy" then
      err dir.pos s!"expected 'history' or 'prophecy', found '{dir.text}'"
    else if colon.text != ":" then err colon.pos s!"expected ':', found '{colon.text}'"
    else
      -- element-type annotation `[Elem]` right after the domain (`Assignments[Expr]`). REQUIRED: it is
      -- spliced into emitted identifiers (`BV<elem>`, `decF<elem>`), so an absent or empty annotation
      -- would emit unusable Lean rather than fail. Reject it here so the totality contract holds —
      -- malformed input is a located error, never a silent misclassify.
      let (elem, rest1) := match rest0 with
        | lb :: e :: rb :: r => if lb.text == "[" && rb.text == "]" then (e.text, r) else ("", rest0)
        | _                  => ("", rest0)
      if elem.isEmpty then
        err dom.pos s!"ghost '{c.text}': domain '{dom.text}' needs an element-type annotation, \
                       as in '{dom.text}[Expr]'"
      else
      match rest1 with
      | brace :: rest =>
        if brace.text != "{" then err brace.pos s!"expected an opening brace, found '{brace.text}'"
        else do
          let (body, rest') ← collectBody 0 [] rest
          let clauses ← parseClauses body
          .ok ({ dir := dir.text, name := nm.text, carried := c.text, dom := dom.text, elem := elem, clauses, pos := dir.pos }, rest')
      | [] => err dir.pos "expected an opening brace after the ghost header"
  | ts => err (hdPos ts) s!"malformed ghost header near '{hdText ts}'"

/-- Read a dotted module path `ident (. ident)*` (e.g. `Tac.Locals`), returning the joined string + rest. -/
partial def takeDottedPath : List Token → (String × List Token)
  | id :: dot :: rest =>
    if dot.text == "." then let (more, r) := takeDottedPath rest; (id.text ++ "." ++ more, r)
    else (id.text, dot :: rest)
  | [id] => (id.text, [])
  | []   => ("", [])

/-- Parse the body of an `analysis { … }` wrapper: a sequence of ghost blocks. A non-ghost token (the
    closing `}` has already been stripped by `collectBody`) is a located error — ghost blocks live *only*
    inside the wrapper. -/
partial def parseGhostList : List Token → Res (List GhostBlock)
  | []          => .ok []
  | ts@(t :: _) =>
    if t.text == "history" || t.text == "prophecy" then do
      let (g, rest') ← parseGhost ts
      let gs ← parseGhostList rest'
      .ok (g :: gs)
    else err t.pos s!"expected a ghost block (`history`/`prophecy`), found '{t.text}'"

/-- Parse a whole program: file-level `include <dotted.path>` directives (collected separately by
    `includesOf`) followed by one or more `analysis <id> { GhostSpec* }` blocks. A ghost block **must** be
    nested inside an `analysis { … }` wrapper — a bare top-level ghost is a located error. -/
partial def parseProgram : List Token → Res (List GhostBlock)
  | [] => .ok []
  | t :: rest =>
    if t.text == "include" then parseProgram (takeDottedPath rest).2
    else if t.text == "analysis" then
      match rest with
      | _nm :: brace :: inner =>
        if brace.text != "{" then err brace.pos s!"expected an opening brace after the analysis name, found '{brace.text}'"
        else do
          let (body, rest') ← collectBody 0 [] inner
          let gs   ← parseGhostList body
          let more ← parseProgram rest'
          .ok (gs ++ more)
      | _ => err (hdPos rest) "expected an analysis name and an opening brace after `analysis`"
    else if t.text == "history" || t.text == "prophecy" then
      err t.pos "a ghost block must be nested inside an `analysis <name> { … }` wrapper"
    else err t.pos s!"expected `analysis` or `include`, found '{t.text}'"

/-- Top-level entry: lex + parse a `.gsl` source into ghost blocks (or a located error). -/
def parseGslBlocks (src : String) : Res (List GhostBlock) := do
  parseProgram (← lex src)

/-- The analysis-level name from the `analysis <Name>` wrapper (`""` if the source has no wrapper). -/
def analysisNameOf (src : String) : String :=
  match lex src with
  | .ok toks =>
    match toks.dropWhile (fun t => t.text != "analysis") with
    | _ :: nm :: _ => nm.text
    | _            => ""
  | .error _ => ""

/-- The file-level `include <dotted.path>` directives, in order (the node-local source namespaces). -/
partial def includesOf (src : String) : List String :=
  match lex src with
  | .ok toks => go toks
  | .error _ => []
where
  go : List Token → List String
  | []        => []
  | t :: rest =>
    if t.text == "include" then let (p, r) := takeDottedPath rest; p :: go r
    else go rest

end GenGeneral
