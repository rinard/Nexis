<!-- Copyright (c) 2026 Martin Rinard -->
# Frozen EBNF — the full MTC surface

> **Status: FROZEN.** This is the grammar the `GenGeneral/` total parser targets. It is the §3 grammar
> of `GHOST-SPEC-LANGUAGE.md` **restricted to what the parser actually builds** (explicit node form) and
> **extended additively** with the `gather`/`image` atom forms and compound `∧`/`∨` guards. Malformed
> input is a **located error**, never a silent misclassify (the totality contract).
>
> **Matches `GenGeneral/Parser.lean`** (the two are the single source of truth for the surface):
> the file-level `include DottedPath` directive and the `[Elem]` element-type annotation are grammar,
> and two constraints are **hard errors** — a ghost block must be nested inside
> an `analysis { … }` wrapper (no bare top-level ghosts), and a `∀` binder must be exactly `n` (per-config)
> or `n → n'` (per-edge).
>
> This grammar is frozen: it is exactly the MTC atoms + the ghost frame, **not** a general expression language.

## Lexical

```ebnf
letter     ::= "a".."z" | "A".."Z" | "_"
digit      ::= "0".."9"
identifier ::= letter { letter | digit | "'" }   (* names; trailing "'" allowed: avail' *)
Node       ::= "n" | "n'"                          (* the two endpoints of an edge *)
Bnd        ::= "entry" | "final"                   (* boundary nodes — seed only *)
Elem       ::= "z" | "y" | identifier              (* element variables: z = output, y = ∃-bound *)
comment    ::= "--" { any } EOL                    (* to end of line *)
```

Keywords: `analysis include history prophecy within seed update predict always check when meets`.
Symbols punched out by the lexer as standalone tokens:
`{ } ( ) [ ] : . , ∀ → ∪ ∩ ∖ ⊆ ∈ ∅ ∧ ∨ ∃`.
`∨`/`∧` also accept the ASCII spellings `or`/`and`. `;` separates clauses on one line.

## Grammar

```ebnf
Program      ::= { Include } { Analysis }         (* ghost blocks live ONLY inside an Analysis *)
Include      ::= "include" DottedPath             (* file-level node-local source namespace *)
DottedPath   ::= identifier { "." identifier }    (* e.g. Tac.Locals · analyses.lcm.LcmDefs *)
Analysis     ::= "analysis" identifier "{" { GhostSpec } "}"

GhostSpec    ::= Direction identifier Ghost ":" Family [ "[" Elem "]" ] "{" { Clause } "}"
Direction    ::= "history" | "prophecy"
Ghost        ::= identifier                        (* carried variable; may be η/π/τ *)
Family       ::= identifier                        (* domain, e.g. Assignments / Variables *)
                                                   (* [Elem] = element-type annotation: Assignments[Expr] *)

Clause       ::= Propagation | Condition | Seed | Within

(* --- propagation: the diagonal step (var'-isolated, unguarded) --- *)
Propagation  ::= ("update" | "predict") ":" [ "∀" Edge "." ] Incl
Edge         ::= "n" "→" "n'"

(* --- condition: an unguarded clamp, or a when-guarded atom --- *)
Condition    ::= ("always" | "check") ":" ( Clamp | Guarded )
Clamp        ::= [ "∀" "n" "." ] Incl                               (* per-config floor/ceiling *)
Guarded      ::= [ "∀" Edge "." ] ( SetExpr "⊆" SelfRef "when" Guard     (* set-level  → gate  *)
                                  | Elem "∈" SelfRef "when" Guard )       (* per-element → image/gather *)

(* --- boundary & universe --- *)
Seed         ::= "seed" ":" Incl
Within       ::= "within" ( [ "∀" "n" "." ] SelfRef "⊆" SetExpr | SetExpr )

(* --- inclusions & set expressions (isolate the carried ghost: exactly one side is a SelfRef) --- *)
Incl         ::= SelfRef "⊆" SetExpr | SetExpr "⊆" SelfRef
SelfRef      ::= CarriedGhost [ "(" NodeArg ")" ]   (* the carried ghost, e.g. anti(n'), avail(entry) *)

(* `∩`/`∖` bind tighter than `∪`; all left-associative; parenthesize to override. *)
SetExpr      ::= SetInter { "∪" SetInter }
SetInter     ::= SetTerm { ("∩" | "∖") SetTerm }
SetTerm      ::= Ref | "∅" | "(" SetExpr ")"

Ref          ::= identifier [ Params ] [ "(" NodeArg ")" ]   (* avail(n) · earliest(anti,avail)(n,n') · liveSeed *)
Params       ::= "(" Ghost { "," Ghost } ")"                 (* foreign ghosts a placement family reads *)
NodeArg      ::= Node | Node "," Node | Elem | Bnd

(* --- guards (monotone in the incoming ghost). `∧` binds tighter than `∨`; both left-associative. --- *)
Guard        ::= GuardAnd { ("∨" | "or")  GuardAnd }
GuardAnd     ::= GuardAtom { ("∧" | "and") GuardAtom }
GuardAtom    ::= SetExpr "meets" Ref                 (* gate     : sng meets in *)
               | "∃" Elem "∈" Ref "." Rel            (* image    : ∃ y ∈ in. R(y,z) *)
               | SetExpr "⊆" Ref                     (* gather   : sub(z) ⊆ in *)
               | Elem "∈" Ref                         (* diagonal : z ∈ in *)
               | Elem "∈" SetExpr                    (* constant : z ∈ source(n) *)
               | "(" Guard ")"
Rel          ::= identifier [ "(" NodeArg ")" ] "(" Elem "," Elem ")"   (* flowsTo(n)(y,z) *)
```

## Atom lowering (Guard → `MTC`)

Each `GuardAtom` maps to exactly one `Transfer`/`MTC` constructor; `∧`→`inter`, `∨`→`union`. Compound
atoms are just composed terms — **no special case, no new template**.

| guard `G`               | atom                | `Transfer`     |
|-------------------------|---------------------|----------------|
| `z ∈ in`                | diagonal            | `var`          |
| `sng meets in`          | gate(`sng`→`res`)   | `gate sng res` |
| `∃ y ∈ in. R(y,z)`      | image(`U`,`R`)      | `image U R`    |
| `sub(z) ⊆ in`           | gather(`U`,`sub`)   | `gather U sub` |

The acid test `PrimeAdd` (shipped as `analyses/primeadd/PrimeAdd.gsl`) exercises a compound
`gather ∩ gate` guard: `below(z) ⊆ g(n) ∧ primes meets g(n)` lowers to
`inter (gather allNums below) (gate primes allNums)`, unioned with the carrier `var`.

## Well-formedness (checked by the parser/selector, `GHOST-SPEC-LANGUAGE.md` §3)

1. **Isolation.** One side of every `Incl` is a single `SelfRef` (never a compound `SetExpr`). A
   propagation whose isolated side is the carried ghost and whose other side is a bare *foreign* ghost
   with no self-occurrence (`tp(n) ⊆ postp(n')`) is a **confluence** (meet/join), not a fixpoint.
2. **The incoming.** In a `Guarded`/`GuardAtom`, the ref right of `meets`/`∈`/`∃…∈`/`⊆` is the incoming:
   `Ghost(n)` for `history`, `Ghost(n')` for `prophecy`.
3. **Monotonicity.** A guard is positive in the incoming — the incoming appears only under
   `meets`/`∈`/`∃…∈`/`⊆`, never negated / `∉` / left of `∖`.
4. **Clamp is per-config, unguarded** (`∀ n`); propagation and guarded conditions are per-edge (`∀ n→n'`).
5. **`gather` base case.** In `sub(z) ⊆ in`, elements with `sub(z)=∅` are vacuously included, so the
   atom's universe `U` excludes base elements (they come from the carrier's `update`/`predict`).
6. **Carrier.** A ghost persists iff it has an `update`/`predict`; `image`/`gather` ride on a carrier.

Direction is **written** (`history`/`prophecy`); the quadrant (fwd/bwd · must/may) is **inferred** by
the selector from (direction, ⊆-polarity of the bounding clause) — never a spec input.
</content>
