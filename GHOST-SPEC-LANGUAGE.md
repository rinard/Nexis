<!-- Copyright (c) 2026 Martin Rinard -->
# Ghost-spec language — reference

A surface language for authoring ghost variables (prophecy/history) that the generator lowers to the
**Monotone Transfer Calculus** (`Solver/Spec.lean`) and its four verified quadrant solvers — the
dataflow mechanism that implements the ghost variables, hidden behind the spec.

The surface is realized by the `GenGeneral/` total parser and the `gen` generator (`lake exe gen`).
See the shipped specs in `analyses/*/*.gsl` for worked examples (both node forms) and
`docs/GENERAL-PIPELINE-EBNF.md` for the frozen grammar.

The settled surface is four keywords — `update`/`predict` (propagation) and `always`/`check`
(condition) — plus `seed`/`within`.

---

## 1. Principle: the language is over the *operational semantics*, not the program

Every clause is a relation over the **operational semantics** — the small-step transition relation
`Step P c c'` and the boundary configurations (`entry`, `Final`) — or a per-configuration invariant.
**Nothing in the language names the CFG.** The solver *derives* the graph computation (meet/join over
realizable neighbors) from the operational constraint plus extremality.

This is why a program-level construct like `meet τ = ⊓ X over nodes` is **wrong**: it prescribes the
computation instead of stating the constraint. meet/join are not primitives — they are the extremal
solution of an ordinary per-step inclusion (section 6).

A ghost is a **history** variable (records the past → accumulates *with* execution) or a **prophecy**
variable (commits to the future → propagates *against* execution). That single semantic word is the
only "direction" annotation; there is no `forward`/`backward` and no `may`/`must` keyword — both fall
out of the shape of the inclusions (section 4).

---

## 2. The MTC term (the value the solver runs)

The **incoming** ghost value (`MTC.var`, the transfer's single input) is written `in` in the surface —
the predecessor's value for `history`, the successor's for `prophecy` (section 9). A transfer is a
*positive* (negation-free ⇒ monotone in the incoming) set-function:

```
in                             var        the incoming ghost value
family                         const      an edge-local set (gen/kill/…), read at a config
a ∪ b                          union
a ∩ b                          inter
a ∖ family                     diffc      subtrahend a constant only (⇒ the incoming never negated)
gate(sng → res)                gate       if in meets sng then res else ∅   (faint-liveness)
image(U, R)                    image      { z ∈ U : ∃ y ∈ in, R y z }        (OR-gather)
gather(U, sub)                 gather     { z ∈ U : sub z ⊆ in }             (AND-gather)
```

With `∪`/`∩` the gather atoms reach **every monotone transfer over a finite universe**. Direction and
extremality are **not** part of the term — the same term serves all four quadrants (section 5, the
diamond). In the clause surface these atoms are written as guarded `always`/`check` conditions
(section 9); this table is the term they lower to.

---

## 3. Grammar (explicit clause surface)

The surface is the four-keyword clause language (`update`/`predict`/`always`/`check` + `seed`/`within`).
This section gives its full EBNF in the **explicit** node form (`∀ n→n'` on per-edge clauses, `∀ n` on
per-config clamps); the **inferred** form (section 8) is the same grammar with the quantifiers and node
arguments erased.

### Lexical

```ebnf
identifier ::= letter { letter | digit | "'" }    (* analysis / ghost / family / relation names; trailing "'" allowed: avail' *)
Node       ::= "n" | "n'"                          (* the two endpoints of an edge *)
Bnd        ::= "entry" | "final"                   (* boundary nodes — seed only *)
Elem       ::= "z" | "y" | identifier              (* element variables: z = output, y = ∃-bound *)
comment    ::= "--" { any } EOL
(* keywords: include history prophecy analysis within seed
             update predict always check when meets
   set ops : ∪ ∩ ∖ ⊆ ∈ ∅   logic: ∨ ∧ (= or/and) ∃   edge: →   quantifier: ∀ *)
```

### Grammar

```ebnf
Program      ::= { Include } { Analysis }            (* ghost blocks live ONLY inside an Analysis *)
Include      ::= "include" DottedPath                (* file-level node-local source namespace *)
DottedPath   ::= identifier { "." identifier }       (* e.g. analyses.lcm.LcmDefs *)
Analysis     ::= "analysis" identifier "{" { GhostSpec } "}"

GhostSpec    ::= Direction identifier Ghost ":" Family "[" ElemTy "]" "{" { Clause } "}"
                                                   (* the [ElemTy] annotation is REQUIRED *)
Direction    ::= "history" | "prophecy"
Ghost        ::= identifier                          (* the carried variable's name; may be η/π/τ (§ Notes) *)
Family       ::= identifier

Clause       ::= Propagation | Condition | Seed | Within

(* --- transfer: propagation (diagonal / meet / join) --- *)
Propagation  ::= ("update" | "predict") ":" "∀" Edge "." Incl
Edge         ::= "n" "→" "n'"

(* --- condition: clamp (unguarded) or guarded atom --- *)
Condition    ::= ("always" | "check") ":" ( Clamp | Guarded )
Clamp        ::= "∀" "n" "." ( SelfRef "⊆" SetExpr         (* ceiling → hi *)
                             | SetExpr "⊆" SelfRef )        (* floor   → lo *)
Guarded      ::= "∀" Edge "." ( SetExpr "⊆" SelfRef "when" Guard   (* set-level (gate)      *)
                              | Elem "∈" SelfRef "when" Guard )     (* per-element (img/gath)*)

(* --- boundary & universe --- *)
Seed         ::= "seed" ":" Incl
Within       ::= "within" SetExpr

(* --- inclusions & set expressions --- *)
(* Incl ISOLATES the carried ghost: exactly one side is a single SelfRef, never a compound SetExpr.   *)
Incl         ::= SelfRef "⊆" SetExpr | SetExpr "⊆" SelfRef
SelfRef      ::= CarriedGhost "(" NodeArg ")"               (* the carried ghost at a node — one bare ref, *)
                                                           (* e.g. π(n'), η(n'), τ(n), avail(entry).      *)
(* Precedence (unambiguous): `∩` and `∖` bind tighter than `∪`; all three LEFT-associative.  Written as
   three layers so the grammar is directly a recursive descent.  Parenthesize to override. *)
SetExpr      ::= SetExpr "∪" SetInter | SetInter
SetInter     ::= SetInter ("∩" | "∖") SetTerm | SetTerm
SetTerm      ::= Ref | "∅" | "(" SetExpr ")"

(* ONE syntactic form for every reference; its KIND is resolved by a symbol table, not the parser:
     - the carried ghost  → the incoming value (`MTC.var`) unprimed / the isolated Self primed;
     - a foreign ghost    → its solved value (`solve_<X>` / `decode …`);
     - anything else      → a family / placement leaf (`MTC.const (fun e => <ref> P e…)`).
   The table is: {carried ghost} ∪ {the analysis's other ghost names} are ghosts; all else are families. *)
Ref          ::= identifier [ Params ] [ "(" NodeArg ")" ]  (* avail(n) · genExprs(n) · earliest(anti,avail)(n,n') · operands(z) · liveSeed *)
Params       ::= "(" Ghost { "," Ghost } ")"                (* ghosts a derived (placement) family is built from *)
NodeArg      ::= "n" | "n'" | "n" "," "n'" | Elem | Bnd

(* --- guards (monotone in the incoming ghost).  `∧` binds tighter than `∨`; both LEFT-associative. --- *)
Guard        ::= Guard "∨" GuardAnd | GuardAnd
GuardAnd     ::= GuardAnd "∧" GuardAtom | GuardAtom
GuardAtom    ::= SetExpr "meets" Ref                        (* gate     : sng(n) meets in *)
               | "∃" Elem "∈" Ref "." Rel                   (* image    : ∃ y ∈ in. R(y,z) *)
               | SetExpr "⊆" Ref                            (* gather   : sub(z) ⊆ in *)
               | Elem "∈" Ref                              (* diagonal : z ∈ in *)
               | Elem "∈" SetExpr                           (* constant : z ∈ source(n) *)
               | "(" Guard ")"
Rel          ::= identifier [ "(" NodeArg ")" ] "(" Elem "," Elem ")"   (* flowsTo(n)(y,z) *)
```

### Well-formedness (side conditions the generator checks)

1. **Propagation isolates the carried ghost.** One side of `Incl` is a single `SelfRef` (the carried
   ghost at one node — `π(n')`/`η(n')`), never a compound `SetExpr`. For a transfer the isolated side is
   the successor `π(n')`/`η(n')` and the `SetExpr` mentions the incoming self `π(n)`/`η(n)`; `update` is
   `history`, `predict` is `prophecy`. If the isolated `SelfRef` is the carried ghost and the other side
   is a *foreign* ghost with no self-occurrence (`τ(n) ⊆ anti(n')`), it is a **meet/join** (section 6).
   The same single-`SelfRef` isolation holds for `Clamp`, `Guarded`, and `Seed`.
2. **The incoming.** In every `Guarded`/`GuardAtom`, the `GhostRef` right of `meets`/`∈`/`∃…∈`/`⊆` is the
   *incoming*: `Ghost(n)` for `history`, `Ghost(n')` for `prophecy`. The `Guarded` `Self` side is the
   dual (`Ghost(n')` history / `Ghost(n)` prophecy).
3. **Monotonicity.** A `Guard` is positive in the incoming — the incoming appears only under
   `meets`/`∈`/`∃…∈`/`⊆`, never negated, `∉`, disjoint, or left of `∖`. This is what bounds the surface
   to exactly the monotone transfers.
4. **Clamp is per-config, unguarded.** `Clamp` quantifies `∀ n`, isolates `Ghost(n)`, mentions no
   incoming; `Propagation` and `Guarded` quantify `∀ n→n'`.
5. **`gather` base case.** In `sub(z) ⊆ in`, the atom's universe excludes base elements (`sub(z) = ∅`,
   which satisfies `∅ ⊆ in` vacuously); those come from the carrier's `gen` (section 9).
6. **Carrier.** A ghost persists iff it has an `update`/`predict`; `image`/`gather` conditions ride on a
   carrier (section 9). Extremality/direction are *read* (not written): `history`/`prophecy` gives
   direction; the `Clamp` ⊆-side (ceiling ⇒ must, floor ⇒ may) plus `seed` gives extremality (section 4).

### Notes

- **Inferred form**: delete every `"∀" Edge "."` / `"∀" "n" "."` and erase `NodeArg` (ghosts as
  `avail`/`avail'`, node families bare, edge families bare). Same productions otherwise.
- `∨`/`∧` accept `or`/`and`; `;` may separate clauses on one line.
- **`η`/`π`/`τ` variable naming (optional convention).** Name the *carried variable* by its kind: `η`
  for a history variable, `π` for a prophecy variable, `τ` for a confluence/transfer variable (meet/join,
  section 6, e.g. `tauP`/`usedOut`). The analysis name carries identity; the letter carries kind.
  This is pure naming — `Ghost` is any identifier, so nothing in the grammar or generator changes. It also
  removes the need for a separate incoming binder: with the ghost named `η`, the history incoming is `η`
  (unprimed = predecessor) and the output `η'`; with `π`, the prophecy incoming is `π'` (primed =
  successor) and the output `π`. Caveat: multi-ghost analyses (LCM/PDCE) need subscripts (`η_avail`,
  `π_anti`, `τ_A`), which make foreign references cryptic — so prefer descriptive names there and reserve
  `η`/`π`/`τ` for single-ghost / pedagogical specs.

  ```
  history Available η : Exprs { update : η' ⊆ gen ∪ (η ∩ transp) ;  seed : η ⊆ ∅ ;  within allExprs }
  prophecy Live    π : Vars  { predict : π' ⊆ π ∪ def ;  check : rhs ⊆ π when def meets π' ;
                                        check : condVars ⊆ π ;  seed : liveSeed ⊆ π ;  within allVars }
  ```
- Examples: the shipped specs in `analyses/*/*.gsl` (e.g. `analyses/lcm/Lcm.gsl`, `analyses/pdce/Pdce.gsl`).

---

## 4. Reading (static semantics — what the generator infers)

1. **Direction** = `Dir` (`history`/`prophecy`). It fixes what `in` (incoming) and `Self` (constrained)
   mean across a transition; `history` accumulates with `⟶`, `prophecy` anticipates against it. Foreign
   ghosts and `in` are read on the incoming side, `Self` on the constrained side.
2. **Extremality** = which side of `⊆` `Self` sits on: `Self ⊆ …` ⇒ **must** (greatest); `… ⊆ Self`
   ⇒ **may** (least). The same rule holds in the propagation, condition, and `seed` clauses; they must
   agree.
3. **Fixpoint vs confluence** = whether the propagation `SetExpr` mentions `in`. Mentions `in` → a
   transfer (self-fixpoint). Ignores `in`, references a foreign ghost → **meet/join** (section 6) — the
   extremal solution *is* the confluence; no separate construct. (Back-end may settle it in one pass;
   invisible in the language.)
4. **Monotonicity is grammatical**: `in` can never be a `∖`-subtrahend (that slot accepts `Family`
   only) and there is no complement, so every `SetExpr` is monotone in `in` by construction.
5. **`within U`** is the operational `bound` (Self ⊆ universe at every reachable config); every leaf
   and boundary set must be provably `⊆ U` — the `Wf` / `_sub` obligation.
6. `(Dir, extremality)` selects the quadrant → `solveMTC{,B,BM,MF}Fun` + `resMTC*_correct` (valid ∧
   extremal, for free). Every ghost must resolve to exactly one quadrant, else fail-fast.

---

## 5. The four canonical analyses

In the clause surface (inferred node form):

```
history  Available avail : Exprs {         -- history · must
  update : avail' ⊆ gen ∪ (avail ∩ transp)
  seed   : avail ⊆ ∅ ;  within allExprs }

history  Reaching  reach : Defs {           -- history · may
  update : gen ∪ (reach ∩ transp) ⊆ reach'
  seed   : ∅ ⊆ reach ;  within allDefs }

prophecy VeryBusy  busy : Exprs {           -- prophecy · must
  predict : busy ∖ gen ⊆ busy'
  check   : busy ⊆ gen ∪ transp                     -- ceiling (hi)
  seed    : busy ⊆ ∅ ;  within allExprs }

prophecy Live      live : Vars {            -- prophecy · may
  predict : live' ⊆ live ∪ def                       -- propagation (kill def)
  check   : rhs ⊆ live  when  def meets live'        -- guarded condition ⇒ gate atom
  check   : condVars ⊆ live                          -- floor (lo)
  seed    : liveSeed ⊆ live ;  within allVars }
```

**The diamond.** Available/VeryBusy share the term `gen ∪ (in ∩ transp)`; Reaching/Live share
`gen ∪ (in ∖ kill)`. The *rows* differ only by `history`/`prophecy`; the *columns* only by which side
of `⊆` `Self` sits on / the direction of the boundary. Nothing distinguishing the four lives in the
term — which is why the quadrant cannot be inferred from the term, and why the direction keyword plus
the boundary direction suffice.

---

## 6. meet / join are ordinary per-step inclusions (no primitive)

A transfer variable relates its ghost to an already-solved *foreign* ghost, per transition — a
`update`/`predict` whose isolated side is the foreign ghost and which never reads the incoming:

```
prophecy TauP    tp      : Exprs { predict : tp ⊆ postp'      within allExprs }
prophecy UsedOut usedOut : Exprs { predict : used' ⊆ usedOut   within allExprs }
```

`TauP`'s clause reads the foreign `postp'` and never touches the incoming, so `tp ⊆ postp'` over every
transition — the greatest such `tp` is the **meet** of `postp` over successors. `UsedOut` has its ghost
on the large side ⇒ least ⇒ **join**. No `⊓`, no `over nodes`: the graph confluence is the extremal
solution, derived by the solver, never named. (Back-end note: a foreign-RHS clause is independent of its
own ghost, so it settles in one pass — the solver may use `resMeet`/`resJoin` instead of the worklist.
That is an optimization under the hood, not a language construct.)

---

## 7. The general form — four independent axes

A monotone ghost variable over a finite powerset `2^U` is exactly a point in **four orthogonal
axes**, each chosen freely:

1. **Direction** — `history` (forward) / `prophecy` (backward). Fixes which neighbour `in` is.
2. **Transfer** — a term `t ∈ MTC` (any monotone `2^U → 2^U`; complete via `gather`+`∪`). The per-step
   relation `in ↦ t`.
3. **Extremality** — `must` (greatest / meet-confluence) / `may` (least / join-confluence). *Which*
   extremal solution.
4. **Bounds** — a set of per-config or per-step inclusions clamping the solution: floors `lo ⊆ Self`,
   ceilings `Self ⊆ hi`. The seed is one of these.

### The symmetric rule

- **Extremality = the `⊆`-direction of the transfer**, not the bound: `Self ⊑ t(in)` ⇒ **must** (the
  ghost is pinned above by its own transfer — greatest); `t(in) ⊑ Self` ⇒ **may** (built up from below —
  least).
- **Bounds (`always`/`check`) are unrestricted**: floor *and/or* ceiling, per-config *and/or* per-step,
  any number, localised by their families (a bound "only at `ifz` nodes" or "only at `entry`" is just a
  family that is empty elsewhere — no scoping construct needed). The solution is the extremal (per the
  transfer's direction) point of the region the bounds cut out.
- **`seed`** is the boundary-localised bound — sugar.

The solution lives in an interval `[lo, hi]`, and any analysis may carry both a floor and a ceiling. A
seed is a bound at the boundary config: `sd ⊆ Self@entry` is a floor localised to `entry` — a
`check`/`always` whose family is `∅`/`⊤` except at the boundary.

### Symmetry group

The design is invariant under the two flips that generate the space:

- **direction flip** (history ↔ prophecy): swap `σ ↔ σ'`, `update ↔ predict`, `always ↔ check`;
- **extremality flip** (must ↔ may): swap `⊆ ↔ ⊇` in the transfer, meet ↔ join at confluence, floor ↔
  ceiling at the seed.

`Available ↔ Reaching` and `VeryBusy ↔ Live` are exactly the extremality flip; the four quadrants are
one schema under the flip group.

### Completeness

MTC is complete for monotone `2^U → 2^U` (`gather`+`∪` = monotone DNF; `image`+`∩` = CNF), and both
directions, both extremalities, and arbitrary bounds are available — so every point of
`{direction} × {monotone transfer} × {extremality} × {bounds}` is expressible. That is exactly the
monotone / finite-powerset dataflow design space, with nothing analysis-specific baked in.

### The one subtlety

A ghost's transfer is the **conjunction of all its per-step inclusions**, combined into a single term
(`∪` for may, `∩` for must) *before* its direction is read. So `Live`'s `predict` (the `∖ def` fragment)
and its per-step `check` (the `gate` fragment) are two fragments of one transfer, and extremality is a
property of the *assembled* term. A per-**config** `check` is a genuine bound (a clamp); a per-**step**
`check` is a transfer fragment. That quantifier is the only thing the reader/generator must inspect to
know whether a `check` shapes the term or clamps the solution.

---

## 8. Node notation — explicit `∀ n→n'` vs inferred (two equivalent surfaces)

Where each leaf is read can be written two ways; pick per taste. They denote the same clause.

**Inferred (concise).** No node names. The incoming ghost value is `in`; a leaf's read-site is
its **arity** — a node family `f : Node → Set` is read at the step's node, an edge family
`g : Node → Node → Set` at the step's edge. **No `@` markers.** A node family that must be read at the
far endpoint is folded into an edge family (`usedKill(i,j) = latestNode(j) ∪ latestEdge(i,j)`), which
is exactly the shape of the underlying MTC leaf (`fun e => latN e.2 ∪ latE e.1 e.2`).

```
update : postp ⊆ earliest(anti,avail) ∪ (in ∖ ue)
```

**Explicit (verbose).** Quantify the transition `∀ n → n'` and apply every ghost/family to explicit
nodes. The incoming ghost is `ghost(sourcenode)`, the constrained (outgoing) is `ghost(targetnode)`;
families carry `(n)` or `(n,n')`. No `in`, no arity-inference, **no `@`** — every read shows its node.

```
update : ∀ n→n'.  postp(n') ⊆ earliest(anti,avail)(n,n') ∪ (postp(n) ∖ ue(n))
```

Same clause; explicit spells out what inferred derives. **Explicit** is the operational form (= the Lean
spec form with `n`/`n'`), makes direction derivable (which node is constrained), and needs no
special notation — at the cost of verbosity and of the *diamond* (with explicit nodes `Available` and
`VeryBusy` no longer read identically). **Inferred** is concise and keeps the diamond (the term is
direction-neutral, reused across quadrants). Neither needs `@`.

---

## 9. The complete symmetric vocabulary — `update` / `predict` / `always` / `check`

The surface has exactly four keywords: the 2×2 of **direction × role**.

|            | **propagation** (the ghost's step) | **condition** (a bound on the ghost) |
|------------|------------------------------------|--------------------------------------|
| **history**  | `update`                           | `always`                             |
| **prophecy** | `predict`                          | `check`                              |

plus `seed` (boundary condition) and `within` (universe). Nothing else.

- **propagation** (`update`/`predict`) — the value the ghost *carries along an edge*: `var'`-isolated,
  unguarded — the **diagonal** (gen/kill). `update` moves it forward (history); `predict` projects it
  backward (prophecy). This is the only role that predicts/updates a value.
- **condition** (`always`/`check`) — a membership the ghost must satisfy: `res ⊆ Self` / `Self ⊆ res`.
  **Unguarded** ⇒ a *static* clamp holding at every config → `lo`/`hi`. **`when`-guarded** ⇒ a condition
  *contingent on the incoming*, holding per edge → a gate/image/gather **atom** (a transfer summand).

`when` is a **condition-keyword modifier only**; `update`/`predict` never carry it. The split is by
concept and it reads correctly: a guarded `res ⊆ Self when G` is a *condition* ("`Self` contains `res`
whenever `G`") — which is what gate/image/gather are — **not** a propagation. So **`Live`'s gate is a
guarded `check`**, not a `predict`: it does not predict a value forward, it *conditions* `live(n)` on the
downstream `live(n')`.

The disambiguation is structural, no overlap:

- `update`/`predict` — the diagonal step (`var'`-isolated, unguarded);
- `always`/`check` **unguarded** — a static clamp (`lo`/`hi`);
- `always`/`check` **`when`-guarded** — a per-edge condition = gate/image/gather atom.

Both the diagonal and the guarded atoms are summands of the emitted MTC term; the keyword split reflects
the *reading* (a value propagated vs a condition imposed), not a partition of the term.

**A ghost has an `update`/`predict` iff it carries state.** A persisting ghost (taint, a reachability
closure, an available-expressions carrier) needs a propagation clause — `update : source ∪ taint ⊆
taint'` — with any guarded condition (`image`/`gather`) riding on top; a guarded condition *alone* does
not persist, so a value tainted at `n` would drop out at `n'`. In practice `image`/`gather` almost always
enrich a carrier this way; a genuinely carrier-free ghost (re-derived each step purely from its
conditions) is well-formed but unusual.

One subtlety specific to `gather`: `gather(U, sub)` includes every `z` with `sub(z) = ∅` *unconditionally*
(`∅ ⊆ in` always holds), so its universe `U` must **exclude base elements** — they come from the
carrier's `gen`, not the vacuous gather. E.g. structural availability applies `gather` over *compound*
expressions and supplies atoms via the `update` carrier (`avail' ⊆ localGen ∪ (avail ∩ transp)`). `image`
has no such corner: `∃ y ∈ ∅` is false, so an empty incoming yields the empty set.

### Guard shapes = the leaf atoms

`G` must be **monotone in `in`** (the incoming ghost value). The monotone shapes are exactly the four
leaf kinds:

| guard `G` | atom | keyword · form |
|---|---|---|
| `z ∈ in` | diagonal | `update`/`predict`, set-level (`var' ⊆ … ∪ (var ∩ keep)`) |
| `sng meets in` | `gate(sng → res)` | guarded `always`/`check`, set-level (`res ⊆ Self when sng meets in`) |
| `∃ y ∈ in. R(y,z)` | `image(U, R)` | guarded `always`/`check`, per-element (`z ∈ Self' when ∃ y ∈ in. R(y,z)`) |
| `sub(z) ⊆ in` | `gather(U, sub)` | guarded `always`/`check`, per-element (`z ∈ Self' when sub(z) ⊆ in`) |

The diagonal (`z ∈ in`) is written as the `update`/`predict` step; image/gather (per-element) are the
compact home of their guarded conditions. `in` is the incoming ghost — the predecessor for history, the
successor for prophecy — written as the unprimed ghost in the clause surface (`var`), or as the primed
ghost when the incoming is the successor (`var'`, prophecy). Meet/join = a propagation clause with a
single **foreign** occurrence and no `in`.

### Completeness — every monotone transfer is a clause form

**Claim.** The guarded `always`/`check` conditions express *every* monotone `f : 2^U → 2^U`.

**Proof.** Each `z ∈ f(in)` is governed by a monotone boolean `P_z(in)`, and every monotone boolean is a
DNF of positive clauses. The guarded condition `z ∈ Self' when (sng₁ meets in) and … and (sngₖ meets in)`
contributes one conjunctive term for `z`; unioning conditions (they combine as lower bounds) assembles
`P_z`. With `sng` a singleton, `sng meets in` is the literal `y ∈ in`; `and` gives `∧`; multiple
conditions give `∨` — a complete generating set for monotone boolean functions. Hence every monotone
`f`. ∎

Two requirements make the surface complete:

1. the `when` guard admits **conjunction** (`and`) — needed for AND-guards (`gather`);
2. **per-element** guards (`z ∈ Self' when …`) are allowed — the compact home of `image`/`gather`.

The `update`/`predict` propagation is then compact sugar for the diagonal condition (`z ∈ Self' when
z ∈ in`). The **unguarded** `always`/`check` clamps, `seed`, and the `history`/`prophecy` direction are
**orthogonal** — they fix the per-node boundary and the quadrant, not the transfer's shape. So the full
surface is complete for the whole MTC: the four quadrants over every monotone transfer. Guards are
positive in `in` (`∈` / `∃…∈` / `⊆`, never `∉` / disjoint), so exactly the monotone functions are
expressible — precisely MTC's domain, and precisely what dataflow admits.

### Symmetry

`update ↔ predict` and `always ↔ check` are dual under direction reversal (swap predecessor ⇄ successor,
i.e. the unprimed ⇄ primed incoming). Within each direction, `propagation ↔ condition` are the ghost's
own value versus every condition imposed on it, and `when` is the modifier that turns a *static*
condition (a clamp) into a *per-edge* one (an atom). The gen/kill 2×2 is the propagation (diagonal)
instance of the square; the gate/image/gather analyses are its guarded-condition instances. `always` is
the history dual of `check`: rarely instantiated for forward analyses (a forward ghost is pinned by
`seed` + diagonal; the `lo`/`hi` clamps are a backward/prophecy phenomenon here), but present so the
square is closed.

### `lo`/`hi`

The unguarded `always`/`check` clauses lower to the solver's per-node boundary clamps:

- **`lo`** — a per-node *floor*: `res(n) ⊆ result(n)` (from `res ⊆ Self`); e.g. `Live`'s `condVars ⊆ live`.
- **`hi`** — a per-node *ceiling*: `result(n) ⊆ res(n)` (from `Self ⊆ res`); e.g. `VeryBusy`'s
  `busy ⊆ genExprs ∪ transpExprs`.

The solver iterates the transfer term and clamps each node's value into `[lo(n), hi(n)]`. Extremality
is read from which clamp is present (ceiling ⇒ must, floor ⇒ may) together with the seed direction.

---

## 10. Design assessment — clean, symmetric, general, complete

A verdict on each, with the caveats stated honestly.

### Clean — yes, with two documented sharp edges

Four keywords (`update`/`predict`/`always`/`check`), one modifier (`when`), two scaffolding keywords
(`seed`/`within`). The disambiguation is *structural*, not conventional: `when` (a guard on the incoming)
partitions every clause into propagation vs static-clamp vs per-edge-condition with no overlap, so the
generator never needs a heuristic. Two honest wrinkles:

- The transfer term's summands are **split across two keywords** — the diagonal under `update`/`predict`,
  the gate/image/gather atoms under guarded `always`/`check`. This is a *reading* split (a propagated
  value vs a condition imposed), not a partition the semantics forces; both are summands of one MTC term.
- Two **semantic gotchas** that are not expressiveness gaps but must be known: `gather`'s empty-base
  vacuity (its universe must exclude base elements) and the carrier requirement (`image`/`gather` persist
  only atop an `update`/`predict`). Both are documented in section 9; neither is visible in the keyword count.

### Symmetric — yes, by construction

The vocabulary is exactly the 2×2 of **direction × role**:

|            | propagation | condition |
|------------|-------------|-----------|
| history    | `update`    | `always`  |
| prophecy   | `predict`   | `check`   |

`update ↔ predict` and `always ↔ check` are duals under direction reversal (predecessor ⇄ successor,
unprimed ⇄ primed incoming). Within a direction, propagation ↔ condition, with `when` the modifier that
turns a static condition (clamp) into a per-edge one (atom). One cell is empirically underused: `always`
(the history clamp) rarely fires, because a forward ghost is pinned by `seed` + diagonal and the `lo`/`hi`
clamps are a backward/prophecy phenomenon here — but it is present so the square closes, and it is
well-defined when a forward analysis does need its own bound.

### General — yes, within its intended domain

The surface expresses **exactly the monotone transfers over a finite powerset** (the MTC), across all
four quadrants (direction × extremality) plus the meet/join transfer variables. Two scope boundaries,
both deliberate:

- **Monotone only.** Guards are positive in the incoming, so non-monotone transfers are inexpressible —
  which is correct: they are not sound dataflow. The restriction *is* the design.
- **Powerset (bitvector) domains only.** No general lattices (constant-propagation's flat lattice,
  interval domains, …). The MTC is a bitvector calculus; this surface is exactly as general as that, no
  more. Extending to non-powerset lattices would be a different calculus, not a new clause.

### Complete — yes, proven (section 9)

Guarded `always`/`check` express **every** monotone `f : 2^U → 2^U`: each output element's monotone
boolean predicate is a positive DNF, and `z ∈ Self' when (sng₁ meets in) and … and (sngₖ meets in)`
plus union-across-conditions assembles it — literals via singleton `meets`, `∧` via `and`, `∨` via
multiple conditions is a complete basis for monotone booleans. Requires only (1) conjunctive `when`
guards and (2) per-element guards. `update`/`predict` is then compact sugar for the diagonal condition;
`always`/`check` clamps, `seed`, and direction are orthogonal (boundary + quadrant). So the surface is
complete for the whole MTC — nothing monotone over the powerset is out of reach.

**Isolation (single `SelfRef`, section 3) preserves completeness.** Requiring the carried ghost alone on
one side of every inclusion is not a restriction on reach: a transfer *is* a function `Self(n') = f(in)`,
so `Self` is inherently isolated on the output side, and the full monotone `f` is assembled from *many*
isolated clauses (the diagonal `update`/`predict` plus any number of guarded `always`/`check` atoms),
not from one compound inclusion. The DNF proof above is stated over exactly these isolated per-element
clauses — completeness holds *because of* the isolated form, not in spite of it. What isolation excludes
(`Self` compounded or on both sides, e.g. `Self(n') ∩ X ⊆ Y`) is precisely the non-functional relational
constraints, which are not monotone dataflow transfers and lie outside the design space.

**Verdict.** Clean, symmetric, general, and complete *for the monotone-powerset design space* — which is
exactly the MTC's domain and exactly what the four verified quadrant solvers cover. The residual rough
edges (`gather` base case, carrier requirement, summands split across two keywords) are documentation
concerns, not gaps in coverage or symmetry.

---

## 11. Lowering summary

| Dir · extremality | quadrant | solver | boundary |
|---|---|---|---|
| history · must | fwd·must | `resMTC_correct` | seed @entry (upper), ceiling = universe |
| history · may | fwd·may | `resMTCMF_correct` | seed @entry (lower) |
| prophecy · must | bwd·must | `resMTCBM_correct` | seed @halt (upper) + `always` ceiling |
| prophecy · may | bwd·may | `resMTCB_correct` | seed @halt (lower) + `always` floor |
| (meet — foreign RHS, Self small) | — | `resMeet_correct` | — |
| (join — foreign RHS, Self large) | — | `resJoin_correct` | — |

The generator's job: parse `Dir` + the `Incl` directions → `(quadrant, term, boundary)`; emit
`def xT : MTC α`, `def solve_x := solveMTC<Q>Fun P (list U) xT <boundary>`,
`theorem x_correct := resMTC<Q>_correct …` (+ the `Wf`/`_sub` proof); optionally the `_iff_flow`
bridge when a clause form is also supplied.
