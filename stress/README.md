<!-- Copyright (c) 2026 Martin Rinard -->
# Stress corpus — spiky `.gsl` specifications

Bizarre / compound / deeply-nested / degenerate / deliberately-malformed specifications, seeded by
`PrimeAdd`, that push the `GenGeneral/` pipeline (parser → lower → select) to its edges — both what it must
**accept** and what it must **refuse**.

Run: **`lake exe gengen-stress`**. This is a **regression gate**, not a diagnostic: each spec has an
*expected* outcome (`lowers <quadrant…>` / `rejects`) and the runner **exits nonzero** on any deviation —
a parse break, a wrong quadrant, a lost or spurious rejection, or an unexpected lower. Sibling gate to
`gengen-check`. The expected outcomes live in `GenGeneralStress.lean` (`corpus`); update them there
deliberately when a generalization changes what a spec does.

## Outcomes

- **`lowers`** — lex+parses the frozen grammar, lowers to an `AnalysisIR`, and selects a consistent
  quadrant. **27 of 37.**
- **`rejects`** — the totality contract produces a **located error**, at lowering (`∩` in a gather-sub /
  gate singleton, a standalone `∅`, a missing `within`, an unguarded clamp under a forward guard) or
  selection (a cyclic or self-referential confluence). **9 of 37** (11, 16, 21–24, 32, 36, 37).
- **`parseFail`** — refused earlier still, in the lexer/parser, before any IR exists. **1 of 37** (35).

## The specs

| # | spec | what it stresses | outcome |
|---|---|---|---|
| 01 | `PrimeAdd` | pure carrier + compound `gather ∧ gate`, fwd·may | lowers |
| 02 | `TriGuard` | 3-way `∧` (gather ∧ gate ∧ gather) | lowers |
| 03 | `DisjImage` | `∨` mixing relational image with a gather; named seed | lowers |
| 04 | `NestedGuard` | parenthesized `(gather ∧ gate) ∨ (gather ∧ gate)` | lowers |
| 05 | `ConstReach` | copy-through **image** over a product domain (Var×Lit) | lowers |
| 06 | `MeetChain` | 4-long confluence dep-DAG (fixpoint → meet → join → meet) | lowers |
| 07 | `EdgeStorm` | edge placement reading **five** foreign ghosts | lowers |
| 08 | `DeepSet` | 4-deep nested set-expr, mixed `∪`/`∩`/`∖` + parens (non-diamond) | lowers |
| 09 | `WideConj` | `∧`/`∨` precedence: `a ∧ b ∨ c ∧ d ∧ e`, no parens | lowers |
| 10 | `DoubleAtom` | bwd·may carrier with **three** guarded atoms (gather+image+set-gate) + floor | lowers |
| 11 | `MutualConfluence` | **cyclic** confluence (`a ⊆ b'`, `b ⊆ a'`) — no topological order | **rejects** |
| 12 | `GatherDiff` | `∖` inside a gather sub (`needs(z) ∖ base(z) ⊆ g`) | lowers |
| 13 | `DiagGuard` | the diagonal atom `z ∈ in` (var) `∧` a gate | lowers |
| 14 | `TwoImages` | two `∃`-images OR'd, distinct ∃-vars | lowers |
| 15 | `QuadZoo` | **five quadrants** across two element types in one analysis | lowers |
| 16 | `SelfRefMeet` | degenerate confluence, foreign == the carried ghost | **rejects** |
| 17 | `DeepParenGuard` | 4-level nested guard `((A∧(B∨C))∧D)∨(E∧(F∨G))` | lowers |
| 18 | `BareWithin` | bare `within U` (no `∀ n.`/`⊆`) + bare `∅` seed | lowers |
| 19 | `BwdImage` | backward (prophecy) image reading the successor `bi(n')` | lowers |
| 20 | `HugeConj` | seven-way `∧` chain of gathers | lowers |
| 21 | `InterGatherSub` | `∩` in a gather-sub (not `Leaf`-shaped) | **rejects** |
| 22 | `EmptyTransfer` | `∅` as a standalone transfer term | **rejects** |
| 23 | `NoWithin` | a ghost with no `within` universe | **rejects** |
| 24 | `InterGate` | `∩` in a gate singleton (not `Leaf`-shaped) | **rejects** |
| 25 | `UnionGatherSub` | `∪` gather-sub (complements GatherDiff's `∖`) | lowers |
| 26 | `UnionGate` | `∪` gate singleton | lowers |
| 27 | `CarryImage` | compound guarded-base (`self ∪ gen`) + image (the taint shape) | lowers |
| 28 | `FwdSetGate` | **forward** set-level gate (`sinks ⊆ self' when trig meets in`) | lowers |
| 29 | `DoubleClamp` | **floor + ceiling** on one carrier ⇒ doubly-clamped bwd·must | lowers |
| 30 | `FwdClamp` | lone **forward ceiling** ⇒ `resFMC` (floor = `∅`) | lowers |
| 31 | `FwdFloor` | lone **forward floor** ⇒ `resFmC` (ceiling = universe) | lowers |
| 32 | `FwdGuardClamp` | forward **guard + unguarded clamp** — still a located error | **rejects** |
| 33 | `FwdMustFloor` | fwd·must + lone floor ⇒ `resFMC` (ceiling = universe) | lowers |
| 34 | `FwdMayCeil` | fwd·may + lone ceiling ⇒ `resFmC` (floor = `∅`) | lowers |
| 35 | `BareFamily` | a domain with no `[Elem]` annotation | **parseFail** |
| 36 | `SuccConst` | a const family at the successor, `gen(n')`, in the diamond | **rejects** |
| 37 | `EdgeConst` | a const family at the edge, `gen(n,n')`, on the general path | **rejects** |

Specs 01–20 are the original edge-probing set (every quadrant, atom, compound, confluence chain, edge
placement, deep/wide nesting, cyclic/self-referential rejection). Specs 21–24 pin the totality contract's
**located-error** paths; 25–28 pin the generalized combinators (compound gather-sub / gate singleton,
compound guarded-base, forward set-level gate); 29–34 pin the doubly-clamped floor/ceiling family
(floor + ceiling, lone forward floor/ceiling across must/may, and the still-rejected guarded-clamp
combination). 35 pins the ghost header (a domain with no element type is refused in the parser, not
lowered into unusable Lean); 36–37 pin the const-leaf read site — a non-ghost family inside a transfer is
read at the *current* node, so applying one to `n'` or to the edge cannot be honoured (only a parameterised
placement `f(…)(n')` carries a `readAt`) and must be a located error rather than a silent read-at-`n`.
Every construct these probe either lowers or is a deliberate located error — there are no
silent drops or undetected inconsistencies.
