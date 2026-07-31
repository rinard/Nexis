-- Copyright (c) 2026 Martin Rinard
import Solver.Spec
import Solver.Impl.Term

/-!
# `Solver.Quadrant` — the four generic quadrant solvers (a MECHANISM, not the seam)

**The substitution boundary is `Seam/`, not this file.** Every analysis — `lcm` included — exports the
same set-level triple in `Seam/<a>/ValidExtremal.lean` (`<c>Sol`, `<c>Sol_valid` against its clause
predicate over `Step`, and `<c>_greatest`/`<c>_least`), and that triple is what everything above
consumes. Substitute there.

This file is a *reusable way to implement* that triple: for any analysis whose transfer is an `MTC` term,
these four solutions + four contracts discharge it outright. That is how 19 of the 21 analyses get theirs
for free, and why a new `.gsl` spec needs no new stubs — every analysis lands in one of four quadrants.
But an analysis may satisfy its interface by **any** means (`lcm`/`pdce` do; see below).

**This file is the only importer of `Solver.Impl.*` outside the bundles.** Enforced by
`script/check-solver-seam.sh`.

## The contract: 4 solutions + 4 proofs

For each quadrant there is one solution function and one theorem, universally quantified over an arbitrary
term `t`, universe `univ`, and seed `sd` — so they cover **every analysis, present and future**:

| quadrant        | solution   | contract            | extremal |
|-----------------|------------|---------------------|----------|
| forward · must  | `resMTC`   | `resMTC_correct`    | greatest |
| forward · may   | `resMTCMF` | `resMTCMF_correct`  | least    |
| backward · must | `resMTCBM` | `resMTCBM_correct`  | greatest |
| backward · may  | `resMTCB`  | `resMTCB_correct`   | least    |

Each `_correct` is exactly *valid ∧ extremal*, e.g. for the forward-must quadrant:

```
resMTC_correct : MTCSpec P univ t sd (resMTC P univ t sd)                                   -- valid
               ∧ ∀ h, MTCSpec P univ t sd h → ∀ n, ∀ x ∈ h n, x ∈ resMTC P univ t sd n      -- extremal
```

`MTCSpec*` and the `MTC` term language live in `Solver.Spec` — they are *vocabulary* (what a valid
solution IS), not mechanism, so a replacement solver is written against them unchanged.

## Substituting a solver

Replace `Solver/Impl/` and re-provide the 8 symbols below. Nothing else in the repository changes: the
generator emits every analysis against exactly these, so **new analysis specs need no new stubs** — every
analysis lands in one of the four quadrants.

To stub (e.g. to vendor the compiler without a solver): give each `resMTC*` any total function and
`sorry` the four `_correct` theorems. The sorries are precisely the deferred obligations — validity and
extremality — and nothing above the seam needs to change.

## What this is NOT: it is not "the" seam

`Solver/Quadrant.lean` is a **mechanism**, not the substitution boundary. The boundary is `Seam/`.

Every analysis — including `lcm` — exports the same triple, set-level, in `Seam/<a>/ValidExtremal.lean`:

    <c>Sol                      the solution
    <c>Sol_valid                it satisfies the analysis's clause predicate  (over `Step`, set ops)
    <c>_greatest / <c>_least    it is extremal among solutions of that predicate

That triple is what everything above consumes, and it mentions no `MTC`, no `ESet`, no fixpoint. For the
compiler-facing analyses `Seam/<a>/Adapter.lean` packages the triples into the transform's bundle —
`LcmSpec` + `Extremal` (7 ghosts x valid + 7 x extremal), `PdceSpec`, `ReachSpec`, `CPSpec` — and
`BaseLanguage/LCM/` (transform, correctness, optimality) is universally quantified over those, containing
no `MTC`/`ESet`/`solveMTC`/`BitVec` at all.

The four quadrants here are a *reusable way to implement* that triple for any analysis whose transfer is
an `MTC` term — which is how 19 of the 21 get theirs for free, and why a new `.gsl` spec needs no new
stubs. But an analysis may satisfy its interface by **any** means.

`Solver/{lcm,pdce}/Solve.lean` do exactly that: they import `Solver.Impl` and build a shared-array bundle
directly, because the memoisation only survives when the array binding and the closure that captures it
live in ONE compiled definition. That import is **below `lcm`'s seam, not through it**: it is an
implementation detail of `lcmSolved`, which is precisely where a representation belongs.

## Why the bundle is not routed through the quadrants

Routing the bundle through these wrappers is sound (it typechecks end to end, correctness inherited via
`memoMTC*_eq` and `memoMeet_correct`/`memoJoin_correct`), but far too slow: `resMTC*` takes `n` as a
parameter, so `solveMTC*Fun`'s array binding is never shared and the fixpoint re-runs for every node. What
is required is to keep ONE definition's array binding out of a per-node lambda across a module boundary,
and `@[noinline]` on the callee is not sufficient — so the bundle binds the concrete `Array` directly.

The `memo*` forms below bind the solve before the node argument, so a caller pays for the fixpoint once;
they are correct and proven.
-/

namespace Solver

open BaseLanguage BaseLanguage.Analysis Tac Semantics Std

variable {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]

/-! ## Memoised forms — the same solutions, evaluated once.

`resMTC*` takes the node `n` as a *parameter*, so `resMTC* P univ t sd n` re-runs the whole fixpoint for
**every node** — the compiler eta-expands it and the array binding inside `solveMTCFun` never gets shared.
That is precisely why the `lcm`/`pdce` bundles exist.

`memoMTC*` binds the solve **before** the node argument, so a caller that binds `memoMTC* P univ t sd`
once (in a `let`, or a bundle field) pays for the fixpoint once and every read is a lookup. They are
*extensionally the same functions* — `memoMTC*_eq` is `rfl` — so correctness is inherited from
`resMTC*_correct` with a rewrite; there is no second contract to discharge.

A replacement solver may simply define `memoMTC* := resMTC*` (still correct, via the same `rfl`); it only
forfeits the sharing. This keeps memoisation a quality-of-implementation matter *below* the seam rather
than an obligation above it. -/

-- NOTE: each binds the concrete `Array` DIRECTLY rather than going through `solveMTC*Fun`. Routing via
-- the `*Fun` wrapper is fatal: it is inlinable, so the compiler inlines it and floats the array-building
-- `let` INSIDE the lambda, rebuilding the fixpoint on every node read — the exact defeat the bundles
-- exist to avoid. Binding the `Array` (a data value, forced at the bind) keeps it fast. Each body is
-- `decode ∘ solveMTC*Fun`'s body, so the `*_eq` bridges below are still `rfl`.

@[noinline] def memoMTC (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) :
    Node → Std.HashSet α :=
  let arr := solveMTC P univ t sd
  fun n => decode univ (arr[n]?.getD (topV univ.length))

@[noinline] def memoMTCMF (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) :
    Node → Std.HashSet α :=
  let arr := solveMTCMF P univ t sd
  fun n => decode univ (if n < P.size then gA arr n else 0)

@[noinline] def memoMTCBM (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → Std.HashSet α :=
  let arr := solveMTCBM P univ t hi sd
  fun n => decode univ (if n < P.size then gA arr n else encode univ (hi n))

@[noinline] def memoMTCB (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α)
    (sd : Std.HashSet α) : Node → Std.HashSet α :=
  let arr := solveMTCB P univ t lo sd
  fun n => decode univ (if n < P.size then gA arr n else encode univ (lo n))

theorem memoMTC_eq (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) :
    memoMTC P univ t sd = resMTC P univ t sd := rfl

theorem memoMTCMF_eq (P : Program) (univ : List α) (t : MTC α) (sd : Std.HashSet α) :
    memoMTCMF P univ t sd = resMTCMF P univ t sd := rfl

theorem memoMTCBM_eq (P : Program) (univ : List α) (t : MTC α) (hi : Node → Std.HashSet α)
    (sd : Std.HashSet α) : memoMTCBM P univ t hi sd = resMTCBM P univ t hi sd := rfl

theorem memoMTCB_eq (P : Program) (univ : List α) (t : MTC α) (lo : Node → Std.HashSet α)
    (sd : Std.HashSet α) : memoMTCB P univ t lo sd = resMTCB P univ t lo sd := rfl

/-- A `@[noinline]` identity barrier. `share f = f` *definitionally* (so every `rfl`/defeq proof is
    unaffected), but the compiler cannot see through it — so `def g P := share (solve P).field` is NOT
    eta-expanded into `fun n => (solve P).field n`, which would rebuild the whole bundle on every node
    read. This is the mechanism the lcm/pdce memoisation rests on. -/
@[noinline] def share {β : Type} (f : Node → β) : Node → β := f

theorem share_eq {β : Type} (f : Node → β) : share f = f := rfl

/-! ## Confluence, set-level.

`Solver.Impl`'s `resMeet`/`resJoin` take the earlier ghost as a *bitvector* field (`Node → ESet`).
`memoMeet`/`memoJoin` take it as a plain
`Node → HashSet α` and re-express the contract over `MeetSpecS`/`JoinSpecS` (`Solver.Spec`), so the
bundle never mentions a representation. Correctness is inherited from `resMeet_correct`/`resJoin_correct`
through the `decode ∘ encode` round-trip, valid under the universe bound the caller already proves. -/

/-- Encode the ghost ONCE per node into a concrete array, rather than on every successor read.
    Extensionally `fun m => encode univ (Y m)` (`encodeMemo_eq`) — the array is purely a memo. Without
    it the meet re-encodes each successor's set on every read (`O(|univ|)` where the bitvector field it
    replaced was an `O(1)` lookup), and since LCM threads `tauP` *inside* `used`'s fixpoint term (via
    `latestNode`) that cost multiplies by iterations x edges. This is the representation living BELOW the seam, where it
    belongs: the contract above is `MeetSpecS`, set-level. -/
@[noinline] def encodeMemo (P : Program) (univ : List α) (Y : Node → Std.HashSet α) :
    Node → ESet univ.length :=
  let arr : Array (ESet univ.length) := Array.ofFn (n := P.size) (fun m => encode univ (Y m.val))
  fun m => arr[m]?.getD (encode univ (Y m))

theorem encodeMemo_eq (P : Program) (univ : List α) (Y : Node → Std.HashSet α) :
    encodeMemo P univ Y = fun m => encode univ (Y m) := by
  funext m
  show (Array.ofFn (n := P.size) (fun m => encode univ (Y m.val)))[m]?.getD (encode univ (Y m))
      = encode univ (Y m)
  by_cases h : m < P.size
  · rw [Array.getElem?_eq_getElem (by simpa using h)]; simp
  · rw [Array.getElem?_eq_none (by simpa using h), Option.getD_none]

@[noinline] def memoMeet (P : Program) (univ : List α) (Y : Node → Std.HashSet α) :
    Node → Std.HashSet α :=
  resMeet P univ (encodeMemo P univ Y)

@[noinline] def memoJoin (P : Program) (univ : List α) (Y : Node → Std.HashSet α) :
    Node → Std.HashSet α :=
  resJoin P univ (encodeMemo P univ Y)

variable {P : Program} {univ : List α}

/-- `MeetSpec` over the encoded ghost IS `MeetSpecS` over the ghost, given the universe bound. -/
theorem meetSpec_encode_iff (hnd : univ.Nodup) {Y : Node → Std.HashSet α}
    (hY : ∀ n, ∀ x ∈ Y n, x ∈ univ) (τ : Node → Std.HashSet α) :
    MeetSpec P univ (fun m => encode univ (Y m)) τ ↔ MeetSpecS P univ Y τ := by
  constructor
  · exact fun h => ⟨fun c c' hs x hx =>
      (mem_decode_encode_of_sub (fun y hy => hY c'.node y hy)).mp (h.1 c c' hs x hx), h.2⟩
  · exact fun h => ⟨fun c c' hs x hx =>
      (mem_decode_encode_of_sub (fun y hy => hY c'.node y hy)).mpr (h.1 c c' hs x hx), h.2⟩

theorem joinSpec_encode_iff (hnd : univ.Nodup) {Y : Node → Std.HashSet α}
    (hY : ∀ n, ∀ x ∈ Y n, x ∈ univ) (τ : Node → Std.HashSet α) :
    JoinSpec P univ (fun m => encode univ (Y m)) τ ↔ JoinSpecS P univ Y τ := by
  constructor
  · exact fun h => ⟨fun c c' hs x hx =>
      h.1 c c' hs x ((mem_decode_encode_of_sub (fun y hy => hY c'.node y hy)).mpr hx), h.2⟩
  · exact fun h => ⟨fun c c' hs x hx =>
      h.1 c c' hs x ((mem_decode_encode_of_sub (fun y hy => hY c'.node y hy)).mp hx), h.2⟩

/-- **The meet is the greatest `MeetSpecS` solution** — the confluence half of the seam contract. -/
theorem memoMeet_correct (hwf : WellFormed P) (hnd : univ.Nodup) {Y : Node → Std.HashSet α}
    (hY : ∀ n, ∀ x ∈ Y n, x ∈ univ) :
    MeetSpecS P univ Y (memoMeet P univ Y) ∧
    ∀ σ, MeetSpecS P univ Y σ → ∀ n, ∀ x ∈ σ n, x ∈ memoMeet P univ Y n := by
  rw [memoMeet, encodeMemo_eq]
  obtain ⟨hv, hg⟩ := resMeet_correct (univ := univ) hwf hnd (fun m => encode univ (Y m))
  exact ⟨(meetSpec_encode_iff hnd hY _).mp hv,
         fun σ hσ => hg σ ((meetSpec_encode_iff hnd hY σ).mpr hσ)⟩

/-- **The join is the least `JoinSpecS` solution.** -/
theorem memoJoin_correct (hwf : WellFormed P) (hnd : univ.Nodup) {Y : Node → Std.HashSet α}
    (hY : ∀ n, ∀ x ∈ Y n, x ∈ univ) :
    JoinSpecS P univ Y (memoJoin P univ Y) ∧
    ∀ σ, JoinSpecS P univ Y σ → ∀ n, ∀ x ∈ memoJoin P univ Y n, x ∈ σ n := by
  rw [memoJoin, encodeMemo_eq]
  obtain ⟨hv, hl⟩ := resJoin_correct (univ := univ) hwf hnd (fun m => encode univ (Y m))
  exact ⟨(joinSpec_encode_iff hnd hY _).mp hv,
         fun σ hσ => hl σ ((joinSpec_encode_iff hnd hY σ).mpr hσ)⟩

/-! ## The seam, machine-checked.

These `#check`s pin the exact shape of the 8 exported symbols. If `Solver.Impl` ever drifts from the
contract — or a replacement solver fails to provide it — this file stops compiling. -/

#check @resMTC
#check @resMTCMF
#check @resMTCBM
#check @resMTCB

#check @resMTC_correct
#check @resMTCMF_correct
#check @resMTCBM_correct
#check @resMTCB_correct

#check @memoMTC
#check @memoMTCMF
#check @memoMTCBM
#check @memoMTCB
#check @memoMTC_eq
#check @memoMTCMF_eq
#check @memoMTCBM_eq
#check @memoMTCB_eq

#check @memoMeet
#check @memoJoin
#check @memoMeet_correct
#check @memoJoin_correct
#check @share

end Solver
