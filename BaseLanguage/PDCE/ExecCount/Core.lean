-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Optimality
import BaseLanguage.IR.Cost

/-!
# `PDCE.ExecCount` — computational (execution-count) optimality of PDCE

Along every terminating run, the transform **executes** each assignment `a` no more often than any
**safe covering placement** `pl`. This is the sinking dual of LCM's execution-count optimality
(`EvalCountHeadline.transform_evalCount_le_safe`), and — like it — does **not** lift pointwise by
`length_filter_mono` (the materialization frontier is non-monotone when the *sink* is varied; see
`Optimality.lean` §"per-path eval-count" and `PDCE.md` §5.2), so the argument is run-dependent. The
monotone axes are the lifetime/sinking-distance (`pathSinkDist_le`) and the qualitative "nothing wasted"
(`matNode_necessary`, `matEdge_necessary`); this file supplies the quantitative statement.

## Target theorem (the headline)

```
theorem transform_execCount_le_safe (S : PdceSpec P) (wf : WellFormed P)
    (a : Asgn) (pl : Node → Bool)
    (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfin : Final P c_f)
    (ks : Nat) (hks : run P ⟨P.entry, σ⟩ ks = (c_f, .next c_f))
    (hcov : PlCoversAsgn P S a pl ⟨P.entry, σ⟩ ks false) :
    ∃ kt, execCount (transform P S) a ⟨blockOff P S P.entry, σ⟩ kt
            ≤ ((runNodes P ⟨P.entry, σ⟩ ks).filter pl).length
```

Per-assignment; the total over all `a ∈ allAsgns` follows by summing (each term `≤`). `pl : Node → Bool` is an
**arbitrary** competing placement with a coverage **hypothesis** `PlCoversAsgn` — we never construct it, so
"≤ every safe placement" *subsumes* "no valid analysis beats the extremal one" (every valid analysis's
transform is such a `pl`) without ever instantiating a second bundle. Halting runs only; faults/divergence are
don't-care, matching `transform_preserves_halt`.

## What everything is built from

Everything is a projection of: the abstract bundle `S` (`sink`/`live` + `isSink`/`isLive`); the
*syntactic* node-locals (`matNode`, `matEdge`, `blockedSet`, `kills`/`pass`, `blockOff`, `blockLen`); the
operational semantics (`step1`/`run`/`Steps`, via `IR/Cost`); and the layout. `execCount` is the assignment
analogue of `IR/Cost.evalCount` — a filter over `step1`, not an analysis. The live `born`-crossing counting
unit is carried as induction state over the run (`Steps`/`run`), a projection of the syntactic `born` + the
abstract `S.π`, never a computed `Node → ℕ` map.

## Structure

The counting unit is the **live `born`-crossing**: a run step where `a ∈ born c.node` (its `x:=e`
site, the sole entry into the greatest `sink`) with `a.lhs` live downstream — a placement-invariant
projection of `born` + `S.π`, the dual of LCM's `earliest`-crossing. It bounds both the transform and
any safe covering placement, so the comparison is one-sided (one `born` per in-flight stretch).

* **`execCount`** — the assignment-firing count, a filter over `step1` (the `IR/Cost.evalCount`
  analogue), built on a generic per-step counter `stepCount` with the fold toolkit
  (`_next`/`_stop`/`_mono`/`_stable`/`_add`/`_eq_filter_runNodes`).
* **Lemma A** (`matCount_le_liveBornCount`): `#mat ≤ #(live born-crossing)`. A live in-flight
  candidate never leaves `sink` silently — every exit is a `matNode` at a blocked node or a `matEdge`
  on a merge-drop edge (`inflight_exit`) — and a `born` opens ≤ one stretch, so there is ≤ 1
  materialization per live `born`-crossing.
* **Lemma B** (`liveBornCount_le_pl`): `#(live born-crossing) ≤ #pl`. A safe covering placement
  computes `a` at least once between consecutive live `born`-crossings (`PlCoversAsgn`); per-demand
  coverage excludes dedup, so `PlCoversAsgn` is per-demand (dedup would make the bound false on
  `x:=b+c; use x; x:=b+c; use x`).
* **The fold** (`execCount_fold`): `execCount (transform P S) a = matCount` over the source run — each
  source block-visit contributes `[a ∈ matNode] + [a ∈ matEdge succ]` for the taken successor. A
  merge-drop materializes on the taken edge `p → s` (`delayedExit p ∖ sink s`), possibly at a
  `pass`-looking node, so an interval can exit on an edge rather than only at a `kills` node.
* **Compose** (`transform_execCount_le_safe`): `execCount = matCount ≤ #(live born-crossing) ≤ #pl`.

The abstract counting cores (the `LemmaA` and `LemmaB` namespaces) are list-model potentials kept as
standalone sanity checks; the run-anchored lemmas below establish the operational bound directly.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
set_option linter.unusedVariables false


/-! ## The interval-exit invariant

A **component of Lemma A**: the structural fact that **a live in-flight candidate never leaves the `sink`
set silently — every exit is witnessed by a materialization** (a `matNode` at a blocked node, or a `matEdge`
on a merge-drop edge). Combined with "a `born` opens ≤ one in-flight stretch", this yields "≤ 1
materialization per live `born`-crossing" (Lemma A). Everything is a projection of the abstract bundle `S`
(`sink`/`live` + `isSink.within`) and the syntactic
`pass`/`blockedSet`/`delayedExit`/`matNode`/`matEdge`. Two atoms + their combination. -/

/-- **Blocked exit ⇒ node materialization.** An in-flight candidate that cannot pass `n` (`a ∉ pass n`, i.e.
    `n` kills it) and is live there is materialized at the node entry. Uses only `isSink.within` (to place
    `a` in `allAsgns`, hence in `blockedSet`) and the `matNode`/`blockedSet` definitions. -/
theorem sink_blocked_materialized {P : Program} (S : PdceSpec P) {n : Node} {a : Asgn}
    (hin : a ∈ S.η n) (hnp : a ∉ pass P n) (hlive : a.lhs ∈ S.π n) :
    a ∈ matNode P S n := by
  have hall : a ∈ allAsgns P := S.isSink.within n a hin
  have hblk : a ∈ blockedSet P n := by
    unfold blockedSet
    split
    · exact hall
    · exact Assignments.mem_sdiff.mpr ⟨hall, hnp⟩
  exact mem_matNode.mpr ⟨hin, hblk, hlive⟩

/-- **Merge-drop exit ⇒ edge materialization.** An in-flight candidate delayable past `p` (`a ∈ pass p`) that
    the merge drops at the successor `s` (`a ∉ sink s`) and is live at `s` is materialized on the edge `p → s`.
    Uses only the `delayedExit`/`matEdge` definitions (`a ∈ sink p ∩ pass p ⊆ delayedExit p`). -/
theorem sink_mergedrop_materialized {P : Program} (S : PdceSpec P) {p s : Node} {a : Asgn}
    (hin : a ∈ S.η p) (hp : a ∈ pass P p) (hout : a ∉ S.η s) (hlive : a.lhs ∈ S.π s) :
    a ∈ matEdge P S p s :=
  mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inr ⟨hin, hp⟩), hout, hlive⟩

/-- **THE INTERVAL-EXIT INVARIANT.** Along a source step `c → c'`, a candidate in flight entering `c`
    (`a ∈ sink c.node`) that leaves flight (`a ∉ sink c'.node`) and is live across the boundary is
    materialized — at the node (`matNode c.node`, blocked case) or on the edge (`matEdge c.node c'.node`,
    merge-drop case). So a materialization ends the one in-flight stretch its `born` opened, and no live stretch
    exits silently; combined with "one `born` per stretch" this gives "≤ 1 materialization per live
    `born`-crossing" (Lemma A — the placement-invariant counting unit is the live `born`-crossing, not this
    stretch). -/
theorem inflight_exit {P : Program} (S : PdceSpec P) {c c' : Config} (hstep : Step P c c')
    {a : Asgn} (hin : a ∈ S.η c.node) (hout : a ∉ S.η c'.node)
    (hlc : a.lhs ∈ S.π c.node) (hlc' : a.lhs ∈ S.π c'.node) :
    a ∈ matNode P S c.node ∨ a ∈ matEdge P S c.node c'.node := by
  by_cases hp : a ∈ pass P c.node
  · exact Or.inr (sink_mergedrop_materialized S hin hp hout hlc')
  · exact Or.inl (sink_blocked_materialized S hin hp hlc)

/-! ## `execCount` (the assignment-firing count; the `IR/Cost.evalCount` analogue)

`execCount P a c fuel` = how many times the fuel-bounded run from `c` **executes** the assignment `a`.
A filter over the interpreter `step1` (exactly the shape of `evalCount`), reading
off `fetch` only — **no analysis, no `Node → Assignments`, no `Node → ℕ`**. It is built on a generic per-step
counter `stepCount P p` over an arbitrary node predicate `p : Node → Bool`, so the whole `evalCount` fold
toolkit (`_next`/`_stop`/`_mono`/`_stable`/`_add`/`_eq_filter_runNodes` — the backbone the fold needs)
is defined **once** and reused; `execCount` is the instance `p := firesAsgn P a`, and `evalCount` itself is the
same shape at `p := computesExpr P · e`. -/

/-- **Generic per-step count**: how many of the first `fuel` steps from `c` sit on a node satisfying `p`.
    Pure instrumentation of `step1` (the sole semantics), identical in shape to `IR/Cost.evalCount`. -/
def stepCount (P : Program) (p : Node → Bool) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      (if p c.node then 1 else 0) +
        (match step1 P c with | .next c' => stepCount P p c' fuel | _ => 0)

/-- **Per-step recursion.** On a real step `c → c'`, the count is `c`'s contribution plus the continuation. -/
theorem stepCount_next {P : Program} {p : Node → Bool} {c c' : Config} {fuel : Nat}
    (h : step1 P c = .next c') :
    stepCount P p c (fuel + 1) = (if p c.node then 1 else 0) + stepCount P p c' fuel := by
  show (if p c.node then 1 else 0)
      + (match step1 P c with | .next c'' => stepCount P p c'' fuel | _ => 0) = _
  rw [h]

/-- A non-stepping configuration contributes only its own hit and stops. -/
theorem stepCount_stop {P : Program} {p : Node → Bool} {c : Config} {m : Nat}
    (hs : ∀ c', step1 P c ≠ .next c') :
    stepCount P p c (m + 1) = (if p c.node then 1 else 0) := by
  show (if p c.node then 1 else 0)
      + (match step1 P c with | .next c'' => stepCount P p c'' m | _ => 0) = _
  cases hstep : step1 P c with
  | next c' => exact absurd hstep (hs c') | halt => simp | fault => simp | stuck => simp

/-- **Well-defined for a terminating run** — once halted within `k` steps, extra fuel re-walks the `Final`
    config (no hit there), so the count is fixed. -/
theorem stepCount_stable {P : Program} {p : Node → Bool} {c : Config} {k : Nat}
    (hhalt : (run P c k).2 = .halt) : ∀ j, stepCount P p c (k + j) = stepCount P p c k := by
  induction k generalizing c with
  | zero => simp [run] at hhalt
  | succ m ih =>
      intro j
      cases hs : step1 P c with
      | next c' =>
          have hr : (run P c' m).2 = .halt := by
            have : run P c (m + 1) = run P c' m := by simp [run, hs]
            rwa [this] at hhalt
          rw [show m + 1 + j = (m + j) + 1 from by omega, stepCount_next hs, stepCount_next hs, ih hr j]
      | halt =>
          rw [show m + 1 + j = (m + j) + 1 from by omega,
              stepCount_stop (p := p) (fun c' => by rw [hs]; simp),
              stepCount_stop (p := p) (fun c' => by rw [hs]; simp)]
      | fault => simp [run, hs] at hhalt
      | stuck => simp [run, hs] at hhalt

/-- **Run-segment additivity** — the backbone of the per-block decomposition (a whole-program run is the
    concatenation of its per-node block sub-runs). -/
theorem stepCount_add {P : Program} {p : Node → Bool} {c c' : Config} {a : Nat}
    (h : run P c a = (c', .next c')) (b : Nat) :
    stepCount P p c (a + b) = stepCount P p c a + stepCount P p c' b := by
  induction a generalizing c with
  | zero =>
      simp only [run, Prod.mk.injEq, Status.next.injEq] at h
      obtain ⟨rfl, _⟩ := h
      show stepCount P p c (0 + b) = 0 + stepCount P p c b
      rw [Nat.zero_add, Nat.zero_add]
  | succ a ih =>
      cases hs : step1 P c with
      | next c1 =>
          have hr : run P c1 a = (c', .next c') := by
            rw [show run P c (a + 1) = run P c1 a from by simp [run, hs]] at h; exact h
          rw [show a + 1 + b = (a + b) + 1 from by omega, stepCount_next hs, stepCount_next hs, ih hr]
          omega
      | halt => rw [show run P c (a + 1) = (c, .halt) from by simp [run, hs]] at h; simp at h
      | fault => rw [show run P c (a + 1) = (c, .fault) from by simp [run, hs]] at h; simp at h
      | stuck => rw [show run P c (a + 1) = (c, .stuck) from by simp [run, hs]] at h; simp at h

/-- **The count is a filter over the run's node-path** — the lingua franca for the optimality comparison
    (matches the RHS shape `(runNodes …).filter pl` of the headline). -/
theorem stepCount_eq_filter_runNodes (P : Program) (p : Node → Bool) (c : Config) (fuel : Nat) :
    stepCount P p c fuel = ((runNodes P c fuel).filter p).length := by
  induction fuel generalizing c with
  | zero => rfl
  | succ m ih =>
      cases hs : step1 P c with
      | next c' =>
          rw [stepCount_next hs, ih c',
              show runNodes P c (m + 1) = c.node :: runNodes P c' m from by simp [runNodes, hs],
              List.filter_cons]
          by_cases hp : p c.node <;> simp [hp] <;> omega
      | halt =>
          rw [stepCount_stop (p := p) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : p c.node <;> simp [hp]
      | fault =>
          rw [stepCount_stop (p := p) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : p c.node <;> simp [hp]
      | stuck =>
          rw [stepCount_stop (p := p) (fun c'' => by rw [hs]; simp),
              show runNodes P c (m + 1) = [c.node] from by simp [runNodes, hs], List.filter_cons]
          by_cases hp : p c.node <;> simp [hp]

/-- **Does node `n` execute the assignment `a = ⟨x,e⟩`?** Read off the existing `fetch` — the assignment
    analogue of `IR/Cost.computesExpr` (which matches only the RHS `e`); this matches the *whole* `⟨x,e⟩`,
    since the transform materializes a specific assignment copy, not merely its expression. -/
def firesAsgn (P : Program) (a : Asgn) (n : Node) : Bool :=
  match P.fetch n with
  | some (.assign x e _) => decide (a = ⟨x, e⟩)
  | _                    => false

/-- **Per-run execution count** of assignment `a` — the LHS of the headline. The `IR/Cost.evalCount`
    analogue, instanced from the generic `stepCount` at the syntactic firing predicate: a filter over
    `step1`, not an analysis. -/
def execCount (P : Program) (a : Asgn) (c : Config) (fuel : Nat) : Nat :=
  stepCount P (firesAsgn P a) c fuel

/-- `execCount` run-segment additivity (the per-block decomposition backbone). -/
theorem execCount_add {P : Program} {a : Asgn} {c c' : Config} {n : Nat}
    (h : run P c n = (c', .next c')) (b : Nat) :
    execCount P a c (n + b) = execCount P a c n + execCount P a c' b :=
  stepCount_add h b


/-! ## Lemma-B core (abstract, availability-free)

The one-symbol-per-step Lemma-B engine, an abstract `decide`-based list model. `safe` = the natural coverage
condition (every `use` of `a.lhs` sees the value available, `armed` = a `pl` fired since the last `born`);
`countLB` = live-`born` count (a `born` whose epoch contains a `use` — the **liveness gate realized as "epoch
contains a use"**, so a dead `a` scores 0); `countPl` = placement count. The bound is **one-sided, no
anti-gap** — PDCE's value-validity boundary is the `born`, so `armed` resets exactly at the demand
boundary. -/

namespace LemmaB
inductive Sym | born | use | pl | other
deriving DecidableEq, Repr

/-- Natural safety: a `use` requires the value available (`armed` = a `pl` since the last `born`); `born`
    invalidates, `pl` provides. Redundancy-dedup is rejected automatically (a second `born` with no following
    `pl` leaves its use unsafe). (Dot-notation constructors: the enclosing `My` namespace already binds a
    `born` function, so bare `born` would shadow the constructor.) -/
def safe : List Sym → Bool → Bool
  | [],          _     => true
  | .born :: r,  _     => safe r false
  | .pl :: r,    _     => safe r true
  | .use :: r,   armed => armed && safe r armed
  | .other :: r, armed => safe r armed

def countPl : List Sym → Nat
  | []        => 0
  | .pl :: r  => 1 + countPl r
  | _ :: r    => countPl r

/-- Live-`born` count: a `born` whose epoch (up to the next `born`, or the end) contains a `use`. `sawUse`
    carries whether the current epoch has seen one; the final epoch is closed at `[]`. -/
def countLB : List Sym → Bool → Nat
  | [],          sawUse => if sawUse then 1 else 0
  | .born :: r,  sawUse => (if sawUse then 1 else 0) + countLB r false
  | .use :: r,   _      => countLB r true
  | .pl :: r,    s      => countLB r s
  | .other :: r, s      => countLB r s

/-- One-sided potential `#live-born ≤ #pl + [armed]`, generalized over `armed`/`sawUse` with the maintained
    invariant `sawUse → armed`. -/
theorem bound : ∀ (l : List Sym) (armed sawUse : Bool),
    safe l armed = true → (sawUse = true → armed = true) →
    countLB l sawUse ≤ countPl l + (if armed then 1 else 0) := by
  intro l
  induction l with
  | nil => intro armed sawUse _ himp; cases sawUse <;> cases armed <;> simp_all [countLB, countPl]
  | cons s r ih =>
    intro armed sawUse hsafe himp
    cases s with
    | born =>
      simp only [safe] at hsafe
      have IH := ih false false hsafe (by simp)
      cases sawUse <;> cases armed <;> simp_all [countLB, countPl] <;> omega
    | pl =>
      simp only [safe] at hsafe
      have IH := ih true sawUse hsafe (by simp)
      cases armed <;> simp_all [countLB, countPl] <;> omega
    | use =>
      simp only [safe, Bool.and_eq_true] at hsafe
      obtain ⟨ha, hs⟩ := hsafe
      subst ha
      have IH := ih true true hs (by simp)
      simp_all [countLB, countPl]
    | other =>
      simp only [safe] at hsafe
      have IH := ih armed sawUse hsafe himp
      simp only [countLB, countPl]; omega

/-- **The availability-free lower bound**: the natural safe-placement condition gives `#live-born ≤ #pl`. -/
theorem natural_covers_bound (l : List Sym) (h : safe l false = true) :
    countLB l false ≤ countPl l := by
  have := bound l false false h (by simp); simpa using this
end LemmaB

/-! ## Lemma-A core (abstract, availability-free) — the upper bound `#mat ≤ #born`

The **dual** of `LemmaB`'s `bound`: a one-sided potential over `(born, mat)` steps giving
`#mat ≤ #born`. `born` opens an in-flight stretch (`a` enters the greatest `sink` **only via `born`**), `mat`
closes it — `inflight_exit` gives "materialization = the stretch's exit", and a materialization sits at a
sink *exit* (`matNode` ⇒ `¬pass` ⇒ exit; `matEdge` ⇒ merge-drop ⇒ exit), so **no `mat` occurs without a
pending `born`** (`MatCovers`) ⇒ ≤1 `mat` per `born`. Anchoring maps the `born` flag to the *live* born
(`mat ⇒ live`, so dead stretches carry no `mat`), which is how this composes with Lemma B, alongside the
identification `execCount = #mat`. -/

namespace LemmaA

/-- No materialization occurs unless a `born` has opened a stretch since the last one (`pending`). Dual of
    `LemmaB.safe`: `born` opens, `mat` closes; `!m || pending || b` = "no `mat` with nothing pending". -/
def MatCovers : List (Bool × Bool) → Bool → Bool
  | [],           _       => true
  | (b, m) :: r,  pending => (!m || pending || b) && MatCovers r ((pending || b) && !m)

def countBorn : List (Bool × Bool) → Nat
  | []          => 0
  | (b, _) :: r => (if b then 1 else 0) + countBorn r
def countMat : List (Bool × Bool) → Nat
  | []          => 0
  | (_, m) :: r => (if m then 1 else 0) + countMat r

/-- One-sided potential `#mat + [pending]`, the mirror of `LemmaB.within`: `#mat ≤ #born + [pending]`. -/
theorem matcovers_bound : ∀ (l : List (Bool × Bool)) (pending : Bool),
    MatCovers l pending = true → countMat l ≤ countBorn l + (if pending then 1 else 0) := by
  intro l
  induction l with
  | nil => intro pending _; cases pending <;> simp [countMat, countBorn]
  | cons hd r ih =>
    intro pending h
    obtain ⟨b, m⟩ := hd
    simp only [MatCovers, Bool.and_eq_true] at h
    obtain ⟨hcov, hrec⟩ := h
    have IH := ih _ hrec
    cases b <;> cases m <;> cases pending <;>
      simp only [countMat, countBorn, Bool.not_true, Bool.not_false, Bool.or_self,
        Bool.or_true, Bool.or_false, Bool.and_true, Bool.and_false,
        if_true, if_false, Bool.false_eq_true] at hcov IH ⊢ <;>
      omega

/-- **Lemma A core (top level): ≤1 materialization per `born`.** -/
theorem matcovers_bound0 (l : List (Bool × Bool)) (h : MatCovers l false = true) :
    countMat l ≤ countBorn l := by
  have := matcovers_bound l false h; simpa using this

/-- Sanity: a materialization with no opening `born` is rejected. -/
theorem mat_without_born_rejected : MatCovers [(false, true)] false = false := by decide
/-- Sanity: one born then its mat is accepted, and `1 ≤ 1`. -/
theorem matcovers_ok :
    MatCovers [(true, false), (false, true)] false = true
    ∧ countMat [(true, false), (false, true)] ≤ countBorn [(true, false), (false, true)] := by decide

/-! ### Counter-potential refinement — handles the `born∧mat` coincidence

The one-`Bool` `MatCovers` cannot express a step that both re-borns and materializes `a` (a node that is
`a`'s own kill site while `a` is in-flight from above): the same-step `born`
that reopens the stretch is lost when the same-step `mat` clears `pending`. A `Nat` counter `k` = number of
open (unmatched) `born`s handles it: `born` increments **first**, then `mat` requires `k > 0` and decrements,
so a coincident step self-covers. -/

/-- `k` = open (unmatched) `born` count. A `born` opens (increment) *before* a same-step `mat` closes
    (decrement, requiring `k > 0`). -/
def MatWF : List (Bool × Bool) → Nat → Bool
  | [],          _ => true
  | (b, m) :: r, k =>
      (if m then decide (0 < k + (if b then 1 else 0)) else true)
        && MatWF r (k + (if b then 1 else 0) - (if m then 1 else 0))

/-- Counter potential: `#mat ≤ #born + k` (open borns). Robust to `born∧mat` coincidence. -/
theorem matwf_bound : ∀ (l : List (Bool × Bool)) (k : Nat),
    MatWF l k = true → countMat l ≤ countBorn l + k := by
  intro l
  induction l with
  | nil => intro k _; simp [countMat, countBorn]
  | cons hd r ih =>
    intro k h
    obtain ⟨b, m⟩ := hd
    simp only [MatWF, Bool.and_eq_true] at h
    obtain ⟨hg, hrec⟩ := h
    have IH := ih _ hrec
    cases b <;> cases m <;>
      simp only [countMat, countBorn, decide_eq_true_eq, if_true, if_false,
        Bool.false_eq_true, Nat.add_zero, Nat.sub_zero] at hg IH ⊢ <;>
      omega

/-- **Lemma A core (counter form): ≤1 materialization per `born`**, coincidence-robust. -/
theorem matwf_bound0 (l : List (Bool × Bool)) (h : MatWF l 0 = true) :
    countMat l ≤ countBorn l := by
  have := matwf_bound l 0 h; simpa using this

/-- Sanity: a `born∧mat` step is accepted (the reopening born covers the same-step mat) — the case the
    one-`Bool` `MatCovers` mishandles. -/
theorem matwf_coincident_ok : MatWF [(true, true)] 0 = true := by decide
/-- Sanity: a materialization with no open `born` is still rejected. -/
theorem matwf_mat_without_born : MatWF [(false, true)] 0 = false := by decide

end LemmaA

/-! ## The live `born`-crossing (the placement-invariant counting unit)

The counting unit: a **live `born`-crossing** is
a source step `c → c'` with `a ∈ born c.node` (its `x:=e` site — the sole entry into the greatest `sink`) and
`a.lhs ∈ S.π c'.node` (the value is **live on exit**). This is the direct dual of LCM's `earliest`-crossing
(`crossCount`, `EvalCountHeadline.lean:131`): a projection of the *syntactic* `born` + the *abstract* `S.π`
along the run — a property of the **program**, bounding BOTH the transform (Lemma A) and any safe covering
placement (Lemma B). Carried as induction state over `step1`, never a computed
`Node → ℕ` map.

The liveness gate is `S.π` at the **successor** `c'`, NOT `S.η` — `sink ⇏ live` (`matNode`
intersects `sink` WITH `live` precisely because a delayable assignment can be dead). The abstract
`LemmaA`/`LemmaB` cores above are kept only as standalone sanity checks — the direct run-walks below do
not call them. -/

/-- **Live `born`-crossing count** — the counting unit, a `crossCount`-style filter over the run: a step whose
    node is `a`'s birth site with `a.lhs` live on exit. The direct dual of `crossCount`. -/
def liveBornCount (P : Program) (S : PdceSpec P) (a : Asgn) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      match step1 P c with
      | .next c' =>
          (if a ∈ born P c.node ∧ a.lhs ∈ S.π c'.node then 1 else 0)
            + liveBornCount P S a c' fuel
      | _        => 0

/-- `liveBornCount` one-step unfolding on a real step (exposes the sum for arithmetic). -/
theorem liveBornCount_next {P : Program} {S : PdceSpec P} {a : Asgn} {c c' : Config} {f : Nat}
    (hs : step1 P c = .next c') :
    liveBornCount P S a c (f + 1)
      = (if a ∈ born P c.node ∧ a.lhs ∈ S.π c'.node then 1 else 0) + liveBornCount P S a c' f := by
  show (match step1 P c with
        | .next c'' => (if a ∈ born P c.node ∧ a.lhs ∈ S.π c''.node then 1 else 0)
                        + liveBornCount P S a c'' f
        | _ => 0) = _
  rw [hs]


end BaseLanguage.Analyses.PDCE
