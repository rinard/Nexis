# Handoff — making LCM correctness depend on **validity** instead of **extremality**

Status as of commit `e207c90`. Everything described below builds:
`lake build`, `lake test`, `lake exe gengen-check`, `lake exe gengen-stress`,
`bash script/check-seam.sh`, `bash script/check-solver-seam.sh` — all exit 0.

**Check the build with `lake build >/dev/null 2>&1; echo $?`.** Piping to `tail`
and reading `$?` reports the *pipe's* status and gives false greens.

---

## How to use this document

**The job is §4, steps 1–5, in order.** Each step names its files and line
numbers. Land each one green — all six commands above exit 0 — and report before
starting the next; do not batch them. Read §0, §3 and §5 before touching
anything: §0 rules out a whole class of tempting-but-forbidden designs, §3 is the
scope boundary, and §5 records findings that cost real effort to establish.

**The completion predicate.** The goal is reached when, and only when,

```
BaseLanguage/Pass/Correctness/PipelineToAsm.lean
```

no longer takes `hLcm : Analyses.LCM.Extremal Slcm`, and `main_compile_correct`
is proved without it. **Do not claim soundness-from-validity before that.**

That predicate exists because it is easy to get wrong. In the session that
produced this document, `main_compile_correct_mat` was briefly described as
progress on soundness; it is not — it is the existing theorem with a different
*extremal* bundle substituted, and it requires `hLcm` exactly as the classic one
does. Wiring an analysis into the driver, proving facts *about* a ghost, and
removing a hypothesis *from a theorem* are three different things. Only the
third is the job.

Partial credit is real and worth reporting — "step 3 done, `Cov` rebuilt, `hLcm`
still required" is a good outcome. Overstatement is not.

---

## 0. The prime directive

Binding on all work here (from `README.md` at the submission commit; the
operational clauses still hold even though the section was reworked when the
solver stopped being a stub):

- **Never write a dataflow fixpoint solver.** A transform or proof that seems to
  need a new analysis does not — the needed fact is a projection of the existing
  bundle `S` or an existing syntactic function.
- **Reachability is a traversal, not an analysis.** Anything that resembles a
  dataflow fixpoint but is in fact a graph traversal must be a plain **inductive
  relation**: no fixpoint, no fuel, no analysis domain.
- **Litmus:** genuine dataflow ⇒ stub it as an extremal bundle; reachability /
  structure ⇒ inductive relation; otherwise it is plumbing. If you are about to
  iterate to a fixpoint, **stop.**

An earlier draft of this work proposed computing temp-availability inside the
transform. That is a directive violation. The remedy the directive itself
supplies — *stub it as a ghost* — is why `Materialized` exists.

---

## 1. The problem

`BaseLanguage/LCM/Transform.lean:127`:

```lean
def recoverable (P : Program) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.union (S.πᵤK n) (insertBefore P S n)
```

This is the **replace gate**: the transform rewrites an original `x := e` into
`x := tₑ` exactly when `e ∈ recoverable P S n`. A *valid but too-large* `πᵤ`
admits a rewrite with no matching insertion, and the program then reads a
temporary nothing ever wrote — `examples/lcm-extremality/ExtremalityNeeded.lean`
observes `0` where the source observes `7`.

Excluding that needs a **lower** bound on a **least** fixpoint. Leastness
quantifies over every solution (`∀ g, Used P … g → πᵤ ⊆ g`), so it is
irreducibly second-order and **no clause can express it**. That is why
`transform_preserves_halt` takes `Extremal S` rather than validity.

## 2. The fix, and what is already proved

`analyses/lcmmat/LcmMat.gsl` adds a seventh ghost whose polarity is inverted:

```
history Materialized ηₘ : Assignments[Expr] {      -- fwd·must
  update : ∀ n→n'. ηₘ(n') ⊆ matPlace(πₐ,ηₐ,ηₚ,τₚ,τᵤ)(n,n') ∪ (ηₘ(n) ∖ notPass(n))
  seed   : ηₘ(entry) ⊆ entrySeed
  within : ∀ n. ηₘ(n) ⊆ allExprs
}
```

An **upper** bound — which is the soundness statement itself, and the direction
every clause already expresses. No language extension: this is the same
`place ∪ (self ∖ gres)` shape `Postponable` uses.

Proved, all axiom-clean `[propext, Classical.choice, Quot.sound]`:

| theorem | file | says |
|---|---|---|
| `mem_matPlace_iff` | `Seam/lcmmat/Sound.lean` | `matPlace` **is** the transform's placement, phase-split |
| `matAvail_written` | `Seam/lcmmat/Sound.lean` | admitted ⇒ placed along the run |
| `matAvail_placedBy` | `Seam/lcmmat/Sound.lean` | the composite, in `Transform.lean`'s vocabulary |
| `lcmMatSolved` / `_extremal` | `Seam/lcmmat/Adapter.lean` | the bundle, as an ordinary `LcmSpec` |
| `LcmAnalysis.bundle_extremal` | `Seam/lcmmat/Adapter.lean` | either analysis is extremal |
| `main_compile_correct_with` | `Seam/compile/CompileCorrect.lean` | end-to-end, generic over the analysis |

```lean
@matAvail_placedBy : (∀ e, S.keep e = true) →
    Materialized P S.πₐ S.ηₐ S.ηₚ S.τₚ S.τᵤ m →
      Steps P ⟨P.entry, σ⟩ c → ∀ e, e ∈ m c.node → PlacedBy P S c e
```

**No `Extremal` anywhere in that chain.** `PlacedBy` is an inductive relation
over `Step`, phrased with `insertEdge` / `insertBefore` / `pass`.

## 3. What is NOT done — read this before claiming anything

- **`Transform.lean` still gates on `πᵤK ∪ insertBefore`.** Nothing in §2 is
  consumed by any correctness theorem. `grep -rn "matAvail_placedBy" --include="*.lean" .`
  returns only its own file.
- **`pipeline_to_asm` still takes `hLcm : Analyses.LCM.Extremal Slcm`**
  (`BaseLanguage/Pass/Correctness/PipelineToAsm.lean:78`), so
  `main_compile_correct_mat` requires extremality exactly as the classic one
  does. The `--lcm-analysis=mat` flag is *wiring*, not a soundness result; both
  settings emit byte-identical assembly.
- **The shipped compiler's dependence on extremality is unchanged.**

## 4. The remaining work, in order

### Step 1 — `ηₘ` into the bundle
`analyses/lcm/LcmAdapter.lean:22`. Add `ηₘ : Node → Assignments` and
`isMat : Materialized P πₐ ηₐ ηₚ τₚ τᵤ ηₘ`. Every `LcmSpec` construction must
supply them: `Seam/lcm/Adapter.lean` (`lcmSolved`), `Seam/lcmmat/Adapter.lean`,
`BaseLanguage/LCM/BasicCorrect.lean` (`mkBasic`), and any test fixtures.
`LcmSpec.withKeep` and `Extremal.withKeep` must carry the new field through.

*Decision to make:* whether the classic bundle keeps a degenerate `ηₘ := ∅`
(valid, so `isMat` is discharged trivially, and the mat gate then replaces
nothing) or whether `lcmSolved` is retired in favour of `lcmMatSolved`. The
latter is cleaner; the former keeps a fallback.

### Step 2 — the gate
```lean
def recoverable (P : Program) (S : LcmSpec P) (n : Node) : Assignments :=
  Assignments.union (S.ηₘ n) (insertBefore P S n)
```
`insertBefore` stays because `ηₘ` is indexed at block *entry*, before the entry
chain runs. **52 sites** mention `recoverable` across `BaseLanguage/LCM/`; most
only use `mem_recoverable`, so re-stating that lemma for the new definition
should carry many of them.

### Step 3 — `Match` / `Cov` (the substance)
`BaseLanguage/LCM/Correctness/{Match,Coverage,MatchStep}.lean`, ~1650 lines.
Replace the **demand** invariant (a frontier `M` threaded through `Cov` over
`πᵤ`) with an **availability** invariant over `ηₘ`:

> for every `e ∈ ηₘ(n)`, `eval τ (tempFor e) = eval σ e`

Maintained across a step by `S.isMat.update` split with `mem_union`: the fresh
disjunct is discharged by the block-execution lemmas (`matNode_execF`,
`steps_insSeg`, `ChainExec.lean`), the carry disjunct by transparency. This
should be *simpler* than the current argument — no frontier to thread — but it
is a rewrite of the layer, not an edit. `matAvail_placedBy` supplies the set
half; the store half is the existing block reasoning, which never depended on
extremality.

### Step 4 — the must-side extremality uses
The gate swap removes `πᵤ` from the gate but does **not** touch these, which
serve the no-reinsertion obligation:

| lemma | file:line |
|---|---|
| `ue_sub_anti` | `Correctness/Match.lean:247` |
| `pass_antiSucc_sub_anti` | `NoReinsert.lean:184` |
| `carry_in_tauP_multisucc` | `NoReinsert.lean:65` |
| `postp_succ_sub_tauP` | `NoReinsert.lean:~136` |

All four are the **converse of a propagation clause**, i.e. consequences of the
transfer *equation* — which is exactly what `Solver/Closure.lean` derives from
the extremality the solver already proves. Route them through
`MTCSpecBM.closed` (for `πₐ`) and `MeetSpecS.closed` (for `τₚ`) via the
generated `_iff_flow` bridges. This is where that commit earns its keep.

*Note:* three further sites — `tauP_not_used` (`Coverage.lean:89`),
`used_diff_avail_sub_anti` (`Coverage.lean:154`), `used_entry_empty`
(`MatchStep.lean:669`) — are **false from the equation alone**. Their witnesses
are *global* (`πᵤ ∖ postponedPast`, `πᵤ ∩ (πₐ ∪ ηₐ)`), so they are least-fixpoint
inductions, not one-step unfoldings; on a cycle a spurious `πᵤ` can be
self-justifying. They should become unnecessary once the gate no longer reads
`πᵤ` — **verify that rather than assume it.** If any survives, `πᵤ` leastness
has to stay as a residual hypothesis and the goal is not reached.

### Step 5 — drop the hypothesis
Generalize `pipeline_to_asm` to not take `hLcm`, then
`main_compile_correct_with` follows. Update the docstring at
`PipelineToAsm.lean:60-67`, which currently explains why extremality is required.

## 5. Facts worth not rediscovering

- **`Extremal` is destructured at only 12 sites** (10 correctness + 2 optimality
  in `Optimality.lean:57,64`), though 63 signatures thread it.
  `grep -rn "hS\.\(πₐ\|ηₐ\|ηₚ\|τₚ\|πᵤ\|τᵤ\)" --include="*.lean" BaseLanguage/LCM/`
- **Optimality keeps extremality, correctly.** `transform_evalCount_le_safe`,
  `pathLiveLen_le`, `liveRegion_minimal` quantify over competitors; extremality
  *is* their content. Do not try to remove it there.
- **Clause language ⊊ term language.** The generator enforces
  `place ∪ (self ∖ gres)` for a forward-must ghost reading foreign ghosts. A
  legal `MTC` term is not necessarily a legal clause.
- **Ghost references are backward-only** — a ghost may read only previously
  declared ghosts. `ηₘ` is declared seventh for this reason.
- **Confluence is not nameable in a clause.** `∀ n→n'` quantification gives a
  meet with the ghost on the ⊆-left and a join with it on the right, so the
  ⊇ direction of a must recursion cannot be written. This is why maximality
  (and hence fixpoint-ness) is inexpressible, and why `Solver/Closure.lean`
  derives it in Lean instead.
- **`--lcm-analysis=mat` scope: classical mode only.** `nodeGen`/`edgeGen` read
  the unfiltered `τᵤ` where the transform gates on `τᵤK = τᵤ ∩ keep`, so under
  `--lcm=safe` the filter removes insertions and `ηₘ` would over-state
  availability. `mem_matPlace_iff` carries `hkeep : ∀ e, S.keep e = true` for
  this reason. A keep-aware variant needs the mode filter visible to the
  analysis, which it deliberately is not.
- **Power is measured, not assumed.** `examples/lcm-materialized/MatGate.lean`
  shows `classic ⊆ mat` at every node of three programs. Re-run it after Step 2
  to confirm the swap costs nothing.

## 6. Reading order for a new session

1. `examples/lcm-extremality/ExtremalityNeeded.lean` — why extremality is
   currently load-bearing
2. `analyses/lcmmat/LcmMat.gsl` — the spec, header comment first
3. `Seam/lcmmat/Sound.lean` — what is proved, and its scope note
4. `BaseLanguage/LCM/Transform.lean:120-130` — the gate to be replaced
5. `BaseLanguage/LCM/Correctness/Coverage.lean:488-500` — `Cov`, to be rebuilt
