# Two LCM replace gates, both shipped: **validity** or **extremality**, your choice

The job this document set out is **complete**, and the result is kept as a *choice* rather
than a replacement: the classical gate and the materialization gate are both live, both
proved, and selectable at the CLI.

**The completion predicate, restated and met.** `LCM.transform_preserves_halt_mat` and
`Compile.main_compile_correct` are proved with **no `Extremal` hypothesis anywhere**.
`pipeline_to_asm` takes the LCM obligation itself,

```lean
(hLcm : Analyses.LCM.GateSound … Slcm)
```

rather than a disjunction it resolves internally — deliberately, so that a caller discharging it
one way never depends on the other way's machinery. §6 verifies that by ablation.

All six gates exit 0: `lake build`, `lake test`, `lake exe gengen-check`,
`lake exe gengen-stress`, `bash script/check-seam.sh`, `bash script/check-solver-seam.sh`.
`main_compile_correct{,_with,_demand}` are `#assert_clean_axioms`-gated.

**Check the build with `lake build >/dev/null 2>&1; echo $?`.** Piping to `tail`
and reading `$?` reports the *pipe's* status and gives false greens.

---

## 1. The selector

`LcmSpec.gate : GateMode` (`analyses/lcm/LcmAdapter.lean`) chooses what
`Transform.recoverable` reads:

| `S.gate` | `recoverable n` | correctness needs |
|---|---|---|
| `.demand` | `πᵤK n ∪ insertBefore n` | `Extremal S`, `WellNormalized P`, the `prependEntry` `noop` entry |
| `.materialized` | `ηₘK n ∪ insertBefore n` | `WellNormalized P` |

Like `keep`, `gate` appears in **no validity clause and no extremality clause**, so
`LcmSpec.withGate` re-aims it for free and one bundle carries both gates. `Extremal.withGate`
and `ExtremalMat.withGate` are one-liners for the same reason.

```
prophecyc --lcm-gate=demand|materialized  --lcm-analysis=classic|mat  prog.src
```

Each analysis ships the gate it can afford (`LcmAnalysis.bundleGate`), and `--lcm-gate`
overrides:

* `--lcm-analysis=classic` (default) → `Lcm.gsl`, six ghosts, gate `.demand` — **the compiler
  exactly as it stood before the seventh ghost existed**;
* `--lcm-analysis=mat` → `LcmMat.gsl`, seven ghosts, gate `.materialized`.

Measured, `examples/opt/lcm_full_redundancy.src`, arithmetic ops emitted:

| | `--lcm-gate=demand` | `--lcm-gate=materialized` |
|---|---|---|
| `--lcm-analysis=classic` | **19** | 20 |
| `--lcm-analysis=mat` | **19** | **19** |

The one weak cell is honest and expected: `Lcm.gsl` declares no `ηₘ`, so `lcmSolved` carries
`ηₘ = ∅` — valid, hence a *sound* materialization gate, but not the greatest one, so it
replaces nothing. Every other cell is byte-identical to the pre-change compiler.

## 2. Why the polarity is the whole story

Keeping the `.demand` gate honest means knowing `πᵤ` is *not too large* — a **lower** bound on
a **least** fixpoint. Leastness quantifies over every solution (`∀ g, Used P … g → πᵤ ⊆ g`), so
it is irreducibly second-order and no clause can state it; it must enter the proof as
`Extremal S`. `Materialized`'s clause is an **upper** bound — everything `ηₘ` admits at `n'` was
placed on the way in or survived `n`'s instruction — which *is* the soundness statement, and is
the direction every clause already expresses. So validity suffices.

`examples/lcm-extremality/ExtremalityNeeded.lean` runs one valid, non-extremal bundle `Sbad`
through both gates: `.demand` observes `y = 0` where the source observes `7`; `.materialized`
observes `7`. Nothing about `Sbad` changes between the two runs.

## 3. `GateSound` — one obligation, two prices

The correctness development consumes the gate through exactly one predicate
(`Correctness/Coverage.lean`), which is what lets **one** proof carry **both** gates — the same
factoring `match_step_core` already uses for its two no-fault obligations, and `Divergence.lean`
for `SafeInserts`.

```lean
structure GateSound (P : Program) (S : LcmSpec P) : Prop where
  entry : ∀ e, e ∉ covSet S P.entry
  step  : ∀ c c', Step P c c' → ∀ e ∈ covSet S c'.node, …
  read  : … → e ∈ recoverable P S nd → e ∈ covSet S nd ∨ e ∈ insertBefore P S nd
```

with `covSet` the gate's own coverage set (`demandSet` / `ηₘK`). What each field costs:

| field | `.materialized` | `.demand` |
|---|---|---|
| `entry` | `isMat.seed` (`ηₘ(entry) ⊆ entrySeed = ∅`) | `used_entry_empty` — a leastness witness (`Extremal`, `wn`, entry `noop`) |
| `step` | one `mem_union` split of `isMatK.update` | `demand_step_edge` — `used_decomp`, `killed_in_insertAfter`, `latestOut_used_succ_sub_insertEdge` |
| `read` | `mem_union` on the gate itself | a `NoSelfRead` argument ruling out "materialized by this node's *exit* chain" |

`gateSound_materialized` takes `(S) (hm : S.gate = .materialized)` and nothing else.
`gateSound_demand` takes `(hd) (hS : Extremal S) (wn) (hen)`.

The `read` asymmetry is the sharpest bit: `ηₘ` is indexed at block *entry*, so "materialized too
late to read" is not even expressible under `.materialized`.

## 3a. The full outcome table, per gate

The base language has exactly three outcomes (halt, fault, diverge). Each is proved for both gates, and
every `_mat` form is the `_demand` form minus `Extremal S` and minus the `prependEntry` `noop` entry:

| outcome | `.materialized` (validity) | `.demand` (extremality) | file |
|---|---|---|---|
| halt | `transform_preserves_halt_mat` | `transform_preserves_halt_demand` | `Correctness/MatchStep.lean` |
| fault | `transform_preserves_faulting_mat` | `transform_preserves_faulting_demand` | `Correctness/FaultPreservation.lean` |
| diverge | `transform_preserves_diverges_mat` | `transform_preserves_diverges_demand` | `Divergence.lean` |
| diverge, side-condition-free | `transform_preserves_diverges_faultFree_mat` | `…_faultFree_demand` | `Divergence.lean` |
| all three, mode-level | `runLcm_safe_preserves_all_mat` | `runLcm_safe_preserves_all_demand` | `Mode.lean` |
| end-to-end | `main_compile_correct` | `main_compile_correct_demand` | `Seam/compile/CompileCorrect.lean` |

Each pair goes through the *same* generic theorem, differing only in which `GateSound` discharge it
supplies. `runLcm_safe_preserves_all_{mat,demand}` is the sharpest single comparison: the same three
conclusions about the same transform, one of them needing two fewer hypotheses.

## 4. The two design decisions

**(a) `isMat` is stated over the unfiltered `τᵤ`; the gate reads a filtered `ηₘK`.**
`keep` (the `--lcm=safe` hoisting filter) appears in no clause of any ghost — that is what makes
`withKeep` free and one development cover both modes. But the transform places only what survives
the filter, so a gate reading the *unfiltered* `ηₘ` would over-state availability under
`--lcm=safe` (the scope note the original plan recorded as blocking). `LcmSpec.isMatK` resolves
it: filtering the ghost by `keep` re-establishes the very same clause over `τᵤK`, because `keep`
simply travels along each disjunct — `matPlace` gates on `τᵤ` by intersection, and the carry
`∖ notPass` does not touch `keep`. So `--lcm=safe` emits byte-identical assembly under either gate.

**(b) `ExtremalMat` is a *separate* predicate from `Extremal`.**
Greatest-ness of `ηₘ` is read by **no** correctness proof, under either gate. It is read by
`demand_materialized`, which shows the `.materialized` gate admits everything `.demand` did —
an *optimality* fact. Folding it into `Extremal` would have cost `LCM.lcmSolved` its extremality
(a six-ghost bundle has no `ηₘ` to be greatest), and with it the `.demand` gate's correctness
proof — which is exactly the artifact this document is about preserving. Keeping them apart costs
nothing: `Extremal` is still the six classical clauses, `lcmSolved_extremal` still holds, and
`ExtremalMat` is discharged only by `lcmMatSolved`.

## 5. Where extremality still lives, correctly

Optimality quantifies over competing placements; extremality *is* its content. Two predicates
carry it into a gate-generic development:

* `GateComplete S : ∀ n, demandSet S n ⊆ covSet S n` — the chosen gate is no weaker than the
  classical demand set. `.demand` satisfies it definitionally (`gateComplete_demand`);
  `.materialized` by `gateComplete_materialized`, from `Extremal` + `ExtremalMat` + `wn` + `hen`.
* `demand_materialized : demandSet S n ⊆ S.ηₘ n` — proved by greatest-ness of `ηₘ`: `demandSet`
  is **itself** a valid `Materialized`, its `update` obligation being exactly `demand_step_edge`
  read at `M := demandSet S c.node` where the hypothesis is reflexivity, and its `seed`
  obligation `used_entry_empty`.

`keptUse_latestNode` (a kept numbered control sits on the latest frontier) is stated over
`GateComplete`, so the whole eval-count chain — `cE_imp_postp`, `cE_le_pl`,
`cE_imp_postp_earliest`, `cEb_imp_postp_earliest`, `cEb_notPostp_imp_insertEdge`,
`cE_notPostp_imp_insertAfter`, `cE_count_le_cross` — and the `BasicCov`/`BasicCorrect` chain run
unchanged under either gate.

**Step 4 of the original plan turned out to be unnecessary.** It proposed routing `ue_sub_anti`,
`pass_antiSucc_sub_anti`, `carry_in_tauP_multisucc` and `postp_succ_sub_tauP` through
`Solver/Closure.lean` to serve the no-reinsertion obligation. `NoReinsert.lean` is imported only
by `EvalCountOpt.lean` — the optimality development — so none of the four is in the correctness
chain under either gate, and optimality keeps extremality by design. Likewise `tauP_not_used`,
`used_diff_avail_sub_anti` and `used_entry_empty` survive, on the optimality and `.demand` paths.
Lean settles this: `transform_preserves_halt_mat` typechecks with no `Extremal` in scope.

## 6. What was measured

* **Assembly is unchanged.** `examples/opt/*.src` + `examples/computations/*.src` (29 programs),
  pre-change compiler vs: (i) the new default (`classic`/`.demand`), (ii) `--lcm-analysis=mat`
  (`.materialized`), (iii) `--lcm=safe --pdce=safe --lcm-analysis=mat` — all byte-identical.
  `examples/opt/dumps/` regenerates with no diff.
* **The gates agree on an extremal bundle.** `examples/lcm-materialized/MatGate.lean` runs the
  same bundle through `withGate .demand` and `withGate .materialized` and reports
  `demand ⊆ materialized` at every node of three programs, strictly larger at some — the
  measurement behind `demand_materialized`.
* **The counterexample bites exactly one gate.** `examples/lcm-extremality/ExtremalityNeeded.lean`,
  above.
* **The two end-to-end proofs are genuinely disjoint** — established by ablation, since Lean
  discards imported theorem bodies and a dependency walk cannot see proof terms. Replace a lemma's
  proof with `sorry`, rebuild, and read which `#assert_clean_axioms` fails:

  | ablated | `main_compile_correct` | `main_compile_correct_demand` | `..._with` |
  |---|---|---|---|
  | `gateSound_demand` | **survives** | breaks | breaks |
  | `gateSound_materialized` | breaks | **survives** | breaks |
  | `used_decomp` + `used_entry_empty` (πᵤ leastness) | **survives** | breaks | breaks |

  The third row is the result in one line: the shipped default's end-to-end correctness proof does
  not touch `πᵤ` leastness at all. `..._with` is generic over both gates, so it legitimately
  depends on both discharges — which is why the two specific theorems are proved *directly* from
  `pipeline_to_asm` rather than routed through it.

## 7. Facts worth not rediscovering

- **`matPlace` at `τᵤK` is `insertEdge ∪ (insertBefore ∩ pass)` by `rfl`.** `edgeGen`/`nodeGen`
  with `S.τᵤK` supplied are literally `Transform.insertEdge`/`insertBefore`, and
  `latestOutG P S.πₐ S.ηₐ S.ηₚ = latestOut P S`. This is why `gateSound_materialized.step` needs
  no bridging lemma and no `hkeep` side condition — unlike `Seam/lcmmat/Sound.lean`'s
  `mem_matPlace_iff`, which is stated over the unfiltered ghosts and carries one.
- **The phase split is load-bearing.** `insertBefore` runs at block entry, *before* the node's
  instruction, so it reaches the successor only through `pass`; `insertEdge` runs after it, so it
  reaches unconditionally. Getting that backwards makes `ηₘ` claim availability for a temp the
  next instruction invalidates.
- **The seed forces `hen` into `demand_materialized`.** `Materialized.seed` is `g(entry) ⊆ ∅`, so
  any set exhibited as a valid `Materialized` must be empty at the entry — for `demandSet` that is
  `πᵤ(entry) = ∅`, i.e. `used_entry_empty`, i.e. the `prependEntry` `noop`. Gating the entry with
  an `if` just moves the obligation to the step *out of* the entry.
- **`mkBasic` widens `τᵤ` to `allExprs`, and `ηₘ` rides along unchanged.** `matPlace` is monotone
  in `τᵤ` (both generators intersect with it) and the clause is an upper bound, so a wider `τᵤ`
  only grows the right-hand side. `mkBasic` also preserves `gate`.
- **`examples/scale/*.src` hang the CLI**, on the pre-change binary too. They are exercised by
  `lake test`, not by `prophecyc` directly; do not read that as a regression.
- **Clause language ⊊ term language**, **ghost references are backward-only**, and **confluence is
  not nameable in a clause** — all still true, all still the reasons `LcmMat.gsl` looks the way it
  does.

## 8. The prime directive was not bent

No dataflow fixpoint solver was written. `ηₘ` is a ghost, solved by the existing generic solver
from the existing `.gsl` clause. `Written`/`PlacedBy` in `Seam/lcmmat/Sound.lean` are inductive
relations over `Step`, not analyses. `demandSet` and `covSet` are projections of the bundle.
`check-seam.sh` and `check-solver-seam.sh` both pass.
