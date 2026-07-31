<!-- Copyright (c) 2026 Martin Rinard -->
# Example programs

Source programs (`.src`, in the language of the top-level `README.md`: statements separated by `;`,
`x := e` assignment, `//` line comments) grouped by purpose:

| directory | what | checked by |
|---|---|---|
| [`opt/`](opt/) | small demos that exercise the two verified optimizations — **LCM** (lazy code motion / partial-redundancy elimination) and **PDCE** (partial dead-code elimination) | `run.sh` / golden [`opt/dumps/`](opt/dumps) |
| [`scale/`](scale/) | large synthetic programs (hundreds of nodes) for optimizer scalability | `lake test` |
| [`computations/`](computations/) | algorithms — gcd, factorial, Fibonacci, fast power, prime counting, Collatz, integer sqrt, sum-of-squares, sum-of-divisors (loops, nested loops, branches, bitwise) | `lake test` (correctness + behaviour preservation) |

Everything is runnable directly, e.g. `prophecyc examples/computations/primes.src` or
`prophecyc --show-opt examples/opt/lcm_full_redundancy.src`.

## Running (the `opt/` corpus)

```sh
examples/run.sh              # compile each, count asm arithmetic ops, run, print a table
examples/run.sh --show-opt   # same, plus the before/after IR dump for each program
```

`run.sh` counts real arithmetic instructions (`add`/`sub`/`mul`/`cmp` on `x9`) in the emitted
assembly — a proxy for what the optimizer removed — then assembles, links, and runs each program and
prints its `name=value` output. To inspect a single program's IR before and after each pass:

```sh
prophecyc --show-opt examples/opt/lcm_full_redundancy.src
```

### Cleanup pass (default; `--no-clean` to disable)

`prophecyc` runs a late **noop-elimination + index-compaction** pass ([BaseLanguage/Pass/Cleanup.lean](../BaseLanguage/Pass/Cleanup.lean))
before codegen **by default**: it drops bypassable `noop` nodes, renumbers the survivors, and rewrites
edges (preserving `noop` cycles, so divergence is kept). Because the backend emits one fixed block per
node, this shrinks the assembly ~30–40%. `--no-clean` skips it; `--show-opt` shows the result as its
final "AFTER CLEANUP" stage.

Status: **fully verified** ([BaseLanguage/Pass/CleanupCorrect.lean](../BaseLanguage/Pass/CleanupCorrect.lean), axiom-clean) —
`cleanup_wellFormed` plus full behavioral preservation (`cleanup_preserves_halt` / `_faults` / `_diverges`)
and `cleanup_codegen` (end-to-end). It is **spliced into `pipeline_to_asm`** (step ④.5), so the verified
end-to-end theorem now describes the actual emitted (cleaned) output. Also empirically validated: every
program here produces byte-identical runtime output with and without `--no-clean`.

### Pre-generated dumps (`examples/opt/dumps/`)

`examples/dump.sh` writes `examples/opt/dumps/<name>.txt` for every program — three views each:
`[1/3]` the IR before optimization, `[2/3]` the IR after LCM + PDCE (what codegen actually consumes),
and `[3/3]` the generated AArch64 assembly. Regenerate with `examples/dump.sh`.

## What each test targets

Inputs default to 0, so `a`, `b`, … print as `0` unless assigned; the point is the **op count**
(optimization fired) and that the result is unchanged (semantics preserved).

### LCM — redundant computations collapse to one

Verify with `prophecyc --show-opt <file>`: the redundant `x := a+b` sites become copies `x := t0`
of a single earlier compute, and on branches LCM *inserts* the compute on the path that lacked it.

| file | source shape | expected effect |
|---|---|---|
| `lcm_full_redundancy` | `y=a+b; z=a+b` | 2 adds → **1** (compute once into `t0`, reuse) |
| `lcm_triple_redundancy` | `x=y=z=a+b` | 3 adds → **1** |
| `lcm_mul_redundancy` | `p=a*b; q=a*b` | 2 muls → **1** |
| `lcm_cse_subexpr` | `x=a+b; y=a+b+c` | the `a+b` *sub*-expression of `a+b+c` shares the standalone `a+b` → computed **once** |
| `lcm_cse_across_code` | `y=a+b; p=c*d; q=c+d; z=a+b` | redundant `a+b` eliminated **across intervening unrelated code** (the `c*d`/`c+d` in between don't block it) |
| `lcm_partial_redundancy` | `if c {y=a+b} else {skip}; z=a+b` | insert `a+b` on the else edge, merge reuses → each path computes it **once** (was twice on the then-path) |
| `lcm_both_branches` | `if c {y=a+b} else {z=a+b}; w=a+b` | both arms feed `t0`; the merge `w=a+b` becomes free → 3 computes → **2** |
| `lcm_loop_redundancy` | `while … { x=a+b; y=a+b; … }` | redundant body compute eliminated → `a+b` **once** per iteration |
| `lcm_loop_hoist` | `while i<5 { x=a+b; … }; z=a+b` | `a+b` also used after the loop ⇒ down-safe at the header ⇒ **hoisted to the pre-header** (single compute, both uses become copies) |

**Non-speculative (down-safety) — whether a loop computation moves out depends on the exit path.**
LCM only places a computation where it is *down-safe* (evaluated on every forward path from that point).
A `while` header has two successors — the body and the loop exit — so a body computation is hoistable
out of the loop **iff it is also computed on the exit path**:

* `lcm_loop_hoist` — `a+b` is used *after* the loop too, so both header successors compute it ⇒ it is
  hoisted to the pre-header (`--show-opt` shows `t := a+b` before the loop test; the in-loop use is a copy).
* `lcm_manual_peel` — `x=a+b; while … { x=a+b; … }`: computing `a+b` once *before* the loop makes it
  **available** around the back-edge, so the in-loop recompute is fully redundant and eliminated. This is
  the shape a first-iteration peeler (or a `do/while`) would produce — LCM then removes the recomputation
  with no change to the optimizer. Result `x=7 i=5`.
* `lcm_loop_invariant` / `lcm_loop_invariant_mul` — the invariant is used *only* inside the loop, so the
  zero-trip / exit path leaves without it ⇒ **not** down-safe at the pre-header ⇒ safe PRE must **not**
  hoist it (a speculative LICM would). Kept as correctness + scope tests; `--show-opt` shows before == after-LCM.

| file | source shape | expected effect |
|---|---|---|
| `lcm_loop_invariant` | `while i<10 { t=a+b; i=i+t }` | `a+b` **not** hoisted (not down-safe at pre-header); loop result `i=16 t=8` |
| `lcm_loop_invariant_mul` | `while i<n { s=s+k*n; i=i+1 }` | invariant `k*n` **not** hoisted; result `s=48` |

### PDCE — dead computations vanish; partially-dead ones sink

| file | source shape | expected effect |
|---|---|---|
| `pdce_fully_dead` | `x=a*b; x=7; y=x+1` | `a*b` overwritten before use → **0** muls |
| `pdce_dead_overwrite` | `r=a*b; r=5; s=r+1` | **0** muls |
| `pdce_dead_sub` | `d=a-b; d=9; e=d` | **0** subs |
| `pdce_dead_after_branch` | `x=a*b; if c {…} else {…}; x=0; w=x` | `a*b` dead (later `x=0`) → **0** muls |
| `pdce_partial_dead_sink` | `x=a*b; if c {y=x} else {x=0}` | `a*b` dead on the else path → sunk into the then-branch only (**1** mul, after the branch) |

### Combined / correctness

| file | purpose |
|---|---|
| `combo_pre_and_dce` | PRE (`a+b` shared) **and** DCE (`a*b` dead) in one program → 2 adds, 0 muls |
| `misc_operators` | all operators (`+ - * << >> ~ &`) with seeded inputs → checks the emitted arithmetic (`r=11 s=44 t=22 u=9`) |
| `misc_control_flow` | nested `while`/`if` → checks control flow (`sum=23 i=5`) |
