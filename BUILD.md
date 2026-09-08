<!-- Copyright (c) 2026 Martin Rinard -->
# Building and evaluating

## Requirements

- [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager. The exact
  Lean version is pinned in `lean-toolchain` and is installed automatically on the first
  build — no manual toolchain setup.
- **No other dependencies.** This is a self-contained Lean 4 project with no external
  libraries (not even Mathlib); `lake-manifest.json` lists no packages.
- Checking the proofs works on any platform Lean supports (macOS / Linux). The compiler
  *emits* AArch64 assembly, so assembling and running that output additionally needs an
  AArch64 host with a C toolchain (`clang`) — but that is **not** required to verify the
  development.

## Build — checks every proof

```sh
lake build
```

Compiles the whole verified library, the `prophecyc` CLI, and the generated verified
prophecy/history-variable analyses. A successful build means the Lean kernel has checked every theorem
in the development. A cold build takes a few minutes on a modern laptop.

## Test

```sh
lake test
```

Parses, lowers, and runs a suite of sample programs through both the reference
interpreter and the full optimizing pipeline, checking that observable results agree.

## Run the compiler

```sh
echo 'x := 2 + 3 * 4' | lake exe prophecyc      # source on stdin  -> AArch64 asm on stdout
lake exe prophecyc prog.src > prog.s            # or from a file
```

## Examples

Sample programs live under `examples/`:

- `examples/computations/` — small algorithms (gcd, factorial, primes, …), each with a
  known result; `examples/scale/` — larger stress programs. These are exactly the
  programs `lake test` exercises.
- `examples/opt/dumps/<name>.txt` — for every optimization demo in `examples/opt/`, one golden file
  with three sections: `[1/3]` the lowered (normalized) three-address IR before optimization,
  `[2/3]` the IR after LCM + PDCE + the verified cleanup pass (fed to codegen), and `[3/3]` the
  emitted AArch64 assembly.

Regenerate a single stage for any program with the CLI:

```sh
lake exe prophecyc --emit-lowered examples/computations/gcd.src   # lowered IR
lake exe prophecyc --emit-opt     examples/computations/gcd.src   # optimized IR (fed to codegen)
lake exe prophecyc                examples/computations/gcd.src   # assembly
lake exe prophecyc --show-opt     examples/computations/gcd.src   # every stage at once
```

## Optimization modes (`--lcm=`, `--pdce=`)

Both structural optimizations ship in two verified modes. The defaults are the classical KRS transforms;
the `safe` modes trade some optimization strength for a stronger behavioral guarantee.

```sh
lake exe prophecyc --lcm=safe  --emit-opt prog.src   # LCM that preserves divergence
lake exe prophecyc --pdce=safe --emit-opt prog.src   # PDCE that preserves faults
```

| flag | modes | default |
|---|---|---|
| `--lcm=` | `classic` (= `krs`) · `safe` (= `preserve-divergence`) | `classic` |
| `--pdce=` | `classic` (= `krs`) · `safe` (= `preserve-faults`) | `classic` |

What each mode is proved to preserve:

| | halting runs | faults | divergence |
|---|---|---|---|
| `--lcm=classic` | ✅ `LCM.transform_preserves_halt` | ✅ `LCM.transform_preserves_faulting` | ✗ (see below) |
| `--lcm=safe` | ✅ `LCM.runLcm_preserves_halt` | ✅ | ✅ `LCM.runLcm_preserves_diverges` |
| `--pdce=classic` | ✅ `PDCE.transform_preserves_halt` | ✗ (see below) | ✅ `PDCE.transform_preserves_diverges` |
| `--pdce=safe` | ✅ `PDCE.runPdce_preserves_halt` | ✅ `PDCE.runPdce_preserves_faulting` | ✅ |

The two gaps in the classical modes are duals, and both are real rather than proof artifacts:

* **LCM can turn divergence into a fault** by hoisting a `div`/`mod` to a point the source never reaches.
  `examples/lcm-divergence/DivergenceGap.lean` is an executable witness on a program that satisfies every
  hypothesis LCM's correctness theorem assumes. `--lcm=safe` hoists only `Expr.faultFree` expressions
  (`LcmSpec.keep`), leaving a `div`/`mod` where the source computes it and hoisting everything else
  exactly as before — per expression, not per program.
* **PDCE can turn a fault into a halt** by sinking a faulting assignment past a branch, or deleting it
  when its result is dead. `--pdce=safe` does neither. It needs a *different liveness analysis*
  (`analyses/pdcefault/PdceFault.gsl`): the classical specification with its liveness floor widened from
  `condVars` to `condVars ∪ faultingRhsVars`, because a computation that can fault is observable and its
  operands must stay live even when its result is dead. That is the only difference between the two
  `.gsl` files.

Optimality is stated relative to the mode: the theorems compare against placements over the same filter
(`S.keep`), since a competitor with a different filter is a different transform, not a different analysis.

## Regenerate the verified analyses (optional)

```sh
lake exe gen
```

Reads the declarative analysis specifications (`analyses/<name>/<Name>.gsl` plus the
authored node-local definitions) and emits, for each analysis, the dataflow solver
(`Generated/Solver/<name>/Solve.lean`), the valid/extremal seam instances
(`Generated/Seam/<name>/ValidExtremal.lean`), and the augmented-semantics instances
(`Generated/Seam/<name>/Augmented.lean`). The checked-in generated files are exactly this output;
regenerating produces byte-identical files.

## What is verified

- **End-to-end.** A single forward-simulation theorem (`pipeline_to_asm`) relates the
  whole pipeline — `normalize ∘ lower`, the LCM and PDCE optimizations, cleanup, and
  instruction selection — to a reference operational semantics on observable behavior.
- **The analyses.** Each generated solver is proved to compute the extremal
  (greatest / least) solution of its declarative prophecy/history-variable specification (`solve_correct`,
  `sorry`-free under a well-formedness precondition that normalization establishes
  unconditionally).
- **The optimizations.** Behavior preservation and optimality of the LCM and PDCE
  transforms, over an arbitrary valid extremal analysis result.
- **Instruction selection** into an operational model of an AArch64 subset
  (`codegen_simulates`).
- **Assembler encoding** (`AsmEnc`): the emitter that turns modelled instructions into
  assembler lines is proved to produce only *encodable* lines — no load/store offset ever
  exceeds the immediate ceiling (`emitCmd_wf`, `codegen_emits_wf`; large slots are legalized
  to a register-offset form) — and its encoding is faithful (`decode_emitCmd` round-trips).
- **The generic solver engine** (`Solver/`): a Kildall worklist
  proved valid, extremal, and terminating for each direction × extremality shape.

All proofs depend only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); there are no `sorry`s and no project-specific axioms.

**Trusted computing base** (assumed, not proved): the parser (text → AST), the reference
semantics that behavior preservation is stated against, the AArch64 machine model, and — in
the printer — the trivial 1:1 `renderLine` (structured line → text), the frame/ABI scaffolding
(`_printf`/`ret`/`_abort`, external calls that every verified compiler axiomatizes), and the
real-hardware *semantics* of the (proved-encodable) instructions. The instruction *encoding*
itself is now verified (`AsmEnc`), not trusted.

## Layout

```
BaseLanguage.lean, BaseLanguage/   the verified library — frontend, IR, passes,
                                   backend + codegen correctness, LCM/PDCE, and the
                                   augmented-semantics framework
Solver.lean, Solver/               the MTC term language + generic verified solver engine
GenGeneral.lean, GenGeneral/       the analysis generator (`lake exe gen`)
Generated/                         all generated output (Solve / ValidExtremal / Augmented)
Seam/, analyses/                   authored adapters + the `.gsl` specs and node-locals
Main.lean                          the prophecyc CLI
test/Tests.lean                    the test suite
```
