<!-- Copyright (c) 2026 Martin Rinard -->
# Nexis

**A verified optimizing compiler with a prophecy/history-variable analysis generator, in Lean 4.**

Nexis is a machine-checked compiler for a small imperative language — from source text to a
model of AArch64 assembly — together with a *generator* that turns declarative prophecy/history
ghost-variable specifications into verified analyses. The analyses are specified by prophecy and history 
variables specified over the operational semantics; dataflow is a hidden implementation mechanism, generated
behind that abstraction. Everything is developed in Lean 4 with **no external dependencies** (not even
Mathlib); a successful `lake build` means the Lean kernel has checked every theorem.

```
text ─parse─▸ AST ─lower─▸ three-address CFG IR ─optimize─▸ ─codegen─▸ AArch64 model ─print─▸ asm
```

## The three pieces

### 1. The verified compiler (`prophecyc`)

Frontend → three-address CFG IR → normalization → optimization → verified ARM64 code generation.
The development proves, kernel-checked and axiom-clean:

- **Code generation is correct** — the emitted AArch64 model simulates the IR reference semantics.
- **The optimizations preserve behavior** — Lazy Code Motion / Partial Redundancy Elimination and
  Partial Dead-Code Elimination each preserve halting, faulting, and divergence, and are proved
  *optimal* (execution-count and register-pressure).

```sh
echo 'x := 2 + 3 * 4' | lake exe prophecyc      # source on stdin  -> AArch64 asm on stdout
lake exe prophecyc prog.src > prog.s            # or from a file
```

### 2. Analyses and test programs

An analysis is written declaratively as an **extremal prophecy/history ghost-variable
bundle** — never as a hand-rolled solver, and never as a dataflow problem (the dataflow solver is
generated behind the ghost-variable abstraction). The repository ships **29 analyses** under `analyses/`
(available expressions, reaching definitions, very-busy, constant propagation, the LCM and PDCE
bundles that drive the optimizer, backward slices, doubly-clamped demos, …), each a `.gsl` spec plus
its authored node-local definitions.

Runnable programs live under `examples/` (small algorithms with known results, plus larger
scalability programs), with the optimization demos in `examples/opt/` carrying golden before/after
pipeline dumps (lowered IR, optimized IR, and AArch64 asm) under `examples/opt/dumps/`. `lake test` runs
them through both the reference interpreter and the full optimizing pipeline and checks that
observable results agree.

### 3. The generator and the ghost-spec language

`lake exe gen` reads each `.gsl` spec, lowers it to the **Monotone Transfer Calculus** (MTC), and
emits — as **pure text, no reflection, no metaprogramming** — **three** Lean files per analysis:

- `Generated/Solver/<name>/Solve.lean` — the dataflow problem (transfer functions) and the solver invocation;
- `Generated/Seam/<name>/ValidExtremal.lean` — the clause predicates restated over the operational semantics,
  the proofs that the solver result is a *valid* and *extremal* solution, and the ghost bundle the
  transforms consume;
- `Generated/Seam/<name>/Augmented.lean` — the augmented-semantics instance: for each ghost, the per-step
  relation and its **Progress** / **Preservation** / bisimulation theorems (instantiating the generic
  framework in `BaseLanguage/Analysis/Augmented.lean`).

Every analysis lands in one of four verified transfer quadrants (forward/backward × must/may), so a
new spec needs **no new proof**: it is one instantiation of the generic solver-correctness theorem.

The surface language — prophecy and history ghost variables, `predict`/`update`/`check`/`always`
clauses — is defined in **[GHOST-SPEC-LANGUAGE.md](GHOST-SPEC-LANGUAGE.md)** with the frozen grammar
in **[docs/GENERAL-PIPELINE-EBNF.md](docs/GENERAL-PIPELINE-EBNF.md)**.

## Layout

| Path | What |
|------|------|
| `BaseLanguage/` | Frontend, three-address IR + reference semantics, passes, normalization, ARM64 backend, the codegen / LCM / PDCE correctness & optimality proofs, and the augmented-semantics framework (`Analysis/Augmented.lean`) |
| `Solver/` | The MTC term language and the generic verified quadrant solver engine (authored) |
| `Seam/` | The authored per-analysis adapters (`lcm`/`pdce`/…) that bundle the generated instances for the transforms |
| `Generated/` | **All `lake exe gen` output** (do not edit): per-analysis `Solver/<name>/Solve.lean` + `Seam/<name>/{ValidExtremal,Augmented}.lean`, under the `Generated.*` namespace |
| `GenGeneral/` | The generator: total parser → IR → term/well-formedness printers → `Emit` → `Driver` |
| `analyses/` | The 29 shipped ghost specs (`<Name>.gsl` + authored `<Name>Defs.lean`) |
| `examples/` | Runnable test programs (`.src`) |
| `test/`, `stress/` | The runnable suite and the generator regression gates |

## Build, test, run

See **[BUILD.md](BUILD.md)**. In short:

```sh
lake build      # check every proof (cold build: a few minutes; no toolchain setup needed)
lake test       # run the sample programs through interpreter + optimizer and compare
lake exe gen    # regenerate the per-analysis solvers + augmented instances from the .gsl specs
```
