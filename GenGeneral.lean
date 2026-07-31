-- Copyright (c) 2026 Martin Rinard
import GenGeneral.IR
import GenGeneral.Lex
import GenGeneral.Parser
import GenGeneral.Lower
import GenGeneral.Select
import GenGeneral.Printer
import GenGeneral.Wf
import GenGeneral.Emit
import GenGeneral.Tests

/-!
# `GenGeneral` — the general, term-driven MTC generator pipeline (library root)

A clean-isolation module tree (its own Lake lib): the analysis generator. It builds `MTC` terms and
instantiates the verified backend; it never modifies `BaseLanguage/Analysis/Solver/*`. Driven by
`lake exe gen` (`GenGeneral.Driver`), which emits each analysis's `Solver/<name>/Solve.lean` +
`Seam/<name>/{ValidExtremal,Augmented}.lean` from its `.gsl` spec.

Pipeline: `IR` (the intermediate representation) → `Lex`/`Parser` (surface AST) → `Lower` (`AnalysisIR`) →
`Select` (quadrant/mode) → `Printer`/`Wf`/`Emit` (the emitted Lean strings).
-/
