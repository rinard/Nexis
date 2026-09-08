-- Copyright (c) 2026 Martin Rinard
-- Frontend
import BaseLanguage.Frontend.Ast
import BaseLanguage.Frontend.TextToAst
import BaseLanguage.Frontend.AstToText
-- IR + reference semantics
import BaseLanguage.IR.TAC
import BaseLanguage.IR.Cost
import BaseLanguage.IR.LocalsSub
-- Passes
import BaseLanguage.Pass.AstToTac
import BaseLanguage.Pass.Correctness.AstToTacCorrect
import BaseLanguage.Pass.Correctness.PipelineToAsm
import BaseLanguage.Normalize.Sim
-- Backend
import BaseLanguage.Backend.Asm
import BaseLanguage.Backend.TacToAsm
import BaseLanguage.Backend.AsmEnc
import BaseLanguage.Backend.AsmToText
import BaseLanguage.Backend.CodegenEncodable
-- TacToAsm correctness
import BaseLanguage.Backend.Correctness.CodegenCorrect
import BaseLanguage.Backend.Correctness.CodegenBinop
import BaseLanguage.Backend.Correctness.CodegenEmit
import BaseLanguage.Backend.Correctness.CodegenSim
import BaseLanguage.Backend.Correctness.CodegenExpr
import BaseLanguage.Backend.Correctness.Arm64Trichotomy
-- Peephole: verified local expression simplification (constant folding + algebraic identities)
import BaseLanguage.Peephole.Simplify
-- Peephole: the program pass + halt/fault/diverge preservation
import BaseLanguage.Peephole.Pass
-- Normalization: CFG constraints + structural pre-passes (the `WellNormalized` foundation)
import BaseLanguage.Normalize.Normalize
-- The turnkey `normalize ∘ lower` pass: WellNormalized unconditionally over any surface statement
import BaseLanguage.Normalize.FromLower
-- LCM/PRE and PDCE analysis developments: the prophecy/history ghost-bundle adapters and the verified
-- transforms, correctness, and optimality theorems over them.
import analyses.lcm.LcmAdapter
import BaseLanguage.LCM.Transform
import BaseLanguage.LCM.Layout
import BaseLanguage.LCM.Correctness
import BaseLanguage.LCM.Optimality
import BaseLanguage.LCM.LayoutEval
import BaseLanguage.LCM.StepsRun
import BaseLanguage.LCM.NoRecompute
import BaseLanguage.LCM.NoReinsert
import BaseLanguage.LCM.EvalCount
import BaseLanguage.LCM.EvalCountOpt
import BaseLanguage.LCM.EvalCountPlace
import BaseLanguage.LCM.EvalCountHeadline
-- LCM preserves divergence in the fault-free-insertion mode (`transform_preserves_diverges`): the
-- `Diverge → Diverge` cell the classical hoist leaves open, via the same simulation with a syntactic
-- no-fault certificate in place of the halting continuation.
import BaseLanguage.LCM.Divergence
-- Mode selection (`runLcm`): `classic` (KRS, divergence out of scope) vs `preserveDivergence`.
import BaseLanguage.LCM.Mode
-- Basic-variant (isolated-insertion) LCM: halt + fault preservation (`transform_preserves_{halt,faulting}_basic`).
import BaseLanguage.LCM.BasicCorrect
-- The two flat/staged order-theoretic keystone findings (`gs_not_greatest` = thm:no-greatest,
-- `staged_unique` = thm:staged-unique), cited in the paper; standalone, bridges to nothing.
import BaseLanguage.LCM.GhostFindings
import analyses.pdce.PdceAdapter
import BaseLanguage.PDCE.Transform
-- The PDCE behavior-preservation proof (`transform_preserves_halt`) + optimality theorems, so the
-- default `lake build` verifies them (these pull in `PDCE.Layout`/`PDCE.Correctness`).
import BaseLanguage.PDCE.Correctness
-- PDCE preserves divergence (`transform_preserves_diverges`): the `Diverge → Diverge` cell of the
-- §4.5 outcome table, via the non-stuttering block expansion + the generic divergence engine.
import BaseLanguage.PDCE.Divergence
-- PDCE preserves faults in the fault-free-sinking mode (`transform_preserves_faulting`): the cell the
-- classical sinking transform leaves open, since it can push a faulting command past a branch or delete
-- it outright. The mode's bundle comes from `analyses/pdcefault` (the liveness floor widened by one
-- clause) and is selected in `Seam/pdce/Mode.lean`.
import BaseLanguage.PDCE.FaultPreservation
import BaseLanguage.PDCE.Optimality
-- Execution-count optimality (computational capstone): `transform_execCount_le_safe` — along every run the
-- transform evaluates each expression no more often than any safe placement (proved, axiom-clean).
import BaseLanguage.PDCE.ExecCount
-- Two-program execution-count optimality (both compiled programs run, synchronized by original steps)
import BaseLanguage.PDCE.ExecCountTwoProgram
-- Register-pressure optimality of the transformed program (operational live-range realization)
import BaseLanguage.PDCE.OperationalLiveRange
-- Two-program register-pressure optimality (both compiled programs run, synchronized by original steps) —
-- the live-range analogue of `ExecCountTwoProgram` (`transform_regOccOrig_le_any`).
import BaseLanguage.PDCE.LiveRangeTwoProgram
-- Augmented operational semantics + Preservation/Progress (Prophecy/History Variables §2)
import BaseLanguage.Analysis.Augmented
-- Full-behavioral preservation of the optimizer-free skeleton (`codegen ∘ normalize ∘ lower`):
-- outcome predicates + fuel-monotonicity foundation (only *use* the audited semantics).
import BaseLanguage.Behavior.Outcomes
import BaseLanguage.Behavior.LowerBehavior
import BaseLanguage.Behavior.NormalizeBehavior
import BaseLanguage.Behavior.CodegenBehavior
import BaseLanguage.Behavior.PipelineBehavior

/-!
# `BaseLanguage` — the verified language foundation (library root)

Importing this module pulls in the whole library: the frontend (`Frontend.*`), the three-address
CFG IR and its reference semantics (`IR.TAC`), the AST→TAC lowering (`Pass.AstToTac`), the normalization
pre-passes (`Normalize.*`), the ARM64 backend (`Backend.*`), and the codegen-correctness proofs
(`Backend.Correctness.*`) — plus the two verified optimization developments (`LCM.*` and `PDCE.*`:
transform, correctness, optimality, and — for PDCE — divergence, iteration, and execution-count/
register-pressure results), the full-behavioral preservation of the optimizer-free skeleton
(`Behavior.*`), and the augmented-semantics framework (`Analysis.Augmented`).

The core compiler pipeline, end to end:

    text ──TextToAst.parse──▸ Ast.Stmt ──AstToTac.lower──▸ TAC `Program`
         ──TacToAsm.codegen──▸ Asm.Prog ──AsmToText.emitText──▸ AArch64 assembler text
-/
