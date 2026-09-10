-- Copyright (c) 2026 Martin Rinard
import Seam.lcm.Adapter
import Generated.Seam.lcmmat.ValidExtremal
import BaseLanguage.Meta.AxiomCheck

/-!
# The materialization-augmented LCM bundle

`analyses/lcmmat/LcmMat.gsl` is `Lcm.gsl` plus a seventh ghost, `Materialized ηₘ` — availability of the
temporary `tₑ` **in the transformed program**. This file assembles the generated solver into the *same*
`LcmSpec` the verified transform already consumes, and exposes `ηₘ` alongside it.

Two things make that assembly free:

* ghosts 1–6 are character-for-character the classical specification, and the node-locals they read are
  re-exported rather than restated, so each generated clause structure is *literally the same proposition*
  as its `LCM` counterpart — the bridges below are field copies; and
* the seventh ghost reads only ghosts 1–6, so it adds no constraint on them. `lcmMatSolved` therefore
  computes exactly the classical bundle, and `lcmMatSolved_toLcm` says so at the level of the ghosts.

**What this is for.** LCM's correctness proof assumes `Extremal S`, and the reason is the replace gate:
`recoverable = πᵤK ∪ insertBefore` can admit a replacement with no matching insertion when `πᵤ` is valid
but too large (`examples/lcm-extremality/ExtremalityNeeded.lean`). Ruling that out needs a *lower* bound on
a *least* fixpoint — irreducibly second-order, expressible by no clause. `matRecoverable` below is the
proposed replacement gate, reading `ηₘ` instead, whose governing clause is an *upper* bound and therefore
follows from validity alone.

**Status.** The bundle, its validity and its extremality are machine-checked. The gate is a definition
only: nothing here yet proves that `ηₘ` under-approximates what the transform actually materializes, which
is the lemma a verified swap would need first. `BaseLanguage/LCM/Transform.lean` still uses the classical
gate, and the compiler still runs the classical transform.
-/

namespace BaseLanguage.Analyses.LcmMat
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis Solver Std

/-! ## Clause bridges — each generated structure is the same proposition as its `LCM` counterpart -/

theorem anti_of {P : Program} {h : Node → Assignments} (x : Anticipated P h) :
    LCM.Anticipated P h := ⟨x.predict, x.check, x.seed, x.within⟩

theorem avail_of {P : Program} {h : Node → Assignments} (x : Available P h) :
    LCM.Available P h := ⟨x.update, x.seed, x.within⟩

theorem postp_of {P : Program} {πₐ ηₐ h : Node → Assignments} (x : Postponable P πₐ ηₐ h) :
    LCM.Postponable P πₐ ηₐ h := ⟨x.update, x.seed, x.within⟩

theorem used_of {P : Program} {latN : Node → Assignments} {latE : Node → Node → Assignments}
    {h : Node → Assignments} (x : Used P latN latE h) :
    LCM.Used P latN latE h := ⟨x.predict, x.check, x.within⟩

/-! ## The bundle -/

/-- The solved bundle, assembled from the `LcmMat` solver into the classical `LcmSpec` the verified
    transform consumes. Ghosts 1–6 are the classical ones; `ηₘ` rides alongside (see `matAvail`). -/
def lcmMatSolved (P : Program) (wf : WellFormed P) : LCM.LcmSpec P :=
  { πₐ  := πₐSol P
    ηₐ  := ηₐSol P
    ηₚ  := ηₚSol P
    τₚ  := τₚSol P
    πᵤ  := πᵤSol P
    τᵤ  := τᵤSol P
    isAnti    := anti_of (πₐSol_valid P wf)
    isAvail   := avail_of (ηₐSol_valid P wf)
    isPostp   := postp_of (ηₚSol_valid P wf)
    isTauP    := τₚSol_valid P wf
    isUsed    := used_of (πᵤSol_valid P wf)
    isUsedOut := τᵤSol_valid P wf }

/-- …and it is extremal, so every existing correctness and optimality theorem applies to it unchanged. -/
theorem lcmMatSolved_extremal (P : Program) (wf : WellFormed P) :
    LCM.Extremal (lcmMatSolved P wf) where
  πₐ  := fun g hg n => πₐ_greatest P wf g ⟨hg.predict, hg.check, hg.seed, hg.within⟩ n
  ηₐ  := fun g hg n => ηₐ_greatest P wf g ⟨hg.update, hg.seed, hg.within⟩ n
  ηₚ  := fun g hg n => ηₚ_greatest P wf g ⟨hg.update, hg.seed, hg.within⟩ n
  τₚ  := τₚ_greatest P wf
  πᵤ  := fun g hg n => πᵤ_least P wf g ⟨hg.predict, hg.check, hg.within⟩ n
  τᵤ  := τᵤ_least P wf

/-! ## The seventh ghost, and the gate it is for -/

/-- Availability of the temporary in the transformed program — the seventh ghost, solved. -/
def matAvail (P : Program) : Node → Assignments := ηₘSol P

/-- Its governing clause holds of the solved value: an **upper** bound, hence a consequence of validity
    rather than of extremality. This is the polarity flip the whole construction is for. -/
theorem matAvail_valid (P : Program) (wf : WellFormed P) :
    Materialized P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P) (matAvail P) :=
  ηₘSol_valid P wf

/-- `ηₘ` is extremal too — which under the proposed gate would be an *optimality* fact, not a
    correctness one. -/
theorem matAvail_greatest (P : Program) (wf : WellFormed P) :
    ∀ g, Materialized P (πₐSol P) (ηₐSol P) (ηₚSol P) (τₚSol P) (τᵤSol P) g →
      ∀ n, (g n).Subset (matAvail P n) :=
  ηₘ_greatest P wf

/-! ## Selecting which analysis the compiler runs

Both bundles are valid, extremal `LcmSpec P`, so the verified transform and every theorem over it accept
either without modification. The selector makes the choice a compiler option; `Seam/compile/CompileCorrect`
proves the end-to-end correctness theorem generically over it, so **both** settings are covered by the
same proof. -/

/-- Which LCM analysis the compiler runs. -/
inductive LcmAnalysis where
  /-- `analyses/lcm/Lcm.gsl` — six ghosts, the shipped default. -/
  | classic
  /-- `analyses/lcmmat/LcmMat.gsl` — the same six plus `Materialized ηₘ`, the availability ghost the
      validity-sufficient replace gate reads (`Seam/lcmmat/Sound.lean`). Ghosts 1–6 are unchanged, so the
      transform's output is identical; what the seventh ghost adds is the extra fact. -/
  | materialized
  deriving DecidableEq, Repr, Inhabited

def LcmAnalysis.ofString? : String → Option LcmAnalysis
  | "classic" | "lcm"       => some .classic
  | "mat" | "materialized"  => some .materialized
  | _                       => none

def LcmAnalysis.name : LcmAnalysis → String
  | .classic      => "classic"
  | .materialized => "materialized"

/-- The bundle a choice supplies. -/
def LcmAnalysis.bundle : LcmAnalysis → (P : Program) → WellFormed P → LCM.LcmSpec P
  | .classic      => LCM.lcmSolved
  | .materialized => lcmMatSolved

/-- **Either choice is extremal**, so every correctness and optimality theorem applies to both. -/
theorem LcmAnalysis.bundle_extremal (a : LcmAnalysis) (P : Program) (wf : WellFormed P) :
    LCM.Extremal (a.bundle P wf) := by
  cases a with
  | classic      => exact LCM.lcmSolved_extremal P wf
  | materialized => exact lcmMatSolved_extremal P wf

#assert_clean_axioms LcmAnalysis.bundle_extremal

#assert_clean_axioms lcmMatSolved
#assert_clean_axioms lcmMatSolved_extremal
#assert_clean_axioms matAvail_valid
#assert_clean_axioms matAvail_greatest

end BaseLanguage.Analyses.LcmMat
