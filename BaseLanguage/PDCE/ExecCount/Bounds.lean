-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.ExecCount.Core

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std
set_option linter.unusedVariables false

/-! ## Lemma A anchored to the run — `#mat ≤ #born` over the source run

The run-induction that carries the counting core (`LemmaA`) onto the real run. `matCount` = the source-run
materialization count of `a` (node materialization `matNode` at the visited node + edge materialization
`matEdge` on the taken edge); `bornRun` = the count of `a`'s site executions. The invariant
`matCount c fuel ≤ bornRun c fuel + [a ∈ S.ηK c.node]` (the `+[sink]` slack = the one currently-open stretch)
is maintained by a **per-step** inequality proved from three atoms — the abstract bundle's `isSink.update`
(sink entry only via `born` or delayed-with-`pass`) and the `matNode`/`matEdge` membership facts. At the
entry `sink = ∅`, so it collapses to `#mat ≤ #born`. `matCount`/`bornRun` are filters over
`step1` (like `execCount`), and everything else is a projection of the abstract `S` + syntactic node-locals.

The live-gated form below (`#mat ≤ #live-born = liveBornCount`, `mat ⇒ live`) and
the fold (`execCount(transform) = matCount`) build on this. -/

/-- Source-run materialization count of `a`: `matNode` at each visited node + `matEdge` on each taken edge. -/
def matCount (P : Program) (S : PdceSpec P) (a : Asgn) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      (if a ∈ matNode P S c.node then 1 else 0)
        + (match step1 P c with
           | .next c' => (if a ∈ matEdge P S c.node c'.node then 1 else 0) + matCount P S a c' fuel
           | _        => 0)

/-- Source-run count of `a`'s site executions (`a ∈ born P n`). -/
def bornRun (P : Program) (a : Asgn) : Config → Nat → Nat
  | _, 0      => 0
  | c, fuel+1 =>
      (if a ∈ born P c.node then 1 else 0)
        + (match step1 P c with | .next c' => bornRun P a c' fuel | _ => 0)

/-- `matCount` one-step unfolding on a real step (exposes the sum for arithmetic). -/
theorem matCount_next {P : Program} {S : PdceSpec P} {a : Asgn} {c c' : Config} {f : Nat}
    (hs : step1 P c = .next c') :
    matCount P S a c (f + 1) = (if a ∈ matNode P S c.node then 1 else 0)
      + ((if a ∈ matEdge P S c.node c'.node then 1 else 0) + matCount P S a c' f) := by
  show (if a ∈ matNode P S c.node then 1 else 0)
     + (match step1 P c with
        | .next c'' => (if a ∈ matEdge P S c.node c''.node then 1 else 0) + matCount P S a c'' f
        | _ => 0) = _
  rw [hs]

/-- `bornRun` one-step unfolding on a real step. -/
theorem bornRun_next {P : Program} {a : Asgn} {c c' : Config} {f : Nat} (hs : step1 P c = .next c') :
    bornRun P a c (f + 1) = (if a ∈ born P c.node then 1 else 0) + bornRun P a c' f := by
  show (if a ∈ born P c.node then 1 else 0)
     + (match step1 P c with | .next c'' => bornRun P a c'' f | _ => 0) = _
  rw [hs]

/-- **The invariant**: `#mat ≤ #born + [in-flight]`. The `+[a ∈ sink]` slack is the single currently-open
    stretch that may still materialize once using no further `born`. -/
theorem matCount_le_bornRun_aux {P : Program} (S : PdceSpec P) (a : Asgn) : ∀ (fuel : Nat) (c : Config),
    matCount P S a c fuel ≤ bornRun P a c fuel + (if a ∈ S.ηK c.node then 1 else 0) := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [matCount, bornRun]
  | succ f ih =>
    intro c
    cases hs : step1 P c with
    | next c' =>
      have hStep : Step P c c' := step1_next_iff.mp hs
      have hupd := S.isSink.update c c' hStep
      have IH := ih c'
      -- non-halt at `c.node` (it steps), so `blockedSet = allAsgns ∖ pass`
      have hnh : P.fetch c.node ≠ some .halt := by
        intro hh
        have hhalt : step1 P c = .halt := by unfold step1; rw [hh]
        rw [hhalt] at hs; simp at hs
      have hbeq : blockedSet P c.node = Assignments.sdiff (allAsgns P) (pass P c.node) := by
        unfold blockedSet
        cases hf : P.fetch c.node with
        | none => rfl
        | some i => cases i with
          | halt => exact absurd hf hnh
          | assign x e nx => rfl
          | ifz x z nz => rfl
          | noop nx => rfl
      -- per-step inequality `(*)`
      have hMNsink : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      have hMNpass : a ∈ matNode P S c.node → a ∉ pass P c.node := by
        intro h; have hb := (mem_matNode.mp h).2.1; rw [hbeq] at hb; exact (Assignments.mem_sdiff.mp hb).2
      have hMEdrop : a ∈ matEdge P S c.node c'.node → a ∉ S.ηK c'.node := fun h => (mem_matEdge.mp h).2.1
      have hMEde : a ∈ matEdge P S c.node c'.node →
          a ∈ born P c.node ∨ (a ∈ S.ηK c.node ∧ a ∈ pass P c.node) :=
        fun h => mem_delayedExit.mp (mem_matEdge.mp h).1
      have hUp : a ∈ S.ηK c'.node → a ∈ born P c.node ∨ (a ∈ S.ηK c.node ∧ a ∈ pass P c.node) := by
        intro h
        have hk := (mem_ηK.mp h).2
        have hm := hupd a (ηK_sub S _ a h)
        rw [Assignments.mem_union, Assignments.mem_inter] at hm
        exact hm.imp id (fun hh => ⟨mem_ηK.mpr ⟨hh.1, hk⟩, hh.2⟩)
      have key : (if a ∈ matNode P S c.node then 1 else 0)
          + ((if a ∈ matEdge P S c.node c'.node then 1 else 0) + (if a ∈ S.ηK c'.node then (1:Nat) else 0))
          ≤ (if a ∈ born P c.node then 1 else 0) + (if a ∈ S.ηK c.node then 1 else 0) := by
        by_cases hmn : a ∈ matNode P S c.node <;>
        by_cases hme : a ∈ matEdge P S c.node c'.node <;>
        by_cases hsk' : a ∈ S.ηK c'.node <;>
        by_cases hbo : a ∈ born P c.node <;>
        by_cases hsk : a ∈ S.ηK c.node <;>
        by_cases hpa : a ∈ pass P c.node <;>
          simp_all <;> omega
      rw [matCount_next hs, bornRun_next hs]
      omega
    | halt =>
      have IH : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      simp only [matCount, bornRun, hs]
      by_cases hmn : a ∈ matNode P S c.node <;> by_cases hsk : a ∈ S.ηK c.node <;>
        simp_all <;> omega
    | fault =>
      have IH : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      simp only [matCount, bornRun, hs]
      by_cases hmn : a ∈ matNode P S c.node <;> by_cases hsk : a ∈ S.ηK c.node <;>
        simp_all <;> omega
    | stuck =>
      have IH : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      simp only [matCount, bornRun, hs]
      by_cases hmn : a ∈ matNode P S c.node <;> by_cases hsk : a ∈ S.ηK c.node <;>
        simp_all <;> omega

/-- **Lemma A anchored: `#mat ≤ #born` over the source run** (from the entry, where `sink = ∅`). The "≤1
    materialization per born-crossing" fact, on the real run. -/
theorem matCount_le_bornRun {P : Program} (S : PdceSpec P) (a : Asgn) (σ : Store) (fuel : Nat) :
    matCount P S a ⟨P.entry, σ⟩ fuel ≤ bornRun P a ⟨P.entry, σ⟩ fuel := by
  have h := matCount_le_bornRun_aux S a fuel ⟨P.entry, σ⟩
  have hentry : a ∉ S.ηK P.entry := by
    intro hmem; have := S.isSink.seed a (ηK_sub S _ a hmem)
    simp [sinkSeed, Assignments.empty] at this
  simpa [hentry] using h

/-! ## Lemma A (live-gated) — `#mat ≤ #(live born-crossing)` over the source run

Strengthens `matCount_le_bornRun` by gating the born count on liveness-on-exit — closing Lemma A on the
placement-invariant unit. The mechanism:
* `mat ⇒ a.lhs ∈ S.π` at the mat node (`matNode_necessary`/`matEdge_necessary`, `Optimality.lean:236/240`);
* a candidate still in flight **passes** every node strictly before its exit (`a ∈ pass ⇒ a.lhs ∉ defVars`,
  `pass_notMem_defVars`), so `Live.predict` (`live c' ⊆ live c ∪ defVars c`) carries
  `a.lhs ∈ S.π` **backward** across the boundary (`pass_live_carry`).
The invariant gates BOTH the count and the `+[sink]` slack by liveness; the per-step inequality closes by the
same six structural atoms as the ungated bound plus these three liveness atoms. -/

/-- A candidate delayable past `n` does not redefine its own lhs (`pass = ¬kills`, and `kills` fires on the
    lhs-redef disjunct `defV == some a.lhs`). -/
theorem pass_notMem_defVars {P : Program} {n : Node} {a : Asgn} (hpa : a ∈ pass P n) :
    a.lhs ∉ defVars P n := by
  have hk : kills P n a = false := by
    unfold pass at hpa
    rw [Assignments.mem_filter'] at hpa
    have h := hpa.2
    simpa using h
  intro hd
  have hdef : defV P n = some a.lhs := by
    unfold defVars at hd
    cases hv : defV P n with
    | none => rw [hv] at hd; exact absurd hd Std.HashSet.not_mem_empty
    | some w => rw [hv] at hd; exact congrArg some (Variables.mem_singleton.mp hd).symm
  unfold kills at hk
  rw [hdef] at hk
  simp at hk

/-- **Backward-liveness carry.** A candidate delayable past `c` that is live on exit is live entering `c`:
    `pass ⇒ a.lhs ∉ defVars` and `Live.predict` (`live c' ⊆ live c ∪ defVars c`) then force `a.lhs ∈ live c`. -/
theorem pass_live_carry {P : Program} (S : PdceSpec P) {c c' : Config} (hStep : Step P c c')
    {a : Asgn} (hpa : a ∈ pass P c.node) (hlv' : a.lhs ∈ S.π c'.node) :
    a.lhs ∈ S.π c.node := by
  have hmem := S.isLive.predict c c' hStep a.lhs hlv'
  rw [Variables.mem_union] at hmem
  rcases hmem with h | h
  · exact h
  · exact absurd h (pass_notMem_defVars hpa)

/-- **The live-gated invariant**: `#mat ≤ #(live born-crossing) + [in-flight ∧ live]`. The `+[sink ∧ live]`
    slack is the single currently-open live stretch that may still materialize once using no further born. -/
theorem matCount_le_liveBornCount_aux {P : Program} (S : PdceSpec P) (a : Asgn)
    (hk : S.keep a = true) :
    ∀ (fuel : Nat) (c : Config),
      matCount P S a c fuel
        ≤ liveBornCount P S a c fuel
            + (if a ∈ S.ηK c.node ∧ a.lhs ∈ S.π c.node then 1 else 0) := by
  intro fuel
  induction fuel with
  | zero => intro c; simp [matCount, liveBornCount]
  | succ f ih =>
    intro c
    cases hs : step1 P c with
    | next c' =>
      have hStep : Step P c c' := step1_next_iff.mp hs
      have hupd := S.isSink.update c c' hStep
      have IH := ih c'
      have hnh : P.fetch c.node ≠ some .halt := by
        intro hh
        have hhalt : step1 P c = .halt := by unfold step1; rw [hh]
        rw [hhalt] at hs; simp at hs
      have hbeq : blockedSet P c.node = Assignments.sdiff (allAsgns P) (pass P c.node) := by
        unfold blockedSet
        cases hf : P.fetch c.node with
        | none => rfl
        | some i => cases i with
          | halt => exact absurd hf hnh
          | assign x e nx => rfl
          | ifz x z nz => rfl
          | noop nx => rfl
      have hMNsink : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      have hMNpass : a ∈ matNode P S c.node → a ∉ pass P c.node := by
        intro h; have hb := (mem_matNode.mp h).2.1; rw [hbeq] at hb; exact (Assignments.mem_sdiff.mp hb).2
      have hMNlive : a ∈ matNode P S c.node → a.lhs ∈ S.π c.node := fun h => matNode_necessary h
      have hMEdrop : a ∈ matEdge P S c.node c'.node → a ∉ S.ηK c'.node := fun h => (mem_matEdge.mp h).2.1
      have hMElive : a ∈ matEdge P S c.node c'.node → a.lhs ∈ S.π c'.node := fun h => matEdge_necessary hk h
      have hMEde : a ∈ matEdge P S c.node c'.node →
          a ∈ born P c.node ∨ (a ∈ S.ηK c.node ∧ a ∈ pass P c.node) :=
        fun h => mem_delayedExit.mp (mem_matEdge.mp h).1
      have hUp : a ∈ S.ηK c'.node → a ∈ born P c.node ∨ (a ∈ S.ηK c.node ∧ a ∈ pass P c.node) := by
        intro h
        have hk := (mem_ηK.mp h).2
        have hm := hupd a (ηK_sub S _ a h)
        rw [Assignments.mem_union, Assignments.mem_inter] at hm
        exact hm.imp id (fun hh => ⟨mem_ηK.mpr ⟨hh.1, hk⟩, hh.2⟩)
      have hPred : a ∈ pass P c.node → a.lhs ∈ S.π c'.node → a.lhs ∈ S.π c.node :=
        fun hp hl => pass_live_carry S hStep hp hl
      have key : (if a ∈ matNode P S c.node then 1 else 0)
          + ((if a ∈ matEdge P S c.node c'.node then 1 else 0)
             + (if a ∈ S.ηK c'.node ∧ a.lhs ∈ S.π c'.node then (1:Nat) else 0))
          ≤ (if a ∈ born P c.node ∧ a.lhs ∈ S.π c'.node then 1 else 0)
             + (if a ∈ S.ηK c.node ∧ a.lhs ∈ S.π c.node then 1 else 0) := by
        by_cases hmn : a ∈ matNode P S c.node <;>
        by_cases hme : a ∈ matEdge P S c.node c'.node <;>
        by_cases hsk' : a ∈ S.ηK c'.node <;>
        by_cases hbo : a ∈ born P c.node <;>
        by_cases hsk : a ∈ S.ηK c.node <;>
        by_cases hpa : a ∈ pass P c.node <;>
        by_cases hlv' : a.lhs ∈ S.π c'.node <;>
        by_cases hlv : a.lhs ∈ S.π c.node <;>
          simp_all <;> omega
      rw [matCount_next hs, liveBornCount_next hs]
      omega
    | halt =>
      have hMNs : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      have hMNl : a ∈ matNode P S c.node → a.lhs ∈ S.π c.node := fun h => matNode_necessary h
      simp only [matCount, liveBornCount, hs]
      by_cases hmn : a ∈ matNode P S c.node <;>
        by_cases hsk : a ∈ S.ηK c.node <;> by_cases hlv : a.lhs ∈ S.π c.node <;>
        simp_all <;> omega
    | fault =>
      have hMNs : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      have hMNl : a ∈ matNode P S c.node → a.lhs ∈ S.π c.node := fun h => matNode_necessary h
      simp only [matCount, liveBornCount, hs]
      by_cases hmn : a ∈ matNode P S c.node <;>
        by_cases hsk : a ∈ S.ηK c.node <;> by_cases hlv : a.lhs ∈ S.π c.node <;>
        simp_all <;> omega
    | stuck =>
      have hMNs : a ∈ matNode P S c.node → a ∈ S.ηK c.node := fun h => (mem_matNode.mp h).1
      have hMNl : a ∈ matNode P S c.node → a.lhs ∈ S.π c.node := fun h => matNode_necessary h
      simp only [matCount, liveBornCount, hs]
      by_cases hmn : a ∈ matNode P S c.node <;>
        by_cases hsk : a ∈ S.ηK c.node <;> by_cases hlv : a.lhs ∈ S.π c.node <;>
        simp_all <;> omega

/-- **Lemma A, live-gated: `#mat ≤ #(live born-crossing)` over the source run** (from the entry, `sink = ∅`).
    Closes the transform half of the count on the placement-invariant unit. -/
theorem matCount_le_liveBornCount {P : Program} (S : PdceSpec P) (a : Asgn)
    (hk : S.keep a = true) (σ : Store) (fuel : Nat) :
    matCount P S a ⟨P.entry, σ⟩ fuel ≤ liveBornCount P S a ⟨P.entry, σ⟩ fuel := by
  have h := matCount_le_liveBornCount_aux S a hk fuel ⟨P.entry, σ⟩
  have hentry : a ∉ S.ηK P.entry := by
    intro hmem; have := S.isSink.seed a (ηK_sub S _ a hmem)
    simp [sinkSeed, Assignments.empty] at this
  simpa [hentry] using h

/-! ## Lemma B (direct) — `#(live born-crossing) ≤ #pl` over the source run

The direct dual of LCM's `PlCovers`/`crossCount_le_pl` (`EvalCountHeadline.lean:292/306`): a safe covering
placement `pl` computes `a` at least once **between consecutive live `born`-crossings**. `owed` tracks a
crossing awaiting coverage; a new crossing demands the pending one already covered (dedup rejected by
construction). Proved directly by fuel-induction with the one-sided `owed` potential. -/

/-- **Operational coverage of a placement `pl`.** Between consecutive live `born`-crossings there is a
    `pl`-computation (`owed` = a pending crossing; a new crossing requires the pending one already covered).
    Placement-invariant crossing predicate (`born` + `S.π`); the direct dual of LCM's `PlCovers`. -/
def PlCoversAsgn (P : Program) (S : PdceSpec P) (a : Asgn) (pl : Node → Bool) :
    Config → Nat → Bool → Prop
  | _, 0,     owed => owed = false
  | c, k + 1, owed =>
      match step1 P c with
      | .next c' =>
          if a ∈ born P c.node ∧ a.lhs ∈ S.π c'.node then
            ((owed && !(pl c.node)) = false) ∧ PlCoversAsgn P S a pl c' k true
          else
            PlCoversAsgn P S a pl c' k (owed && !(pl c.node))
      | _        => owed = false

/-- **Lemma B — `#(live born-crossing) + [owed] ≤ #pl`.** A covering placement computes `a` at least once per
    live `born`-crossing; at entry (`owed = false`) this is `liveBornCount ≤ #pl`. Direct dual of
    `crossCount_le_pl`, by fuel-induction on the one-sided `owed` potential. -/
theorem liveBornCount_le_pl_aux {P : Program} (S : PdceSpec P) (a : Asgn) (pl : Node → Bool) :
    ∀ (fuel : Nat) (c : Config) (owed : Bool), PlCoversAsgn P S a pl c fuel owed →
      liveBornCount P S a c fuel + (if owed then 1 else 0)
        ≤ ((runNodes P c fuel).filter pl).length := by
  intro fuel
  induction fuel with
  | zero =>
    intro c owed hcov
    have ho : owed = false := hcov
    subst ho; simp [liveBornCount, runNodes]
  | succ k ih =>
    intro c owed hcov
    cases hs : step1 P c with
    | next c' =>
      have hrn : runNodes P c (k + 1) = c.node :: runNodes P c' k := by simp [runNodes, hs]
      have hfp : (List.filter pl (c.node :: runNodes P c' k)).length
          = (if pl c.node then 1 else 0) + (List.filter pl (runNodes P c' k)).length := by
        rw [List.filter_cons]; by_cases h : pl c.node <;> simp [h, Nat.add_comm]
      rw [PlCoversAsgn] at hcov
      simp only [hs] at hcov
      rw [liveBornCount_next hs, hrn, hfp]
      by_cases hcross : a ∈ born P c.node ∧ a.lhs ∈ S.π c'.node
      · rw [if_pos hcross] at hcov
        obtain ⟨ho1, hrec⟩ := hcov
        have ihk : liveBornCount P S a c' k + 1 ≤ ((runNodes P c' k).filter pl).length := by
          have := ih c' true hrec; simpa using this
        simp only [if_pos hcross]
        have hop : (if owed = true then (1:Nat) else 0) ≤ (if pl c.node = true then 1 else 0) := by
          revert ho1; cases owed <;> cases hb : pl c.node <;> simp
        omega
      · rw [if_neg hcross] at hcov
        have ihk := ih c' (owed && !(pl c.node)) hcov
        simp only [if_neg hcross]
        have hop : (if owed = true then (1:Nat) else 0)
            ≤ (if pl c.node = true then 1 else 0)
              + (if (owed && !(pl c.node)) = true then 1 else 0) := by
          cases owed <;> cases hb : pl c.node <;> simp
        omega
    | halt =>
      have ho : owed = false := by rw [PlCoversAsgn] at hcov; simp only [hs] at hcov; exact hcov
      subst ho
      have hrn : runNodes P c (k + 1) = [c.node] := by simp [runNodes, hs]
      simp only [liveBornCount, hs, hrn]; simp
    | fault =>
      have ho : owed = false := by rw [PlCoversAsgn] at hcov; simp only [hs] at hcov; exact hcov
      subst ho
      have hrn : runNodes P c (k + 1) = [c.node] := by simp [runNodes, hs]
      simp only [liveBornCount, hs, hrn]; simp
    | stuck =>
      have ho : owed = false := by rw [PlCoversAsgn] at hcov; simp only [hs] at hcov; exact hcov
      subst ho
      have hrn : runNodes P c (k + 1) = [c.node] := by simp [runNodes, hs]
      simp only [liveBornCount, hs, hrn]; simp

/-- **Lemma B, at entry: `liveBornCount ≤ #pl`.** A safe covering placement computes `a` at least as often as
    there are live `born`-crossings on the source run. The headline's RHS. -/
theorem liveBornCount_le_pl {P : Program} (S : PdceSpec P) (a : Asgn) (pl : Node → Bool)
    (c : Config) (ks : Nat) (hcov : PlCoversAsgn P S a pl c ks false) :
    liveBornCount P S a c ks ≤ ((runNodes P c ks).filter pl).length := by
  have := liveBornCount_le_pl_aux S a pl ks c false hcov; simpa using this

/-- **Lemma A ∘ Lemma B — `#mat ≤ #pl` over the source run** (the quantitative heart of PDCE exec-count
    optimality, modulo the fold `execCount(transform) = matCount`). Every materialization the transform
    performs along the source run is matched by a computation of any safe covering placement `pl`. -/
theorem matCount_le_pl {P : Program} (S : PdceSpec P) (a : Asgn) (hk : S.keep a = true)
    (pl : Node → Bool) (σ : Store) (ks : Nat)
    (hcov : PlCoversAsgn P S a pl ⟨P.entry, σ⟩ ks false) :
    matCount P S a ⟨P.entry, σ⟩ ks ≤ ((runNodes P ⟨P.entry, σ⟩ ks).filter pl).length := by
  have hA := matCount_le_liveBornCount S a hk σ ks
  have hB := liveBornCount_le_pl S a pl ⟨P.entry, σ⟩ ks hcov
  omega


end BaseLanguage.Analyses.PDCE
