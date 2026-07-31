-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.ConstFold
import BaseLanguage.Pass.UCE
/-!
# `Pass.Optimize` — the const-prop optimization round, iterated to a fixpoint.

One round is `constFold ∘ branchFold ∘ UCE`, each re-analyzed against the *current* program (a
`RoundSpecs` bundles the three abstract specs). `iterateOpt` applies the round `n` times, re-analyzing
each time — this is the alternation taken to a (bounded) fixpoint, so constant chains propagate to any
depth: `a := 1; b := a+1; c := b+1` becomes `c := 3` after enough rounds.

Everything is abstract over the specs: `iterateOpt` takes a *provider* `(Q) → WellFormed Q → RoundSpecs Q`
(the re-analysis), so `pipeline_to_asm` threads it without ever touching the solver; `Main` supplies the
concrete provider (`cpSpec`/`reachSpec`). Preservation is by induction on the fuel — each round preserves
halt/fault/diverge over its specs, so any composition does.
-/
namespace BaseLanguage
namespace Pass

open Tac Semantics

variable {P : Program}

/-- The three specs one optimization round needs, each for the program the previous pass produced. -/
structure RoundSpecs (P : Program) where
  scp1   : BranchFold.CPSpec P
  scp2   : BranchFold.CPSpec (ConstFold.run P scp1)
  sreach : UCE.ReachSpec (BranchFold.run (ConstFold.run P scp1) scp2)

/-- One optimization round: substitute+fold, fold determined branches, remove the orphaned code. -/
def optRound (P : Program) (rs : RoundSpecs P) : Program :=
  UCE.run (BranchFold.run (ConstFold.run P rs.scp1) rs.scp2) rs.sreach

theorem optRound_wf (wf : WellFormed P) (rs : RoundSpecs P) : WellFormed (optRound P rs) :=
  UCE.wellFormed rs.sreach (BranchFold.run_wellFormed rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf))

theorem optRound_preserves_halt (wf : WellFormed P) (rs : RoundSpecs P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (optRound P rs) ⟨(optRound P rs).entry, σ⟩ df ∧ Final (optRound P rs) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v := by
  obtain ⟨cf1, hs1, hf1, ho1⟩ := ConstFold.preserves_halt rs.scp1 hrun hfin
  obtain ⟨cf2, hs2, hf2, ho2⟩ := BranchFold.preserves_halt rs.scp2 hs1 hf1
  obtain ⟨cf3, hs3, hf3, ho3⟩ :=
    UCE.preserves_halt rs.sreach (BranchFold.run_wellFormed rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf)) hs2 hf2
  exact ⟨cf3, hs3, hf3, fun v hv => (ho3 v hv).trans ((ho2 v hv).trans (ho1 v hv))⟩

theorem optRound_preserves_faults (wf : WellFormed P) (rs : RoundSpecs P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (optRound P rs) ⟨(optRound P rs).entry, σ⟩ df ∧ Faulting (optRound P rs) df := by
  obtain ⟨cf1, hs1, hf1⟩ := ConstFold.preserves_faults rs.scp1 hrun hfault
  obtain ⟨cf2, hs2, hf2⟩ := BranchFold.preserves_faults rs.scp2 hs1 hf1
  exact UCE.preserves_faults rs.sreach
    (BranchFold.run_wellFormed rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf)) hs2 hf2

theorem optRound_preserves_diverges (wf : WellFormed P) (rs : RoundSpecs P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (optRound P rs) ⟨(optRound P rs).entry, σ⟩ :=
  UCE.preserves_diverges rs.sreach
    (BranchFold.run_wellFormed rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf))
    (BranchFold.preserves_diverges rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf)
      (ConstFold.preserves_diverges rs.scp1 wf hdiv))

@[simp] theorem optRound_obs (P : Program) (rs : RoundSpecs P) : (optRound P rs).obs = P.obs := rfl

/-- A round ends in UCE, so its result has no unreachable node — regardless of the input's reachability. -/
theorem optRound_allReachable (wf : WellFormed P) (rs : RoundSpecs P) : AllReachable (optRound P rs) :=
  UCE.allReachable rs.sreach (BranchFold.run_wellFormed rs.scp2 (ConstFold.run_wellFormed rs.scp1 wf))

/-! ## Iterating the round (bounded fuel), over an abstract re-analysis provider. -/

/-- Re-analyse any well-formed program into a fresh `RoundSpecs`. Instantiated concretely (from the solver)
    at `Main`; abstract here so nothing downstream depends on the solver. -/
abbrev Provider := (Q : Program) → WellFormed Q → RoundSpecs Q

/-- Apply `optRound` up to `n` times, re-analysing each time, **stopping early at a fixpoint**: once a
    round is a no-op (`optRound P … = P`), every further round is also a no-op, so the result is already
    settled. `n` (the caller passes `P.size`, the worst-case chain length) is only an upper bound; a program
    with nothing left to fold converges in one round instead of `n`, which is the difference between
    `O(n · round)` and `O(depth · round)` — the const-prop iteration does not re-run the reachable/CP
    analyses `n` times over an already-fixed program. The result is IDENTICAL to running all `n` rounds
    (a fixpoint is a fixpoint), so every preservation property is re-established below unchanged. -/
def iterateOpt (prov : Provider) : (n : Nat) → (P : Program) → WellFormed P → Program
  | 0,     P, _  => P
  | n + 1, P, wf =>
    if optRound P (prov P wf) = P then optRound P (prov P wf)
    else iterateOpt prov n (optRound P (prov P wf)) (optRound_wf wf (prov P wf))

/-- The `n+1` unfolding equation (definitional), so the theorems below can `rw` then `split` on the
    fixpoint test without re-deriving the recursor each time. -/
theorem iterateOpt_succ (prov : Provider) (n : Nat) (P : Program) (wf : WellFormed P) :
    iterateOpt prov (n + 1) P wf =
      if optRound P (prov P wf) = P then optRound P (prov P wf)
      else iterateOpt prov n (optRound P (prov P wf)) (optRound_wf wf (prov P wf)) := rfl

theorem iterateOpt_wf (prov : Provider) : (n : Nat) → (P : Program) → (wf : WellFormed P) →
    WellFormed (iterateOpt prov n P wf)
  | 0,     _, wf => wf
  | n + 1, P, wf => by
      rw [iterateOpt_succ]; split
      · exact optRound_wf wf (prov P wf)
      · exact iterateOpt_wf prov n _ (optRound_wf wf (prov P wf))

theorem iterateOpt_preserves_halt (prov : Provider) (n : Nat) :
    ∀ (P : Program) (wf : WellFormed P) {σ : Store} {cf : Config},
      Steps P ⟨P.entry, σ⟩ cf → Final P cf →
      ∃ df, Steps (iterateOpt prov n P wf) ⟨(iterateOpt prov n P wf).entry, σ⟩ df
          ∧ Final (iterateOpt prov n P wf) df ∧ ∀ v ∈ P.obs, df.store v = cf.store v := by
  induction n with
  | zero => intro P wf σ cf hrun hfin; exact ⟨cf, hrun, hfin, fun _ _ => rfl⟩
  | succ n ih =>
      intro P wf σ cf hrun hfin
      obtain ⟨cfR, hsR, hfR, hoR⟩ := optRound_preserves_halt wf (prov P wf) hrun hfin
      rw [iterateOpt_succ]; split
      · exact ⟨cfR, hsR, hfR, hoR⟩
      · obtain ⟨df, hs, hf, ho⟩ := ih (optRound P (prov P wf)) (optRound_wf wf (prov P wf)) hsR hfR
        exact ⟨df, hs, hf, fun v hv => (ho v hv).trans (hoR v hv)⟩

theorem iterateOpt_preserves_faults (prov : Provider) (n : Nat) :
    ∀ (P : Program) (wf : WellFormed P) {σ : Store} {cf : Config},
      Steps P ⟨P.entry, σ⟩ cf → Faulting P cf →
      ∃ df, Steps (iterateOpt prov n P wf) ⟨(iterateOpt prov n P wf).entry, σ⟩ df
          ∧ Faulting (iterateOpt prov n P wf) df := by
  induction n with
  | zero => intro P wf σ cf hrun hfault; exact ⟨cf, hrun, hfault⟩
  | succ n ih =>
      intro P wf σ cf hrun hfault
      obtain ⟨cfR, hsR, hfR⟩ := optRound_preserves_faults wf (prov P wf) hrun hfault
      rw [iterateOpt_succ]; split
      · exact ⟨cfR, hsR, hfR⟩
      · exact ih (optRound P (prov P wf)) (optRound_wf wf (prov P wf)) hsR hfR

theorem iterateOpt_preserves_diverges (prov : Provider) (n : Nat) :
    ∀ (P : Program) (wf : WellFormed P) {σ : Store}, Diverges P ⟨P.entry, σ⟩ →
      Diverges (iterateOpt prov n P wf) ⟨(iterateOpt prov n P wf).entry, σ⟩ := by
  induction n with
  | zero => intro P wf σ hdiv; exact hdiv
  | succ n ih =>
      intro P wf σ hdiv
      have hdR := optRound_preserves_diverges wf (prov P wf) hdiv
      rw [iterateOpt_succ]; split
      · exact hdR
      · exact ih (optRound P (prov P wf)) (optRound_wf wf (prov P wf)) hdR

/-- `iterateOpt` keeps `AllReachable`: every round re-establishes it (`optRound_allReachable`), and the
    zero-fuel case returns the program unchanged — hence the hypothesis. -/
theorem iterateOpt_allReachable (prov : Provider) : (n : Nat) → (P : Program) → (wf : WellFormed P) →
    AllReachable P → AllReachable (iterateOpt prov n P wf)
  | 0,     _, _,  har => har
  | n + 1, P, wf, _   => by
      rw [iterateOpt_succ]; split
      · exact optRound_allReachable wf (prov P wf)
      · exact iterateOpt_allReachable prov n _ (optRound_wf wf (prov P wf)) (optRound_allReachable wf (prov P wf))

@[simp] theorem iterateOpt_obs (prov : Provider) :
    ∀ (n : Nat) (P : Program) (wf : WellFormed P), (iterateOpt prov n P wf).obs = P.obs
  | 0,     _, _  => rfl
  | n + 1, P, wf => by
      rw [iterateOpt_succ]; split
      · exact optRound_obs P (prov P wf)
      · rw [iterateOpt_obs prov n, optRound_obs]

end Pass
end BaseLanguage
