-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.PDCE.Correctness

/-!
# `PDCE.FaultPreservation` — PDCE preserves faults in the fault-preserving mode

`Correctness.lean` proves observable preservation on **halting** runs, and `Divergence.lean` the
`Diverge → Diverge` cell; faults were left don't-care, and not by oversight. PDCE *sinks*, so it can
push a faulting computation past a branch and out of the executed path — and, being partial **dead-code**
elimination, it can delete one outright when its result is unused. Either way a faulting source run
becomes a halting target run. That is a real defect of the classical transform.

This file closes it for the mode that declines to sink faulting assignments, i.e. any bundle whose
`keep` admits only fault-free right-hand sides. The two mechanisms that lose a fault are both blocked:

* **sinking** — `η` is read through `ηK`, so a non-`keep` assignment is never deferred; it is dropped at
  its very first successor and materialized in its own birth block's edge chain;
* **elimination** — `matEdge` gates through `liveFilterK`, which lets a non-`keep` assignment past the
  liveness filter even when its left-hand side is dead.

The second is sound only because of the bundle's `keepLive` field: refusing to sink an assignment is not
enough, the transform must still evaluate it *correctly*, and PDCE's liveness is **faint**
(`Live.gate` makes operands live only when the result is). `keepLive` supplies exactly the missing
liveness for a non-`keep` assignment's operands; `kills` then blocks their pending definitions at the
node (it blocks on *use*), so they are materialized in `matNode` before the control instruction and the
operands hold source values by the time the edge chain runs.
-/

namespace BaseLanguage.Analyses.PDCE
open Tac Semantics Std

/-- A faulting right-hand side is not `faultFree`, hence not `keep` for any fault-free-only filter. -/
theorem not_keep_of_eval_none {P : Program} (S : PdceSpec P)
    (hkf : ∀ a : Asgn, S.keep a = true → a.rhs.faultFree = true)
    {a : Asgn} {σ : Store} (hev : eval σ a.rhs = none) : S.keep a = false := by
  rcases Bool.eq_false_or_eq_true (S.keep a) with h | h
  · obtain ⟨v, hv⟩ := eval_isSome_of_faultFree (σ := σ) (hkf a h)
    rw [hv] at hev; exact absurd hev (Option.some_ne_none v)
  · exact h

/-- **PDCE preserves faults, in the fault-free-sinking mode.** If the source run reaches a faulting
    configuration, the transform faults too. The hypothesis `hkf` says the bundle only ever sinks
    assignments that cannot fault; it is `fun _ h => h` for the mode whose `keep` *is* `faultFree`. -/
theorem transform_preserves_faulting {P : Program} (S : PdceSpec P) (wf : WellFormed P)
    (hkf : ∀ a : Asgn, S.keep a = true → a.rhs.faultFree = true)
    {σ : Store} {c_f : Config} (hrun : Steps P ⟨P.entry, σ⟩ c_f) (hfault : Faulting P c_f) :
    ∃ df, Steps (transform P S) ⟨blockOff P S P.entry, σ⟩ df ∧ Faulting (transform P S) df := by
  obtain ⟨x, e, next, hf, hev⟩ := hfault
  obtain ⟨nd, cσ⟩ := c_f
  simp only at hf hev
  -- the source reaches the faulting node's block, matched
  obtain ⟨d, hsteps, hm⟩ := match_steps S wf (match_init S σ) hrun
  obtain ⟨hnode, h2, hrec, hindep⟩ := hm
  obtain ⟨dn, dσ⟩ := d
  subst hnode
  have hi : nd < P.size := fetch_lt hf
  have hbound : ∀ n, Assignments.Subset (S.η n) (allAsgns P) := S.isSink.within
  have hkeep0 : S.keep (⟨x, e⟩ : Asgn) = false := not_keep_of_eval_none S hkf (σ := cσ) hev
  have hbornx : born P nd = Assignments.singleton (⟨x, e⟩ : Asgn) := by unfold born; rw [hf]
  have huseV : useV P nd = instrUsedVars (.assign x e next) := by unfold useV; rw [hf]
  -- the faulting assignment is materialized on the edge out of its own block
  have hinE : (⟨x, e⟩ : Asgn) ∈ matEdge P S nd next := by
    refine mem_matEdge.mpr ⟨mem_delayedExit.mpr (Or.inl ?_), ?_, Or.inr hkeep0⟩
    · rw [hbornx]; exact Assignments.mem_singleton.mpr rfl
    · intro hc; rw [(mem_ηK.mp hc).2] at hkeep0; exact Bool.noConfusion hkeep0
  -- run the node-entry chain (every entry is recoverable, so none of them faults)
  have hrn : ∀ a ∈ matNode P S nd, eval dσ a.rhs = some (cσ a.lhs) := by
    intro a ha; obtain ⟨hs, _, hl⟩ := mem_matNode.mp ha; exact hrec a.lhs a.rhs hs hl
  obtain ⟨τ1, hs1, hoff1, hon1⟩ := matNode_exec S hi hrn hindep
  have hmat_ntransp : ∀ m ∈ matNode P S nd, m ∉ pass P nd := by
    intro m hm hmt
    have hb := (mem_matNode.mp hm).2.1; simp only [blockedSet, hf] at hb
    exact (Assignments.mem_sdiff.mp hb).2 hmt
  -- `keepLive` gives the operands of the faulting assignment their liveness at `nd`
  have hwlive : ∀ w, w ∈ useV P nd → w ∈ S.π nd := by
    intro w hw
    refine S.keepLive nd ⟨x, e⟩ ?_ hkeep0 w ?_
    · rw [hbornx]; exact Assignments.mem_singleton.mpr rfl
    · simp only [rhsVars, hf, usedVars]; exact Variables.mem_ofList.mpr hw
  -- …hence they are materialized to their source values before the control instruction
  have hop_fresh : ∀ w, w ∈ useV P nd → τ1 w = cσ w := by
    intro w hw
    have hwl := hwlive w hw
    by_cases hwf : ∃ ew, (⟨w, ew⟩ : Asgn) ∈ S.ηK nd
    · obtain ⟨ew, hew⟩ := hwf
      have hewη : (⟨w, ew⟩ : Asgn) ∈ S.η nd := ηK_sub S nd _ hew
      have hk : kills P nd ⟨w, ew⟩ = true := by simp [kills, List.contains_eq_mem, hw]
      have hntr : (⟨w, ew⟩ : Asgn) ∉ pass P nd := fun ht => by
        have := (mem_transp.mp ht).2; rw [hk] at this; exact absurd this (by simp)
      exact hon1 ⟨w, ew⟩ (mem_matNode.mpr ⟨hew,
        by simp only [blockedSet, hf]
           exact Assignments.mem_sdiff.mpr ⟨hbound nd _ hewη, hntr⟩, hwl⟩)
    · have hnf : ∀ e', (⟨w, e'⟩ : Asgn) ∉ S.ηK nd := fun e' h => hwf ⟨e', h⟩
      rw [hoff1 w (fun m hm hmw => hnf m.rhs (by rw [← hmw]; exact (mem_matNode.mp hm).1))]
      exact h2 w hwl hnf
  have hevτ1 : eval τ1 e = none := by
    rw [eval_congr (fun w hw => hop_fresh w (huseV ▸ readsVar_imp_mem hw))]; exact hev
  -- block layout: entry chain, the floated control, then the edge chain
  have hbeq : block P S nd = matChain (matNode P S nd) (blockOff P S nd)
      ++ (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
            else blockOff P S nd + (matNode P S nd).length + 1)
          :: edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
              (blockOff P S next)) := by simp only [block, hf]
  have hcs : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
      = (block P S nd)[(matNode P S nd).length]? :=
    transform_fetch hi (by rw [block_length]; simp only [blockLen, hf]; omega)
  have hctl : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length)
      = some (Cmd.noop (if (matEdge P S nd next).isEmpty then blockOff P S next
            else blockOff P S nd + (matNode P S nd).length + 1)) := by
    rw [hcs, hbeq, show (matNode P S nd).length = (matNode P S nd).length + 0 from rfl,
        matChain_append_get]; rfl
  have hne : ¬ (matEdge P S nd next).isEmpty := by
    intro hemp; rw [List.isEmpty_iff.mp hemp] at hinE; simp at hinE
  have hctlstep : Step (transform P S)
      ⟨blockOff P S nd + (matNode P S nd).length, τ1⟩
      ⟨blockOff P S nd + (matNode P S nd).length + 1, τ1⟩ := by
    refine Step.noop ?_; rw [hctl, if_neg hne]
  -- the edge chain's fetch facts
  have hef : ∀ k (hk : k < (matEdge P S nd next).length),
      (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
        = some (.assign ((matEdge P S nd next)[k]'hk).lhs ((matEdge P S nd next)[k]'hk).rhs
          (if k + 1 == (matEdge P S nd next).length then blockOff P S next
           else blockOff P S nd + (matNode P S nd).length + 1 + k + 1)) := by
    intro k hk
    have hjb : (matNode P S nd).length + 1 + k < (block P S nd).length := by
      rw [block_length]; simp only [blockLen, hf]; omega
    have hfetcheq : (transform P S).fetch (blockOff P S nd + ((matNode P S nd).length + 1 + k))
        = (block P S nd)[(matNode P S nd).length + 1 + k]? := transform_fetch hi hjb
    have hL : (transform P S).fetch (blockOff P S nd + (matNode P S nd).length + 1 + k)
        = (edgeChain (matEdge P S nd next) (blockOff P S nd + (matNode P S nd).length + 1)
            (blockOff P S next))[k]? := by
      rw [show blockOff P S nd + (matNode P S nd).length + 1 + k
            = blockOff P S nd + ((matNode P S nd).length + 1 + k) from by omega, hfetcheq, hbeq,
          show (matNode P S nd).length + 1 + k = (matNode P S nd).length + (1 + k) from by omega,
          matChain_append_get, show 1 + k = k + 1 from by omega, List.getElem?_cons_succ]
    rw [hL, edgeChain_getElem? hk]
  have hindepE : ∀ a ∈ matEdge P S nd next, ∀ b ∈ matEdge P S nd next, a ≠ b →
      exprReadsVar a.rhs b.lhs = false := fun a ha b hb hab =>
    (Indep_delayedExit S hindep (mem_matEdge.mp hb).1 (mem_matEdge.mp ha).1 (Ne.symm hab)).2
  -- either the edge chain faults (done) or every entry evaluates — which our entry does not
  rcases steps_edgeSeg_fault (Q := transform P S) (blockOff P S next) (matEdge P S nd next)
      (blockOff P S nd + (matNode P S nd).length + 1) τ1 matEdge_nodup hef hindepE with
    ⟨cf, hcs2, hfl⟩ | hclean
  · exact ⟨cf, steps_trans hsteps
      (steps_trans hs1 (steps_trans (Steps.tail Steps.refl hctlstep) hcs2)), hfl⟩
  · exact absurd hevτ1 (hclean _ hinE)

end BaseLanguage.Analyses.PDCE
