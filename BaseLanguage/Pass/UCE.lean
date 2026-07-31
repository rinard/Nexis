-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Compact
import BaseLanguage.Behavior.Outcomes
import BaseLanguage.IR.LocalsSub
import BaseLanguage.Pass.ReachBFS
/-!
# `Pass.UCE` — unreachable-code elimination over an abstract reachability solution.

Every proof here runs on `ReachSpec` — an abstract **keep-predicate** with three graph-level obligations:
it holds at the entry, it is closed under `succList` (CFG edges), and it implies forward reachability
`FReach`. It never mentions a solver, a fixpoint, a term calculus, or a dataflow domain: any engine can
supply a `ReachSpec` — a hand-written graph BFS (`bfsReachSpec`, the shipped one) or an adapter over some
solved solution. UCE's whole verification — well-formedness, halt/fault/diverge preservation, and
`AllReachable` — goes through unchanged for any of them.

`keep n` decides "the entry reaches `n` in the CFG"; the `sound`/`closed`/`entry` obligations pin it to
`FReach` closely enough for both soundness (a dropped node is never executed) and the `AllReachable`
postcondition (every kept node is forward-reachable). `bfsReachSpec` discharges all three from a plain
`succList` traversal (`ReachBFS.reachList`), replacing the ancestor-set dataflow solve.
-/
namespace BaseLanguage
namespace Pass
namespace UCE

open Tac Tac.Locals Semantics Pass Pass.Compact
open scoped Classical

variable {P : Program}

/-- **Abstract reachability keep-predicate.** Three graph-level obligations: `entry` holds; `closed` under
    `succList` (every CFG successor of a kept node is kept); and `sound` — a kept node is forward-reachable
    (`FReach`). No solver, no dataflow domain, no `Step`-level reasoning. `bfsReachSpec` discharges all three
    from a `succList` BFS; the obligations are exactly what UCE's soundness + `AllReachable` proofs need. -/
structure ReachSpec (P : Program) where
  keep   : Node → Bool
  entry  : keep P.entry = true
  closed : ∀ {p nd : Node}, nd ∈ succList P p → keep p = true → keep nd = true
  sound  : ∀ {nd : Node}, keep nd = true → FReach P nd

/-! ## Step helpers (language-level: the source of a step is fetchable, in range, gens itself). -/

theorem step_src_fetch {c c' : Config} (h : Step P c c') : ∃ instr, P.fetch c.node = some instr := by
  cases h with
  | assign hf _ => exact ⟨_, hf⟩ | ifzT hf _ => exact ⟨_, hf⟩
  | ifzF hf _ => exact ⟨_, hf⟩ | noop hf => exact ⟨_, hf⟩

theorem step_src_lt {c c' : Config} (h : Step P c c') : c.node < P.size :=
  let ⟨_, hf⟩ := step_src_fetch h; fetch_lt hf

theorem step_gen_self {c c' : Config} (h : Step P c c') : c.node ∈ genNode P c.node := by
  obtain ⟨i, hi⟩ := step_src_fetch h; rw [genNode, hi]; exact Defs.mem_singleton.mpr rfl

/-- A step edge is a CFG edge (language-level; no `realizableSucc`). -/
theorem step_mem_succList {c c' : Config} (h : Step P c c') : c'.node ∈ succList P c.node := by
  cases h with
  | assign hf _ => rw [succList, hf]; simp [Cmd.succs]
  | ifzT hf _ => rw [succList, hf]; simp [Cmd.succs]
  | ifzF hf _ => rw [succList, hf]; simp [Cmd.succs]
  | noop hf => rw [succList, hf]; simp [Cmd.succs]

variable (S : ReachSpec P)

/-! ## The keep-predicate and its closure. -/

/-- `n` survives iff the spec's keep-predicate holds. -/
def keep (n : Node) : Bool := S.keep n

@[simp] theorem keep_entry : keep S P.entry = true := S.entry

/-- **Closure.** `keep` is preserved by every step (a step is a CFG edge, and `keep` is `succList`-closed). -/
theorem keep_step {c c' : Config} (h : Step P c c') (hk : keep S c.node = true) :
    keep S c'.node = true := S.closed (step_mem_succList h) hk

theorem keep_run {c d : Config} (hr : keep S c.node = true) (h : Steps P c d) :
    keep S d.node = true := by
  induction h with
  | refl => exact hr
  | tail _ hbc ih => exact keep_step S hbc ih

/-- **Soundness kernel.** A dropped node is never executed. -/
theorem not_keep_unreached {n : Node} (hk : keep S n = false) {σ σ' : Store}
    (h : Steps P ⟨P.entry, σ⟩ ⟨n, σ'⟩) : False := by
  have : keep S n = true := keep_run S (keep_entry S) h
  rw [hk] at this; exact Bool.noConfusion this

/-! ## The transform. -/

/-- Representative: keep survivors fixed, redirect dropped nodes to the (kept) entry. -/
def rep (n : Node) : Node := if keep S n then n else P.entry

theorem rep_self {n : Node} (h : keep S n = true) : rep S n = n := if_pos h

/-- **Unreachable-code elimination** (parameterized by the reachability solution). -/
def run (P : Program) (S : ReachSpec P) : Program := compactBy (keep S) (rep S) P

abbrev keptL (S : ReachSpec P) : List Node := keptList (keep S) P
abbrev newNode (S : ReachSpec P) (n : Node) : Node := remap (rep S) (keptL S) n

theorem rep_kept (wf : WellFormed P) {n : Node} (hn : n < P.size) : rep S n ∈ keptL S := by
  unfold rep
  split
  · next h => exact mem_keptList.mpr ⟨hn, h⟩
  · next => exact mem_keptList.mpr ⟨wf.entry_lt, keep_entry S⟩

theorem interface (wf : WellFormed P) : Interface (keep S) (rep S) P where
  entry_rep_kept := rep_kept S wf wf.entry_lt
  succ_rep_kept := fun _ hf hs => rep_kept S wf (wf.succ_lt hf hs)

theorem wellFormed (wf : WellFormed P) : WellFormed (run P S) :=
  compactBy_wellFormed (interface S wf)

@[simp] theorem obs (P : Program) (S : ReachSpec P) : (run P S).obs = P.obs := rfl
theorem entry_eq : (run P S).entry = newNode S P.entry := compactBy_entry P

theorem fetch (wf : WellFormed P) {n : Node} (hr : keep S n = true) (hn : n < P.size)
    {c : Cmd} (hc : P.fetch n = some c) :
    (run P S).fetch (newNode S n) = some (remapCmd (rep S) (keptL S) c) := by
  refine compacted_fetch (rep_kept S wf hn) ?_
  rw [rep_self S hr]; exact hc

/-! ## Behaviour preservation. -/

theorem step_sim (wf : WellFormed P) {c c' : Config} (hstep : Step P c c')
    (hr : keep S c.node = true) :
    Step (run P S) ⟨newNode S c.node, c.store⟩ ⟨newNode S c'.node, c'.store⟩ := by
  cases hstep with
  | @assign nd σ x e next v hf hv =>
      have hcf : (run P S).fetch (newNode S nd) = some (.assign x e (newNode S next)) := by
        simpa only [remapCmd] using fetch S wf hr (fetch_lt hf) hf
      exact Step.assign hcf hv
  | @ifzT nd σ x z nz hf hz =>
      have hcf : (run P S).fetch (newNode S nd) = some (.ifz x (newNode S z) (newNode S nz)) := by
        simpa only [remapCmd] using fetch S wf hr (fetch_lt hf) hf
      exact Step.ifzT hcf hz
  | @ifzF nd σ x z nz hf hz =>
      have hcf : (run P S).fetch (newNode S nd) = some (.ifz x (newNode S z) (newNode S nz)) := by
        simpa only [remapCmd] using fetch S wf hr (fetch_lt hf) hf
      exact Step.ifzF hcf hz
  | @noop nd σ next hf =>
      have hcf : (run P S).fetch (newNode S nd) = some (.noop (newNode S next)) := by
        simpa only [remapCmd] using fetch S wf hr (fetch_lt hf) hf
      exact Step.noop hcf

private theorem oneStep {c c' : Config} (h : Step P c c') : Steps P c c' := Steps.tail Steps.refl h

theorem steps_sim (wf : WellFormed P) {c d : Config} (hr : keep S c.node = true) (h : Steps P c d) :
    Steps (run P S) ⟨newNode S c.node, c.store⟩ ⟨newNode S d.node, d.store⟩ := by
  induction h with
  | refl => exact Steps.refl
  | tail hab hbc ih => exact steps_trans ih (oneStep (step_sim S wf hbc (keep_run S hr hab)))

theorem preserves_halt (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (run P S) ⟨(run P S).entry, σ⟩ df ∧ Final (run P S) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v := by
  refine ⟨⟨newNode S cf.node, cf.store⟩, ?_, ?_, fun v _ => rfl⟩
  · rw [entry_eq]; exact steps_sim S wf (keep_entry S) hrun
  · have hrcf := keep_run S (keep_entry S) hrun
    show (run P S).fetch (newNode S cf.node) = some .halt
    simpa only [remapCmd] using fetch S wf hrcf (fetch_lt hfin) hfin

theorem preserves_faults (wf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (run P S) ⟨(run P S).entry, σ⟩ df ∧ Faulting (run P S) df := by
  refine ⟨⟨newNode S cf.node, cf.store⟩, ?_, ?_⟩
  · rw [entry_eq]; exact steps_sim S wf (keep_entry S) hrun
  · have hrcf := keep_run S (keep_entry S) hrun
    obtain ⟨x, e, next, hf, hev⟩ := hfault
    refine ⟨x, e, newNode S next, ?_, hev⟩
    show (run P S).fetch (newNode S cf.node) = some (.assign x e (newNode S next))
    simpa only [remapCmd] using fetch S wf hrcf (fetch_lt hf) hf

def Rel (c d : Config) : Prop := keep S c.node = true ∧ d = ⟨newNode S c.node, c.store⟩

theorem stepSimG (wf : WellFormed P) : StepSimG P (run P S) (Rel S) := by
  intro c c' d _ hR hstep
  obtain ⟨hr, rfl⟩ := hR
  exact ⟨_, _, step_sim S wf hstep hr, Steps.refl, keep_step S hstep hr, rfl⟩

theorem preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (run P S) ⟨(run P S).entry, σ⟩ := by
  rw [entry_eq]
  exact diverges_of_stepsimG (stepSimG S wf) wf wf.entry_lt ⟨keep_entry S, rfl⟩ hdiv

/-! ## `AllReachable`: the compacted program has no unreachable node. -/

/-- `FReach → keep`: `keep` holds at the entry (`entry`) and is `succList`-closed (`closed`). -/
theorem FReach_keep {n : Node} (h : FReach P n) : keep S n = true := by
  induction h with
  | entry => exact keep_entry S
  | step _ hs ih => exact S.closed hs ih

/-- Forward reachability transfers into the compacted program (kept nodes remap to reachable nodes). -/
theorem FReach_run (wf : WellFormed P) {n : Node} (h : FReach P n) :
    FReach (run P S) (newNode S n) := by
  induction h with
  | entry => rw [← entry_eq]; exact FReach.entry
  | @step p nd hp hs ih =>
      refine FReach.step ih ?_
      have hrp : keep S p = true := FReach_keep S hp
      have hplt : p < P.size := FReach_lt wf hp
      obtain ⟨instr, hf, hns⟩ := mem_succList hs
      show newNode S nd ∈ succList (run P S) (newNode S p)
      rw [succList, fetch S wf hrp hplt hf, Option.elim, remapCmd_succs]
      exact List.mem_map.mpr ⟨nd, hns, rfl⟩

theorem keptL_nodup (P : Program) (S : ReachSpec P) : (keptL S).Nodup := (List.nodup_range).filter _

theorem newNode_getElem (wf : WellFormed P) {m : Node} (hm : m < (keptL S).length) :
    newNode S ((keptL S)[m]'hm) = m := by
  have hkr : keep S ((keptL S)[m]'hm) = true := (mem_keptList.mp (List.getElem_mem hm)).2
  show remap (rep S) (keptL S) ((keptL S)[m]'hm) = m
  unfold remap
  rw [rep_self S hkr]
  have hjlt : (keptL S).findIdx (· == (keptL S)[m]'hm) < (keptL S).length :=
    List.findIdx_lt_length_of_exists ⟨(keptL S)[m]'hm, List.getElem_mem hm, by simp⟩
  have hjeq : (keptL S)[(keptL S).findIdx (· == (keptL S)[m]'hm)]'hjlt = (keptL S)[m]'hm :=
    eq_of_beq (List.findIdx_getElem (w := hjlt))
  exact (List.getElem_inj (keptL_nodup P S)).mp hjeq

/-- **UCE leaves no unreachable node.** -/
theorem allReachable (wf : WellFormed P) : AllReachable (run P S) := by
  intro m hm
  rw [show (run P S).size = (keptL S).length from by rw [run, compactBy_size]] at hm
  rw [← newNode_getElem S wf hm]
  exact FReach_run S wf (S.sound (mem_keptList.mp (List.getElem_mem hm)).2)

/-! ## The shipped engine: a `succList` BFS discharges every `ReachSpec` obligation. -/

/-- `keep` from the BFS reachable set — `reachList P` is let-bound so the traversal runs **once**, then
    membership is a lookup (no per-node re-solve). -/
def bfsKeep (P : Program) : Node → Bool :=
  let rl := ReachBFS.reachList P
  fun n => decide (n ∈ rl)

theorem bfsKeep_iff (P : Program) (n : Node) : bfsKeep P n = true ↔ n ∈ ReachBFS.reachList P :=
  decide_eq_true_iff

/-- **The reachability `ReachSpec` produced by a plain graph BFS** — no dataflow solve. Its three
    obligations are `ReachBFS.entry_mem_reachList` / `reachList_closed` / `mem_reachList_iff_FReach`. -/
def bfsReachSpec (P : Program) (wf : WellFormed P) : ReachSpec P where
  keep := bfsKeep P
  entry := (bfsKeep_iff P P.entry).mpr ReachBFS.entry_mem_reachList
  closed := fun {p nd} hs hk => (bfsKeep_iff P nd).mpr (ReachBFS.reachList_closed wf ((bfsKeep_iff P p).mp hk) hs)
  sound := fun {nd} hk => (ReachBFS.mem_reachList_iff_FReach wf nd).mp ((bfsKeep_iff P nd).mp hk)

end UCE
end Pass
end BaseLanguage
