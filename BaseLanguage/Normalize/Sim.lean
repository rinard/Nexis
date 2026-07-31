-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Normalize

/-!
# `Normalize.Sim` — semantic forward simulation for the three normal-form pre-passes

The existing `Normalize.*` proofs establish only **structural** facts (`WellFormed`, reachability,
sizes, fetch). This module adds the missing **semantic** layer: each pre-pass *preserves a halting
run's observable result*. The three `*_preserves_halt` lemmas compose into `normalize_preserves_halt`,
which is what the end-to-end AST→ASM pipeline correctness threads through (between `lower` and the
LCM/PDCE optimizer + backend).

Shape (mirrors `LCM`/`PDCE`'s `transform_preserves_halt`): on a terminating source run
`Steps P ⟨P.entry, σ⟩ cf` with `Final P cf`, the transformed program halts from its own entry in a
store agreeing with `cf` on every **observable** (`v ∈ P.obs`). Inserted scratch (`.tmp`) writes are
unobservable, so they don't disturb the observable frame.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

-- `steps_trans` (transitivity of `Steps`) is a shared reference-semantics lemma hoisted to `IR.TAC`.

/-- A single step is a `Steps`. -/
theorem steps_single {Q : Program} {a b : Config} (h : Step Q a b) : Steps Q a b :=
  Steps.tail Steps.refl h

/-! ## Store-update + eval-congruence micro-lemmas (shared). -/

theorem upd_self {σ : Store} {x : Var} {v : Val} : (σ.update x v) x = v := by simp [Store.update]
theorem upd_ne {σ : Store} {x y : Var} {v : Val} (h : y ≠ x) : (σ.update x v) y = σ y := by
  simp [Store.update, h]

/-- An atom's value depends only on the store at its (single) read var. -/
theorem evalAtom_agree' {σT σ : Store} {a : Atom} (h : ∀ v ∈ (atomVar a).toList, σT v = σ v) :
    evalAtom σT a = evalAtom σ a := by
  cases a with
  | var x => exact h x (by simp [atomVar])
  | imm n => rfl

/-- An expression's value depends only on the store at its read vars. -/
theorem eval_agree' {σT σ : Store} {e : Expr} (h : ∀ v ∈ exprVars e, σT v = σ v) :
    eval σT e = eval σ e := by
  cases e with
  | atom a => show some (evalAtom σT a) = some (evalAtom σ a); rw [evalAtom_agree' h]
  | una op a => show some (op.denote (evalAtom σT a)) = some (op.denote (evalAtom σ a))
                rw [evalAtom_agree' h]
  | bin op a b =>
      show op.denote (evalAtom σT a) (evalAtom σT b) = op.denote (evalAtom σ a) (evalAtom σ b)
      rw [evalAtom_agree' (a := a) (fun v hv => h v (List.mem_append.mpr (Or.inl hv))),
          evalAtom_agree' (a := b) (fun v hv => h v (List.mem_append.mpr (Or.inr hv)))]

/-! ## `prependEntry` — append a `noop` entry; old nodes are byte-for-byte unchanged.

The transformed run is: one `noop` from the fresh entry into the old entry, then the source run
verbatim (old nodes keep their `fetch`, so every step lifts and the store never changes). -/

variable {P : Program}

/-- A source step at an in-range node lifts unchanged into `prependEntry P` (old `fetch` agrees). -/
theorem step_lift_prepend {c c' : Config} (hc : c.node < P.size) (h : Step P c c') :
    Step (prependEntry P) c c' := by
  cases h with
  | assign hf hv => exact Step.assign (by rw [prependEntry_fetch_lt hc]; exact hf) hv
  | ifzT hf hz   => exact Step.ifzT (by rw [prependEntry_fetch_lt hc]; exact hf) hz
  | ifzF hf hz   => exact Step.ifzF (by rw [prependEntry_fetch_lt hc]; exact hf) hz
  | noop hf      => exact Step.noop (by rw [prependEntry_fetch_lt hc]; exact hf)

/-- A whole in-range source run lifts into `prependEntry P`. -/
theorem steps_lift_prepend (hwf : WellFormed P) {c c' : Config}
    (hc : c.node < P.size) (h : Steps P c c') : Steps (prependEntry P) c c' := by
  induction h with
  | refl => exact Steps.refl
  | tail hs hstep ih =>
      exact Steps.tail ih (step_lift_prepend (reachable_in_range hwf hc hs) hstep)

/-- **`prependEntry` preserves a halting run.** -/
theorem prependEntry_preserves_halt (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ cf', Steps (prependEntry P) ⟨(prependEntry P).entry, σ⟩ cf' ∧ Final (prependEntry P) cf'
         ∧ ∀ v ∈ P.obs, cf'.store v = cf.store v := by
  have hcf : cf.node < P.size := reachable_in_range hwf hwf.entry_lt hrun
  refine ⟨cf, ?_, ?_, fun v _ => rfl⟩
  · rw [prependEntry_entry]
    exact steps_trans (steps_single (Step.noop (prependEntry_fetch_size P)))
      (steps_lift_prepend hwf hwf.entry_lt hrun)
  · show (prependEntry P).fetch cf.node = some .halt
    rw [prependEntry_fetch_lt hcf]; exact hfin

/-! ## `deDeg` — rewrite degenerate `ifz x z z` to `noop z`.

Both `ifz`-branches of a degenerate test already went to the same node `z`, so the rewritten `noop z`
reaches the *same* successor in the *same* store. Every source step maps to one target step with an
identical result config; no precondition needed (the per-node `fetch` is total via `map`). -/

/-- A source step maps to one `deDeg` step with the identical result config. -/
theorem step_lift_deDeg {c c' : Config} (h : Step P c c') : Step (deDeg P) c c' := by
  cases h with
  | assign hf hv => exact Step.assign (by rw [deDeg_fetch, hf]; simp [deDegCmd]) hv
  | @ifzT nd σ x z nz hf hz =>
      by_cases hzz : z = nz
      · subst hzz; exact Step.noop (by rw [deDeg_fetch, hf]; simp [deDegCmd])
      · have hfetch : (deDeg P).fetch nd = some (.ifz x z nz) := by
          rw [deDeg_fetch, hf]; simp only [Option.map_some, deDegCmd, if_neg hzz]
        exact Step.ifzT hfetch hz
  | @ifzF nd σ x z nz hf hz =>
      by_cases hzz : z = nz
      · subst hzz; exact Step.noop (by rw [deDeg_fetch, hf]; simp [deDegCmd])
      · have hfetch : (deDeg P).fetch nd = some (.ifz x z nz) := by
          rw [deDeg_fetch, hf]; simp only [Option.map_some, deDegCmd, if_neg hzz]
        exact Step.ifzF hfetch hz
  | noop hf => exact Step.noop (by rw [deDeg_fetch, hf]; simp [deDegCmd])

theorem steps_lift_deDeg {c c' : Config} (h : Steps P c c') : Steps (deDeg P) c c' := by
  induction h with
  | refl => exact Steps.refl
  | tail _ hstep ih => exact Steps.tail ih (step_lift_deDeg hstep)

/-- **`deDeg` preserves a halting run.** -/
theorem deDeg_preserves_halt {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ cf', Steps (deDeg P) ⟨(deDeg P).entry, σ⟩ cf' ∧ Final (deDeg P) cf'
         ∧ ∀ v ∈ P.obs, cf'.store v = cf.store v := by
  refine ⟨cf, ?_, ?_, fun v _ => rfl⟩
  · rw [deDeg_entry]; exact steps_lift_deDeg hrun
  · show (deDeg P).fetch cf.node = some .halt
    rw [deDeg_fetch, hfin]; simp [deDegCmd]

/-! ## `normalizeSelfRead` — split a self-reading compute through a fresh temp.

`x := e[x] → next` becomes `(fresh) := e[x] → c ; c: x := fresh → next`. A single source step is matched
by **two** target steps (in-place compute into the fresh temp, then the copy back into `x`), reaching
the same original node `next`. The fresh temp `freshN P nd = .tmp (tmpBound P + nd)` occurs nowhere in
`P`, so the stores stay equal off the fresh temps (`AgreeF`); observables (all `.orig`) never alias a
fresh temp, so they agree. Non-self-reading nodes keep their instruction verbatim (one matched step). -/

/-- Stores agree everywhere except (possibly) the fresh temps `freshN P i`. -/
def AgreeF (P : Program) (σT σ : Store) : Prop := ∀ v, (∀ i, v ≠ freshN P i) → σT v = σ v

theorem AgreeF.rfl' {P : Program} {σ : Store} : AgreeF P σ σ := fun _ _ => rfl

/-- A var read by an instruction of `P` is never a fresh temp. -/
theorem read_nonfresh {P : Program} {n : Node} {instr : Cmd} {v : Var}
    (hf : P.fetch n = some instr) (hv : v ∈ instrUsedVars instr) (i : Nat) : v ≠ freshN P i := by
  intro he; subst he; exact (freshN_freshForN P).unread i hf hv

/-- Under `AgreeF`, the RHS of an assignment evaluates identically (its operands are non-fresh). -/
theorem eval_agree_at {P : Program} {σT σ : Store} {n : Node} {x : Var} {e : Expr} {next : Node}
    (hag : AgreeF P σT σ) (hf : P.fetch n = some (.assign x e next)) :
    eval σT e = eval σ e :=
  eval_agree' (fun v hv => hag v (read_nonfresh hf (show v ∈ instrUsedVars (.assign x e next) from hv)))

/-! ### `normalizeSelfRead` fetch helpers (specialized to `freshN P`). -/

/-- A kept non-self-reading node keeps its instruction verbatim. -/
theorem norm_fetch_nonself {n : Node} {instr : Cmd} (hlt : n < P.size)
    (hns : n ∉ selfNodes P) (hf : P.fetch n = some instr) :
    (normalizeSelfRead P (freshN P)).fetch n = some instr := by
  rw [normalize_fetch_kept P (freshN P) hlt]
  have hcode : P.code[n]'hlt = instr := Option.some.inj ((fetch_eq_getElem hlt).symm.trans hf)
  rw [hcode]
  cases instr with
  | assign x e next =>
      simp only [normInplace]
      by_cases hsr : (isNumbered e && exprReadsVar e x) = true
      · rw [Bool.and_eq_true] at hsr
        exact absurd (mem_selfNodes_of P hlt hf hsr.1 hsr.2) hns
      · rw [if_neg hsr]
  | ifz x z nz => rfl
  | noop n => rfl
  | halt => rfl

/-- The in-place half of a self-reading node computes into the fresh temp. -/
theorem norm_fetch_self {n : Node} {x : Var} {e : Expr} {next : Node}
    (h : n ∈ selfNodes P) (hf : P.fetch n = some (.assign x e next)) :
    (normalizeSelfRead P (freshN P)).fetch n
      = some (.assign (freshN P n) e (normLabel P n)) := by
  obtain ⟨hlt, x', e', next', hf', hnum, hrd⟩ := mem_selfNodes P h
  have heq : Cmd.assign x e next = .assign x' e' next' := Option.some.inj (hf.symm.trans hf')
  injection heq with hx he hn; subst hx; subst he; subst hn
  have hcode : P.code[n]'hlt = .assign x e next :=
    Option.some.inj ((fetch_eq_getElem hlt).symm.trans hf)
  rw [normalize_fetch_kept P (freshN P) hlt, hcode]
  simp only [normInplace, if_pos (show (isNumbered e && exprReadsVar e x) = true by simp [hnum, hrd])]

/-- The copy half of a self-reading node copies the fresh temp back into `x`. -/
theorem norm_fetch_copy {n : Node} {x : Var} {e : Expr} {next : Node}
    (h : n ∈ selfNodes P) (hf : P.fetch n = some (.assign x e next)) :
    (normalizeSelfRead P (freshN P)).fetch (normLabel P n)
      = some (.assign x (.atom (.var (freshN P n))) next) := by
  rw [fetch_normLabel P (freshN P) h]; unfold normCopy; rw [hf]

/-- A node carrying a non-`assign` instruction is not self-reading. -/
theorem not_self_of_ne_assign {n : Node} {instr : Cmd}
    (hf : P.fetch n = some instr) (hna : ∀ x e next, instr ≠ .assign x e next) :
    n ∉ selfNodes P := by
  intro hmem; obtain ⟨_, x, e, next, hf', _, _⟩ := mem_selfNodes P hmem
  rw [hf] at hf'; injection hf' with hf'; exact hna x e next hf'

/-- **Single-step diagram.** One source step at an in-range node is matched by ≥1 `normalizeSelfRead`
    steps reaching the same successor node, preserving `AgreeF`. -/
theorem selfread_step_sim {cmid c : Config} {σT : Store}
    (hlt : cmid.node < P.size) (hag : AgreeF P σT cmid.store) (hstep : Step P cmid c) :
    ∃ σT', Steps (normalizeSelfRead P (freshN P)) ⟨cmid.node, σT⟩ ⟨c.node, σT'⟩
         ∧ AgreeF P σT' c.store := by
  cases hstep with
  | @assign nd σ x e next v hf hv =>
      have hev : eval σT e = some v := by rw [eval_agree_at hag hf]; exact hv
      by_cases hsr : (isNumbered e && exprReadsVar e x) = true
      · -- self-reading: two steps through the copy node
        rw [Bool.and_eq_true] at hsr
        have hmem : nd ∈ selfNodes P := mem_selfNodes_of P hlt hf hsr.1 hsr.2
        have hstep1 : Step (normalizeSelfRead P (freshN P))
            ⟨nd, σT⟩ ⟨normLabel P nd, σT.update (freshN P nd) v⟩ :=
          Step.assign (norm_fetch_self hmem hf) hev
        have hev2 : eval (σT.update (freshN P nd) v) (.atom (.var (freshN P nd))) = some v := by
          show some ((σT.update (freshN P nd) v) (freshN P nd)) = some v
          rw [upd_self]
        have hstep2 : Step (normalizeSelfRead P (freshN P))
            ⟨normLabel P nd, σT.update (freshN P nd) v⟩
            ⟨next, (σT.update (freshN P nd) v).update x v⟩ :=
          Step.assign (norm_fetch_copy hmem hf) hev2
        refine ⟨(σT.update (freshN P nd) v).update x v,
          steps_trans (steps_single hstep1) (steps_single hstep2), ?_⟩
        intro w hw
        show ((σT.update (freshN P nd) v).update x v) w = (σ.update x v) w
        by_cases hwx : w = x
        · subst hwx; rw [upd_self, upd_self]
        · rw [upd_ne hwx, upd_ne (hw nd), upd_ne hwx]; exact hag w hw
      · -- non-self-reading assign: one step verbatim
        have hns : nd ∉ selfNodes P := by
          intro hmem
          obtain ⟨_, x', e', next', hf', hnum', hrd'⟩ := mem_selfNodes P hmem
          have heq : Cmd.assign x e next = .assign x' e' next' := Option.some.inj (hf.symm.trans hf')
          injection heq with hx he hn; subst hx; subst he; subst hn
          exact hsr (by rw [Bool.and_eq_true]; exact ⟨hnum', hrd'⟩)
        refine ⟨σT.update x v, steps_single (Step.assign (norm_fetch_nonself hlt hns hf) hev), ?_⟩
        intro w hw
        show (σT.update x v) w = (σ.update x v) w
        by_cases hwx : w = x
        · subst hwx; rw [upd_self, upd_self]
        · rw [upd_ne hwx, upd_ne hwx]; exact hag w hw
  | @ifzT nd σ x z nz hf hz =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      have hzt : σT x = 0 := by rw [hag x (read_nonfresh hf (by simp [instrUsedVars]))]; exact hz
      exact ⟨σT, steps_single (Step.ifzT (norm_fetch_nonself hlt hns hf) hzt), hag⟩
  | @ifzF nd σ x z nz hf hz =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      have hzt : σT x ≠ 0 := by rw [hag x (read_nonfresh hf (by simp [instrUsedVars]))]; exact hz
      exact ⟨σT, steps_single (Step.ifzF (norm_fetch_nonself hlt hns hf) hzt), hag⟩
  | @noop nd σ next hf =>
      have hns : nd ∉ selfNodes P := not_self_of_ne_assign hf (by intro x e next; simp)
      exact ⟨σT, steps_single (Step.noop (norm_fetch_nonself hlt hns hf)), hag⟩

/-- A whole halting source run lifts into a `normalizeSelfRead` run reaching the same node. -/
theorem selfread_steps_sim (hwf : WellFormed P) {σ : Store} {c : Config}
    (h : Steps P ⟨P.entry, σ⟩ c) :
    ∃ σT', Steps (normalizeSelfRead P (freshN P)) ⟨P.entry, σ⟩ ⟨c.node, σT'⟩
         ∧ AgreeF P σT' c.store := by
  induction h with
  | refl => exact ⟨σ, Steps.refl, AgreeF.rfl'⟩
  | tail hs hstep ih =>
      obtain ⟨σTmid, hsteps, hag⟩ := ih
      obtain ⟨σTf, hsteps2, hagf⟩ :=
        selfread_step_sim (reachable_in_range hwf hwf.entry_lt hs) hag hstep
      exact ⟨σTf, steps_trans hsteps hsteps2, hagf⟩

/-- **`normalizeSelfRead` preserves a halting run** (observables all-`.orig` so they avoid fresh temps). -/
theorem normalizeSelfRead_preserves_halt (hwf : WellFormed P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ cf', Steps (normalizeSelfRead P (freshN P))
              ⟨(normalizeSelfRead P (freshN P)).entry, σ⟩ cf'
         ∧ Final (normalizeSelfRead P (freshN P)) cf'
         ∧ ∀ v ∈ P.obs, cf'.store v = cf.store v := by
  obtain ⟨σT', hsteps, hag⟩ := selfread_steps_sim hwf hrun
  have hcf : cf.node < P.size := reachable_in_range hwf hwf.entry_lt hrun
  have hns : cf.node ∉ selfNodes P := not_self_of_ne_assign hfin (by intro x e next; simp)
  refine ⟨⟨cf.node, σT'⟩, hsteps, norm_fetch_nonself hcf hns hfin, ?_⟩
  intro v hv
  refine hag v (fun i he => ?_)
  have h1 := hobs v hv
  rw [he, freshN_nonobs P i] at h1
  simp at h1

/-! ## Composition — `normalize_preserves_halt`.

`normalize = prependEntry ∘ deDeg ∘ normalizeSelfRead` (each pass keeps `obs`),
so the three `*_preserves_halt` lemmas chain: each output is `WellFormed` (the existing structural
lemmas), and the observable agreement composes transitively on the shared `obs` set. -/

/-- **`normalize` preserves a halting run.** On a terminating source run, the normalized program halts
    from its entry agreeing with the source on every observable. (Needs `WellFormed P` and that the
    observables are source vars — the same inputs the optimizer pipeline already assumes.) -/
theorem normalize_preserves_halt (hwf : WellFormed P)
    (hobs : ∀ v ∈ P.obs, varIsOrig v = true) {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ cf', Steps (normalize P) ⟨(normalize P).entry, σ⟩ cf'
         ∧ Final (normalize P) cf' ∧ ∀ v ∈ P.obs, cf'.store v = cf.store v := by
  obtain ⟨cf1, hr1, hfin1, ho1⟩ := normalizeSelfRead_preserves_halt hwf hobs hrun hfin
  have hwf1 : WellFormed (normalizeSelfRead P (freshN P)) := normalize_wellFormed P (freshN P) hwf
  obtain ⟨cf2, hr2, hfin2, ho2⟩ :=
    deDeg_preserves_halt (P := normalizeSelfRead P (freshN P)) hr1 hfin1
  have hwf2 : WellFormed (deDeg (normalizeSelfRead P (freshN P))) := deDeg_wellFormed _ hwf1
  obtain ⟨cf3, hr3, hfin3, ho3⟩ :=
    prependEntry_preserves_halt (P := deDeg (normalizeSelfRead P (freshN P))) hwf2 hr2 hfin2
  refine ⟨cf3, hr3, hfin3, ?_⟩
  intro v hv
  rw [ho3 v hv, ho2 v hv, ho1 v hv]

/-- **The normalized entry is a `noop`** (the `prependEntry` `noop`). This is the LCM optimizer's
    `hen` precondition. -/
theorem normalize_entry_noop (P : Program) :
    ∃ ne, (normalize P).fetch (normalize P).entry = some (.noop ne) := by
  refine ⟨(deDeg (normalizeSelfRead P (freshN P))).entry, ?_⟩
  show (prependEntry (deDeg (normalizeSelfRead P (freshN P)))).fetch
        (prependEntry (deDeg (normalizeSelfRead P (freshN P)))).entry
      = some (.noop _)
  rw [prependEntry_entry, prependEntry_fetch_size _]

end Normalize
end BaseLanguage
