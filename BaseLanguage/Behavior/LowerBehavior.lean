-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.Correctness.AstToTacCorrect
import BaseLanguage.Behavior.Outcomes

namespace BaseLanguage

/-!
# `Behavior/LowerBehavior.lean` — `lower` preserves **fault & divergence**

The full-behavioral-preservation theory: the big-step/fuel source semantics `Ast.evalS` and the
small-step IR `Semantics.Step` agree on
*divergence*. Concretely, if the reference interpreter times out at **every** loop-fuel
(`∀ fuel, evalS fuel s σ = .timeout` — the honest divergence predicate, well-defined by
`Ast.evalS_mono`), then the lowered CFG `lower s` runs forever (`Semantics.Diverges`).

The proof is a **plus-simulation step-count argument, with no well-founded measure**: one unit of
source loop-fuel maps to ≥ 1 IR steps (a loop back-edge is ≥ 1 step), so a source run that survives
`fuel` iterations forces an IR run still live after ≥ `fuel` steps. The `RunsFor`/`runsFor_of_steps`
toolkit (in `Behavior.Outcomes`) turns "survives `fuel` iterations" into "IR still `.next` after `fuel`
steps", and `Diverges` follows because `fuel` is unbounded. Straight-line prefixes (condition/body
evaluation) are spliced in from the *existing* halting simulations `layC_correct`/`layS_correct` — this
file only **uses** the audited lowering proofs, never edits them.
-/

namespace AstToTac

open Tac Ast Semantics

/-! ## Fault simulation — a source fault reaches an IR `Faulting` config

`evalE`/`evalS` return `none`/`.fault` exactly on a `div`/`mod`-by-zero. The lowered code evaluates
left-to-right, so it steps through the (non-faulting) prefix and then sits on the very `.assign` whose
right-hand side faults — an IR `Faulting` config. These mirror the `_correct` simulations but stop at
the fault instead of running to the continuation; the non-faulting prefixes reuse the `_correct` runs. -/

/-- **`layE` fault.** A faulting sub-expression drives the lowered `layE` block from its entry to a
    `Faulting` config. -/
theorem layE_fault {P : Program} :
    ∀ (e : Ast.Expr) {cont b : Nat} {σT σ : Store},
      Expr.noTmp e →
      CodeAt P b (layE e cont b).1 →
      AgreeOrig σT σ →
      evalE σ e = none →
    ∃ cf, Steps P ⟨(layE e cont b).2.2, σT⟩ cf ∧ Faulting P cf := by
  intro e
  induction e with
  | atom a => intro cont b σT σ _ _ _ hv; simp [evalE] at hv
  | una op e ih =>
      intro cont b σT σ hnt hcode hag hv
      simp only [layE] at hcode ⊢
      have hcode_e : CodeAt P b (layE e (b + szE e) b).1 := hcode.append_left
      have hv' : evalE σ e = none := by simp only [evalE, Option.map_eq_none_iff] at hv; exact hv
      exact ih (cont := b + szE e) (b := b) hnt hcode_e hag hv'
  | bin op e₁ e₂ ih₁ ih₂ =>
      intro cont b σT σ hnt hcode hag hv
      obtain ⟨hnt₁, hnt₂⟩ := hnt
      simp only [layE] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcode₁ : CodeAt P b
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1 := hcode.append_left
      have hBC := hcode.append_right
        (l₁ := (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1)
      rw [layE_len] at hBC
      have hcode₂ : CodeAt P (b + szE e₁) (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1 :=
        hBC.append_left
      cases hee₁ : evalE σ e₁ with
      | none => exact ih₁ (b := b) hnt₁ hcode₁ hag hee₁
      | some a =>
          obtain ⟨σ1, hsteps1, hag1, hfr1, hval1⟩ :=
            layE_correct e₁ (b := b) hnt₁ hcode₁ hag hee₁
          cases hee₂ : evalE σ e₂ with
          | none =>
              obtain ⟨cf, hcf, hfcf⟩ :=
                ih₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
              exact ⟨cf, Steps.trans hsteps1 hcf, hfcf⟩
          | some b' =>
              have hden : op.denote a b' = none := by simp only [evalE, hee₁, hee₂] at hv; exact hv
              obtain ⟨σ2, hsteps2, hag2, hfr2, hval2⟩ :=
                layE_correct e₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
              have hassign : P.fetch (b + szE e₁ + szE e₂)
                  = some (.assign (.tmp (b + szE e₁ + szE e₂))
                      (.bin op (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
                               (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) cont) := by
                have hC := hBC.append_right (l₁ := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1)
                rw [layE_len] at hC; exact hC.head
              have hstable₁ : AtomStable (b + szE e₁)
                  (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 :=
                layE_result_stable e₁ _ b hnt₁
              have hval1' : Semantics.evalAtom σ2
                  (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 = a := by
                rw [evalAtom_frame hfr2 hstable₁]; exact hval1
              refine ⟨⟨b + szE e₁ + szE e₂, σ2⟩, Steps.trans hsteps1 hsteps2,
                ⟨_, _, _, hassign, ?_⟩⟩
              simp only [Semantics.eval, hval1', hval2]; exact hden

/-- **`layI` fault.** Same, for `layI` (result written into `x`). -/
theorem layI_fault {P : Program} (x : Var) :
    ∀ (e : Ast.Expr) {cont b : Nat} {σT σ : Store},
      Expr.noTmp e →
      CodeAt P b (layI x e cont b).1 →
      AgreeOrig σT σ →
      evalE σ e = none →
    ∃ cf, Steps P ⟨(layI x e cont b).2, σT⟩ cf ∧ Faulting P cf := by
  intro e
  cases e with
  | atom a => intro cont b σT σ _ _ _ hv; simp [evalE] at hv
  | una op e =>
      intro cont b σT σ hnt hcode hag hv
      simp only [layI] at hcode ⊢
      have hcode_e : CodeAt P b (layE e (b + szE e) b).1 := hcode.append_left
      have hv' : evalE σ e = none := by simp only [evalE, Option.map_eq_none_iff] at hv; exact hv
      exact layE_fault e (cont := b + szE e) (b := b) hnt hcode_e hag hv'
  | bin op e₁ e₂ =>
      intro cont b σT σ hnt hcode hag hv
      obtain ⟨hnt₁, hnt₂⟩ := hnt
      simp only [layI] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcode₁ : CodeAt P b
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1 := hcode.append_left
      have hBC := hcode.append_right
        (l₁ := (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1)
      rw [layE_len] at hBC
      have hcode₂ : CodeAt P (b + szE e₁) (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1 :=
        hBC.append_left
      cases hee₁ : evalE σ e₁ with
      | none => exact layE_fault e₁ (b := b) hnt₁ hcode₁ hag hee₁
      | some a =>
          obtain ⟨σ1, hsteps1, hag1, hfr1, hval1⟩ :=
            layE_correct e₁ (b := b) hnt₁ hcode₁ hag hee₁
          cases hee₂ : evalE σ e₂ with
          | none =>
              obtain ⟨cf, hcf, hfcf⟩ :=
                layE_fault e₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
              exact ⟨cf, Steps.trans hsteps1 hcf, hfcf⟩
          | some b' =>
              have hden : op.denote a b' = none := by simp only [evalE, hee₁, hee₂] at hv; exact hv
              obtain ⟨σ2, hsteps2, hag2, hfr2, hval2⟩ :=
                layE_correct e₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
              have hassign : P.fetch (b + szE e₁ + szE e₂)
                  = some (.assign x
                      (.bin op (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
                               (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) cont) := by
                have hC := hBC.append_right (l₁ := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1)
                rw [layE_len] at hC; exact hC.head
              have hstable₁ : AtomStable (b + szE e₁)
                  (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 :=
                layE_result_stable e₁ _ b hnt₁
              have hval1' : Semantics.evalAtom σ2
                  (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 = a := by
                rw [evalAtom_frame hfr2 hstable₁]; exact hval1
              refine ⟨⟨b + szE e₁ + szE e₂, σ2⟩, Steps.trans hsteps1 hsteps2,
                ⟨_, _, _, hassign, ?_⟩⟩
              simp only [Semantics.eval, hval1', hval2]; exact hden

/-- **`layC` fault.** A faulting condition drives `layC`'s materialisation block to a `Faulting`. -/
theorem layC_fault {P : Program} :
    ∀ (c : Ast.Expr) {cont b : Nat} {σT σ : Store},
      Expr.noTmp c →
      CodeAt P b (layC c cont b).2.1 →
      AgreeOrig σT σ →
      evalE σ c = none →
    ∃ cf, Steps P ⟨(layC c cont b).2.2, σT⟩ cf ∧ Faulting P cf := by
  intro c
  cases c with
  | atom a =>
      cases a with
      | var x => intro cont b σT σ _ _ _ hv; simp [evalE] at hv
      | imm n => intro cont b σT σ _ _ _ hv; simp [evalE] at hv
  | una op e =>
      intro cont b σT σ hnt hcode hag hv
      simp only [layC] at hcode ⊢
      exact layI_fault (.tmp b) (.una op e) hnt hcode hag hv
  | bin op e₁ e₂ =>
      intro cont b σT σ hnt hcode hag hv
      simp only [layC] at hcode ⊢
      exact layI_fault (.tmp b) (.bin op e₁ e₂) hnt hcode hag hv

/-- **Fault simulation for `layS`.** If `evalS fuel s σ = .fault`, the lowered block steps from its
    entry to a `Faulting` config. Proved by `evalS.induct`, mirroring `layS_correct` but ending at the
    fault; non-faulting prefixes reuse `layS_correct`/`layC_correct`. -/
theorem layS_fault {P : Program} (fuel : Nat) (s : Stmt) (σ : Store) :
    ∀ {cont b : Nat} {σT : Store},
      Stmt.noTmp s →
      CodeAt P b (layS s cont b).1 →
      AgreeOrig σT σ →
      evalS fuel s σ = .fault →
    ∃ cf, Steps P ⟨(layS s cont b).2, σT⟩ cf ∧ Faulting P cf := by
  induction fuel, s, σ using evalS.induct with
  | case1 fuel σ => intro cont b σT _ _ _ hev; simp only [evalS] at hev; exact absurd hev (by simp)
  | case2 fuel xv e σ bv heq =>
      intro cont b σT _ _ _ hev; simp only [evalS, heq] at hev; exact absurd hev (by simp)
  | case3 fuel xv e σ heq =>   -- assign whose rhs faults
      intro cont b σT hnt hcode hag _
      obtain ⟨_, hnte⟩ := hnt
      simp only [layS] at hcode ⊢
      exact layI_fault xv e hnte hcode hag heq
  | case4 fuel s1 s2 σ σmid hmid ih1 ih2 =>   -- seq, first ok — fault in s2
      intro cont b σT hnt hcode hag hev
      obtain ⟨hnt1, hnt2⟩ := hnt
      simp only [evalS, hmid] at hev
      simp only [layS] at hcode ⊢
      have hcode1 : CodeAt P b (layS s1 (layS s2 cont (b + szS s1)).2 b).1 := hcode.append_left
      have hcode2 := hcode.append_right (l₁ := (layS s1 (layS s2 cont (b + szS s1)).2 b).1)
      rw [layS_len] at hcode2
      obtain ⟨σ1, hs1, hag1⟩ := layS_correct fuel s1 σ hnt1 hcode1 hag hmid
      obtain ⟨cf, hcf, hfcf⟩ := ih2 hnt2 hcode2 hag1 hev
      exact ⟨cf, Steps.trans hs1 hcf, hfcf⟩
  | case5 fuel s1 s2 σ hfail ih1 =>   -- seq, first not ok — must be s1 faulting
      intro cont b σT hnt hcode hag hev
      obtain ⟨hnt1, _⟩ := hnt
      simp only [evalS] at hev
      simp only [layS] at hcode ⊢
      have hcode1 : CodeAt P b (layS s1 (layS s2 cont (b + szS s1)).2 b).1 := hcode.append_left
      cases hm : evalS fuel s1 σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault => exact ih1 hnt1 hcode1 hag hm
      | timeout => rw [hm] at hev; simp at hev
  | case6 fuel c t e σ bv heq hz ihe =>   -- ite, cond = 0 — fault in else
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, _, hnte⟩ := hnt
      simp only [evalS, heq, hz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc, List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBCD := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBCD
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1
          (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2) := hBCD.head
      have hCD := hBCD.tail
      have hcodeE0 := hCD.append_right (l₁ := (layS t cont (b + szC c + 1)).1)
      rw [layS_len] at hcodeE0
      have hcz : σTc (layC c (b + szC c) b).1 = 0 := by rw [hxc]; exact eq_of_beq hz
      obtain ⟨cf, hcf, hfcf⟩ := ihe hnte hcodeE0 hagc hev
      exact ⟨cf, Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzT hifz hcz)) hcf), hfcf⟩
  | case7 fuel c t e σ bv heq hnz iht =>   -- ite, cond ≠ 0 — fault in then
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntt, _⟩ := hnt
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc, List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBCD := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBCD
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1
          (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2) := hBCD.head
      have hCD := hBCD.tail
      have hcodeT0 := hCD.append_left (l₁ := (layS t cont (b + szC c + 1)).1)
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      obtain ⟨cf, hcf, hfcf⟩ := iht hntt hcodeT0 hagc hev
      exact ⟨cf, Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzF hifz hcne)) hcf), hfcf⟩
  | case8 fuel c t e σ heq =>   -- ite, cond faults
      intro cont b σT hnt hcode hag _
      obtain ⟨hntc, _, _⟩ := hnt
      simp only [layS] at hcode ⊢
      rw [List.append_assoc, List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      exact layC_fault c hntc hcodeC hag heq
  | case9 c bd σ => intro cont b σT _ _ _ hev; simp only [evalS] at hev; exact absurd hev (by simp)
  | case10 fuel c bd σ bv heq hz =>
      intro cont b σT _ _ _ hev; simp only [evalS, heq, hz] at hev; exact absurd hev (by simp)
  | case11 fuel c bd σ bv heq hnz σmid hbody ihb ihw =>   -- while iterate — fault on a later iteration
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      have hcode0 := hcode
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz, hbody] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBC := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBC
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1 cont
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).2) := hBC.head
      have hcodeB : CodeAt P (b + szC c + 1)
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).1 := hBC.tail
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      obtain ⟨σ1, hsB, hag1⟩ := layS_correct fuel bd σ hntb hcodeB hagc hbody
      obtain ⟨cf, hcf, hfcf⟩ := ihw ⟨hntc, hntb⟩ hcode0 hag1 hev
      exact ⟨cf, Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzF hifz hcne))
        (Steps.trans hsB hcf)), hfcf⟩
  | case12 fuel c bd σ bv heq hnz hfail ihb =>   -- while, body not ok — fault in body
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBC := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBC
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1 cont
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).2) := hBC.head
      have hcodeB : CodeAt P (b + szC c + 1)
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).1 := hBC.tail
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      cases hm : evalS fuel bd σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault =>
          obtain ⟨cf, hcf, hfcf⟩ := ihb hntb hcodeB hagc hm
          exact ⟨cf, Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzF hifz hcne)) hcf), hfcf⟩
      | timeout => rw [hm] at hev; simp at hev
  | case13 fuel c bd σ heq =>   -- while, cond faults
      intro cont b σT hnt hcode hag _
      obtain ⟨hntc, _⟩ := hnt
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      exact layC_fault c hntc hcodeC hag heq

/-- **`lower` preserves faults, in composable form:** a source fault drives the lowered program from
    its entry to a `Faulting` config (threadable through the later IR passes). -/
theorem lower_faultSteps (s : Stmt) (fuel : Nat) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .fault) :
    ∃ cf, Steps (lower s) ⟨(lower s).entry, Store.init⟩ cf ∧ Faulting (lower s) cf := by
  obtain ⟨cf, hsteps, hflt⟩ :=
    layS_fault fuel s Store.init (cont := 0) (b := 1) (σT := Store.init)
      hnt (lower_codeAt s) (fun _ => rfl) h
  have he : (lower s).entry = (layS s 0 1).2 := rfl
  exact ⟨cf, by rw [he]; exact hsteps, hflt⟩

/-- **`lower` preserves faults.** If the reference interpreter faults at some fuel, the lowered program
    reaches a `Faulting` config from its entry (hence IR-`Faults`). -/
theorem lower_faults (s : Stmt) (fuel : Nat) (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .fault) :
    Semantics.Faults (lower s) ⟨(lower s).entry, Store.init⟩ := by
  obtain ⟨cf, hsteps, hflt⟩ := lower_faultSteps s fuel hnt h
  exact faults_of_steps_faulting hsteps hflt

/-- **Divergence simulation for `layS`.** If `evalS fuel s σ = .timeout` (the source ran out of loop
    fuel), then the lowered block, started at its entry in an agreeing store, is **still running after
    `fuel` IR steps** (`RunsFor`). Proved by `evalS.induct`, mirroring `layS_correct`'s decomposition
    but concluding a step-count lower bound instead of a halting run. Terminating shapes
    (skip/assign/exit/faults) make the `= .timeout` hypothesis contradictory. -/
theorem layS_diverge {P : Program} (fuel : Nat) (s : Stmt) (σ : Store) :
    ∀ {cont b : Nat} {σT : Store},
      Stmt.noTmp s →
      CodeAt P b (layS s cont b).1 →
      AgreeOrig σT σ →
      evalS fuel s σ = .timeout →
    RunsFor P ⟨(layS s cont b).2, σT⟩ fuel := by
  induction fuel, s, σ using evalS.induct with
  | case1 fuel σ =>   -- skip (terminates)
      intro cont b σT _ _ _ hev; simp only [evalS] at hev; exact absurd hev (by simp)
  | case2 fuel xv e σ bv heq =>   -- assign, ok (terminates)
      intro cont b σT _ _ _ hev; simp only [evalS, heq] at hev; exact absurd hev (by simp)
  | case3 fuel xv e σ heq =>   -- assign, fault (terminates)
      intro cont b σT _ _ _ hev; simp only [evalS, heq] at hev; exact absurd hev (by simp)
  | case4 fuel s1 s2 σ σmid hmid ih1 ih2 =>   -- seq, first ok — divergence is in s2
      intro cont b σT hnt hcode hag hev
      obtain ⟨hnt1, hnt2⟩ := hnt
      simp only [evalS, hmid] at hev
      simp only [layS] at hcode ⊢
      have hcode1 : CodeAt P b (layS s1 (layS s2 cont (b + szS s1)).2 b).1 := hcode.append_left
      have hcode2 := hcode.append_right (l₁ := (layS s1 (layS s2 cont (b + szS s1)).2 b).1)
      rw [layS_len] at hcode2
      obtain ⟨σ1, hs1, hag1⟩ := layS_correct fuel s1 σ hnt1 hcode1 hag hmid
      exact runsFor_of_steps hs1 (ih2 hnt2 hcode2 hag1 hev)
  | case5 fuel s1 s2 σ hfail ih1 =>   -- seq, first not ok — must be s1 timing out
      intro cont b σT hnt hcode hag hev
      obtain ⟨hnt1, _⟩ := hnt
      simp only [evalS] at hev
      simp only [layS] at hcode ⊢
      have hcode1 : CodeAt P b (layS s1 (layS s2 cont (b + szS s1)).2 b).1 := hcode.append_left
      cases hm : evalS fuel s1 σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault => rw [hm] at hev; simp at hev
      | timeout => exact ih1 hnt1 hcode1 hag hm
  | case6 fuel c t e σ bv heq hz ihe =>   -- ite, cond = 0 (else branch diverges)
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, _, hnte⟩ := hnt
      simp only [evalS, heq, hz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc, List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBCD := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBCD
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1
          (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2) := hBCD.head
      have hCD := hBCD.tail
      have hcodeE0 := hCD.append_right (l₁ := (layS t cont (b + szC c + 1)).1)
      rw [layS_len] at hcodeE0
      have hcz : σTc (layC c (b + szC c) b).1 = 0 := by rw [hxc]; exact eq_of_beq hz
      exact runsFor_of_steps (Steps.trans hsC (Steps.singleton (Step.ifzT hifz hcz)))
        (ihe hnte hcodeE0 hagc hev)
  | case7 fuel c t e σ bv heq hnz iht =>   -- ite, cond ≠ 0 (then branch diverges)
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntt, _⟩ := hnt
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc, List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBCD := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBCD
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1
          (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2) := hBCD.head
      have hCD := hBCD.tail
      have hcodeT0 := hCD.append_left (l₁ := (layS t cont (b + szC c + 1)).1)
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      exact runsFor_of_steps (Steps.trans hsC (Steps.singleton (Step.ifzF hifz hcne)))
        (iht hntt hcodeT0 hagc hev)
  | case8 fuel c t e σ heq =>   -- ite, cond faults (terminates)
      intro cont b σT _ _ _ hev; simp only [evalS, heq] at hev; exact absurd hev (by simp)
  | case9 c bd σ =>   -- while, fuel = 0 (still running: 0 steps)
      intro cont b σT _ _ _ _; exact ⟨_, rfl⟩
  | case10 fuel c bd σ bv heq hz =>   -- while, cond = 0 (exit — terminates)
      intro cont b σT _ _ _ hev; simp only [evalS, heq, hz] at hev; exact absurd hev (by simp)
  | case11 fuel c bd σ bv heq hnz σmid hbody ihb ihw =>   -- while, iterate (loop back-edge ≥ 1 step)
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      have hcode0 := hcode
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz, hbody] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBC := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBC
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1 cont
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).2) := hBC.head
      have hcodeB : CodeAt P (b + szC c + 1)
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).1 := hBC.tail
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      -- run condition, take the back-edge into the body, run the body to the loop head, then loop.
      -- the `ifzF` back-edge is the one guaranteed step that bumps the count `fuel → fuel + 1`.
      obtain ⟨σ1, hsB, hag1⟩ := layS_correct fuel bd σ hntb hcodeB hagc hbody
      refine runsFor_of_steps hsC
        (runsFor_step (step1_next_iff.mpr (Step.ifzF hifz hcne)) ?_)
      exact runsFor_of_steps hsB (ihw ⟨hntc, hntb⟩ hcode0 hag1 hev)
  | case12 fuel c bd σ bv heq hnz hfail ihb =>   -- while, body not ok — body times out
      intro cont b σT hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz] at hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBC := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBC
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1 cont
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).2) := hBC.head
      have hcodeB : CodeAt P (b + szC c + 1)
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).1 := hBC.tail
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      cases hm : evalS fuel bd σ with
      | ok σmid => exact absurd hm (hfail σmid)
      | fault => rw [hm] at hev; simp at hev
      | timeout =>
          exact runsFor_of_steps hsC
            (runsFor_step (step1_next_iff.mpr (Step.ifzF hifz hcne)) (ihb hntb hcodeB hagc hm))
  | case13 fuel c bd σ heq =>   -- while, cond faults (terminates)
      intro cont b σT _ _ _ hev; simp only [evalS, heq] at hev; exact absurd hev (by simp)

/-- **`lower` preserves divergence.** If the reference interpreter times out at every loop-fuel, the
    lowered program runs forever from its entry. -/
theorem lower_diverges (s : Stmt) (hnt : Stmt.noTmp s)
    (h : ∀ fuel, Ast.evalS fuel s Store.init = .timeout) :
    Semantics.Diverges (lower s) ⟨(lower s).entry, Store.init⟩ := by
  apply diverges_of_runsFor
  intro n
  have hrf := layS_diverge n s Store.init (cont := 0) (b := 1) (σT := Store.init)
    hnt (lower_codeAt s) (fun _ => rfl) (h n)
  have he : (lower s).entry = (layS s 0 1).2 := rfl
  rw [he]; exact hrf

end AstToTac

end BaseLanguage
