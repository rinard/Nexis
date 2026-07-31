-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Correctness.CodegenBinop
import BaseLanguage.Backend.Correctness.CodegenExpr

namespace BaseLanguage

/-!
# `CodegenEmit` — expression-emission simulation (`emitExpr_correct`)

Item 1 of the forward simulation: running the `emitExpr` instructions evaluates the IR expression into `x9`.
Builds on `loadAtom_correct` (atom load) and the `CodegenBinop` value layer (every `Binop` computes
`encode (Binop.denote · a b)`), composing the per-instruction steps with `run_running_add`.

The non-faulting cases leave `encode (eval σ e)` in `x9` with the frame untouched and the pc advanced by
`(emitExpr …).length`. The faulting case (only `div`/`mod` by a zero divisor) reaches the fault block via the
emitted `cbz x10, faultPc` and faults.
-/

namespace Asm

/-- `prog` contains the instruction list `l` at consecutive pcs from `p`. -/
def Embeds (prog : Prog) (p : Nat) (l : List Cmd) : Prop :=
  ∀ k, k < l.length → prog[p + k]? = l[k]?

theorem Embeds.head {prog : Prog} {p : Nat} {i : Cmd} {l : List Cmd}
    (h : Embeds prog p (i :: l)) : prog[p]? = some i := by
  have := h 0 (by simp); simpa using this

theorem Embeds.get0 {prog : Prog} {p : Nat} {l : List Cmd}
    (h : Embeds prog p l) (hl : 0 < l.length) : prog[p]? = l[0]? := by
  have := h 0 hl; rwa [Nat.add_zero] at this

theorem Embeds.tail {prog : Prog} {p : Nat} {i : Cmd} {l : List Cmd}
    (h : Embeds prog p (i :: l)) : Embeds prog (p + 1) l := by
  intro k hk
  have := h (k + 1) (by simp only [List.length_cons]; omega)
  rwa [show p + (k + 1) = p + 1 + k from by omega, List.getElem?_cons_succ] at this

theorem Embeds.append_left {prog : Prog} {p : Nat} {l₁ l₂ : List Cmd}
    (h : Embeds prog p (l₁ ++ l₂)) : Embeds prog p l₁ := by
  intro k hk
  have := h k (by rw [List.length_append]; omega)
  rwa [List.getElem?_append_left hk] at this

theorem Embeds.append_right {prog : Prog} {p : Nat} {l₁ l₂ : List Cmd}
    (h : Embeds prog p (l₁ ++ l₂)) : Embeds prog (p + l₁.length) l₂ := by
  intro k hk
  have := h (l₁.length + k) (by rw [List.length_append]; omega)
  rw [show p + (l₁.length + k) = p + l₁.length + k from by omega,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  exact this

/-- Running `a` `cont`-steps to a `running` state composes with a further run. -/
theorem run_running_add {prog : Prog} {s s' : State} (a b : Nat)
    (h : run prog a s = .running s') : run prog (a + b) s = run prog b s' := by
  induction a generalizing s with
  | zero => simp only [run] at h; rw [Nat.zero_add]; cases h; rfl
  | succ n ih =>
      rw [Nat.succ_add]
      cases hs : step prog s with
      | cont s1 => rw [run_one_cont n hs] at h; rw [run_one_cont (n + b) hs]; exact ih h
      | halt s1 => simp [run, hs] at h
      | fault => simp [run, hs] at h

/-- A register write to `r ≠ 9` preserves `x9`. -/
theorem get9_set_ne (s : State) (r : Nat) (x : Word) (h : r ≠ 9) : (s.set r x).get 9 = s.get 9 :=
  get_set_ne s r 9 x (by omega)

end Asm

namespace TacToAsm

open Tac Semantics Asm

/-- The `unArm` op applied to `x9 = encode v` leaves `encode (Unop.denote op v)` in `x9`. -/
theorem unArm_correct {prog : Asm.Prog} {op : Unop} {v : Val} {s : Asm.State}
    (hi : prog[s.pc]? = (unArm op)[0]?) (h9 : s.get 9 = encode v) :
    Asm.run prog 1 s = .running ((s.set 9 (encode (Unop.denote op v))).next) := by
  cases op with
  | neg =>
    have hi' : prog[s.pc]? = some (.neg 9 9) := hi
    have : Asm.step prog s = .cont ((s.set 9 (- s.get 9)).next) := by simp only [Asm.step, hi']
    rw [Asm.run_one_cont 0 this, h9]; rfl
  | not =>
    have hi' : prog[s.pc]? = some (.mvn 9 9) := hi
    have : Asm.step prog s = .cont ((s.set 9 (~~~ s.get 9)).next) := by simp only [Asm.step, hi']
    rw [Asm.run_one_cont 0 this, h9]; rfl

/-- A single-`alu` `binArm` op (`add/sub/mul/and/or/xor/shl/lshr/ashr`) on `x9 = encode va`, `x10 = encode vb`
    leaves `encode (the result)` in `x9` after one step. The result value comes from the `CodegenBinop`/
    `CodegenCorrect` `alu`/`shift` value lemmas. -/
theorem alu_step {prog : Asm.Prog} {aluop : Asm.ALU} {va vb : Val} {res : Word} {s : Asm.State}
    (hi : prog[s.pc]? = some (.alu aluop 9 9 10)) (h9 : s.get 9 = encode va) (h10 : s.get 10 = encode vb)
    (hres : aluEval aluop (encode va) (encode vb) = res) :
    Asm.run prog 1 s = .running ((s.set 9 res).next) := by
  have hstep : Asm.step prog s = .cont ((s.set 9 (aluEval aluop (s.get 9) (s.get 10))).next) := by
    simp only [Asm.step, hi]
  rw [Asm.run_one_cont 0 hstep, h9, h10, hres]; rfl

/-- A comparison `binArm` op (`cmp x9,x10 ; cset x9,c`) on `x9 = encode va`, `x10 = encode vb` leaves
    `csetVal c va vb` (= `encode (the comparison result)`, via the `cset_*` value lemmas) in `x9`, after two
    steps — frame and pc tracked. -/
theorem cmp_cset_step {prog : Asm.Prog} {c : Asm.Cond} {va vb : Val} {s : Asm.State}
    (hi0 : prog[s.pc]? = some (.cmp 9 10)) (hi1 : prog[s.pc + 1]? = some (.cset 9 c))
    (h9 : s.get 9 = encode va) (h10 : s.get 10 = encode vb) :
    ∃ s', Asm.run prog 2 s = .running s' ∧ s'.get 9 = csetVal c va vb
        ∧ s'.mem = s.mem ∧ s'.pc = s.pc + 2 := by
  have hstep0 : Asm.step prog s = .cont ({ s with flags := subFlags (s.get 9) (s.get 10) }.next) := by
    simp only [Asm.step, hi0]
  have hi1' : prog[({ s with flags := subFlags (s.get 9) (s.get 10) }.next).pc]? = some (.cset 9 c) :=
    hi1
  have hstep1 : Asm.step prog ({ s with flags := subFlags (s.get 9) (s.get 10) }.next)
      = .cont ((({ s with flags := subFlags (s.get 9) (s.get 10) }.next).set 9
          (if c.holds (subFlags (s.get 9) (s.get 10)) then 1 else 0)).next) := by
    simp only [Asm.step, hi1']; rfl
  refine ⟨(({ s with flags := subFlags (s.get 9) (s.get 10) }.next).set 9
            (if c.holds (subFlags (s.get 9) (s.get 10)) then 1 else 0)).next, ?_, ?_, ?_, ?_⟩
  · rw [show (2 : Nat) = 1 + 1 from rfl,
        Asm.run_running_add 1 1 (show Asm.run prog 1 s
            = .running ({ s with flags := subFlags (s.get 9) (s.get 10) }.next) by
          rw [Asm.run_one_cont 0 hstep0]; rfl),
        Asm.run_one_cont 0 hstep1]; rfl
  · show (if c.holds (subFlags (s.get 9) (s.get 10)) then 1 else 0) = csetVal c va vb
    rw [h9, h10]
  · rfl
  · rfl

/-- `encode v = 0` iff `v = 0` (`encode` is injective, `encode 0 = 0`). -/
theorem encode_eq_zero (v : Val) : (encode v == (0 : Asm.Word)) = (v == 0) := by
  show (encode v == encode 0) = (v == 0); rw [← encode_beq]

/-- **`div` stepping (with fault).** `cbz x10, faultPc ; sdiv x9, x9, x10`: if `vb ≠ 0` leaves
    `encode (va / vb)` in `x9` (2 steps); if `vb = 0` the `cbz` branches to the fault block and faults. -/
theorem div_step {prog : Asm.Prog} {faultPc : Nat} {va vb : Val} {s : Asm.State}
    (hi0 : prog[s.pc]? = some (.cbz 10 faultPc)) (hi1 : prog[s.pc + 1]? = some (.alu .sdiv 9 9 10))
    (hf : prog[faultPc]? = some .abort) (h9 : s.get 9 = encode va) (h10 : s.get 10 = encode vb) :
    match Binop.denote .div va vb with
    | some v => ∃ s', Asm.run prog 2 s = .running s' ∧ s'.get 9 = encode v
                  ∧ s'.mem = s.mem ∧ s'.pc = s.pc + 2
    | none => Asm.run prog 2 s = .faulted := by
  by_cases hvb : vb = 0
  · -- fault: cbz branches to faultPc, then abort
    have hd : Binop.denote .div va vb = none := by simp [Binop.denote, hvb]
    rw [hd]
    have h0 : s.get 10 = (0 : Asm.Word) := by rw [h10, hvb]; rfl
    have hstep0 : Asm.step prog s = .cont { s with pc := faultPc } := by
      simp only [Asm.step, hi0]; rw [h0]; rfl
    have hstepf : Asm.step prog ({ s with pc := faultPc }) = .fault := by
      simp only [Asm.step, hf]
    rw [show (2 : Nat) = 1 + 1 from rfl, Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep0]; rfl)]
    simp only [Asm.run, hstepf]
  · -- ok: cbz falls through, sdiv computes va / vb
    have hd : Binop.denote .div va vb = some (va / vb) := by simp [Binop.denote, hvb]
    rw [hd]
    have hbz : (s.get 10 == (0 : Asm.Word)) = false := by
      rw [beq_eq_false_iff_ne, h10]; intro he; exact hvb (Int64.toBitVec_inj.mp he)
    have hstep0 : Asm.step prog s = .cont s.next := by
      simp only [Asm.step, hi0]; rw [hbz]; rfl
    have hi1' : prog[s.next.pc]? = some (.alu .sdiv 9 9 10) := hi1
    have h9' : s.next.get 9 = encode va := by rw [Asm.next_get, h9]
    have h10' : s.next.get 10 = encode vb := by rw [Asm.next_get, h10]
    refine ⟨(s.next.set 9 (encode (va / vb))).next, ?_, ?_, ?_, ?_⟩
    · rw [show (2 : Nat) = 1 + 1 from rfl, Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep0]; rfl)]
      exact alu_step hi1' h9' h10' (by rw [alu_div])
    · rfl
    · simp only [Asm.next_mem, Asm.set_mem]
    · rfl

/-- **`mod` stepping (with fault).** `cbz x10, faultPc ; sdiv x11, x9, x10 ; msub x9, x11, x10, x9`:
    if `vb ≠ 0` leaves `encode (va - va/vb*vb)` in `x9` (3 steps); if `vb = 0` faults. -/
theorem mod_step {prog : Asm.Prog} {faultPc : Nat} {va vb : Val} {s : Asm.State}
    (hi0 : prog[s.pc]? = some (.cbz 10 faultPc)) (hi1 : prog[s.pc + 1]? = some (.alu .sdiv 11 9 10))
    (hi2 : prog[s.pc + 2]? = some (.msub 9 11 10 9))
    (hf : prog[faultPc]? = some .abort) (h9 : s.get 9 = encode va) (h10 : s.get 10 = encode vb) :
    match Binop.denote .mod va vb with
    | some v => ∃ s', Asm.run prog 3 s = .running s' ∧ s'.get 9 = encode v
                  ∧ s'.mem = s.mem ∧ s'.pc = s.pc + 3
    | none => Asm.run prog 3 s = .faulted := by
  by_cases hvb : vb = 0
  · have hd : Binop.denote .mod va vb = none := by simp [Binop.denote, hvb]
    rw [hd]
    have h0 : s.get 10 = (0 : Asm.Word) := by rw [h10, hvb]; rfl
    have hstep0 : Asm.step prog s = .cont { s with pc := faultPc } := by
      simp only [Asm.step, hi0]; rw [h0]; rfl
    have hstepf : Asm.step prog ({ s with pc := faultPc }) = .fault := by simp only [Asm.step, hf]
    rw [show (3 : Nat) = 1 + 2 from rfl, Asm.run_running_add 1 2 (by rw [Asm.run_one_cont 0 hstep0]; rfl),
        show (2 : Nat) = 1 + 1 from rfl]
    simp only [Asm.run, hstepf]
  · have hd : Binop.denote .mod va vb = some (va - va / vb * vb) := by simp [Binop.denote, hvb]
    rw [hd]
    have hbz : (s.get 10 == (0 : Asm.Word)) = false := by
      rw [beq_eq_false_iff_ne, h10]; intro he; exact hvb (Int64.toBitVec_inj.mp he)
    have hstep0 : Asm.step prog s = .cont s.next := by simp only [Asm.step, hi0]; rw [hbz]; rfl
    -- sdiv x11, x9, x10  (writes x11)
    have hi1' : prog[s.next.pc]? = some (.alu .sdiv 11 9 10) := hi1
    have hstep1 : Asm.step prog s.next
        = .cont ((s.next.set 11 (encode (va / vb))).next) := by
      simp only [Asm.step, hi1']
      rw [Asm.next_get, Asm.next_get, h9, h10, alu_div]
    -- msub x9, x11, x10, x9  (writes x9 := x9 - x11*x10)
    have hi2' : prog[((s.next.set 11 (encode (va / vb))).next).pc]? = some (.msub 9 11 10 9) := hi2
    have hg9 : ((s.next.set 11 (encode (va / vb))).next).get 9 = encode va := by
      rw [Asm.next_get, Asm.get9_set_ne _ 11 _ (by decide), Asm.next_get, h9]
    have hg10 : ((s.next.set 11 (encode (va / vb))).next).get 10 = encode vb := by
      rw [Asm.next_get, Asm.get_set_ne _ 11 10 _ (by decide), Asm.next_get, h10]
    have hg11 : ((s.next.set 11 (encode (va / vb))).next).get 11 = encode (va / vb) :=
      by rw [Asm.next_get]; exact Asm.get_set_same _ 11 _ (by decide)
    have hstep2 : Asm.step prog ((s.next.set 11 (encode (va / vb))).next)
        = .cont (((s.next.set 11 (encode (va / vb))).next).set 9 (encode (va - va / vb * vb))).next := by
      simp only [Asm.step, hi2']
      rw [hg9, hg10, hg11, ← alu_div, mod_msub]
    refine ⟨(((s.next.set 11 (encode (va / vb))).next).set 9 (encode (va - va / vb * vb))).next,
            ?_, ?_, ?_, ?_⟩
    · rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
          Asm.run_running_add (1 + 1) 1 (by
            rw [Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep0]; rfl),
                Asm.run_one_cont 0 hstep1]; rfl),
          Asm.run_one_cont 0 hstep2]; rfl
    · rfl
    · simp only [Asm.next_mem, Asm.set_mem]
    · rfl

/-- **`binArm` execution.** On `x9 = encode va`, `x10 = encode vb`, running node `i`'s `binArm op` leaves
    `encode (Binop.denote op va vb)` in `x9` (when total), or faults (div/mod by zero). The per-operator
    dispatch onto `alu_step` / `cmp_cset_step` / `div_step` / `mod_step` and the `CodegenBinop` value layer. -/
theorem binArm_correct {prog : Asm.Prog} {faultPc : Nat} {op : Binop} {va vb : Val} {s : Asm.State}
    (hpres : Asm.Embeds prog s.pc (binArm faultPc op)) (hf : prog[faultPc]? = some .abort)
    (h9 : s.get 9 = encode va) (h10 : s.get 10 = encode vb) :
    match Binop.denote op va vb with
    | some v => ∃ s', Asm.run prog (binArm faultPc op).length s = .running s'
                  ∧ s'.get 9 = encode v ∧ s'.mem = s.mem ∧ s'.pc = s.pc + (binArm faultPc op).length
    | none => Asm.run prog (binArm faultPc op).length s = .faulted := by
  cases op with
  | add => exact ⟨_, alu_step hpres.head h9 h10 (alu_add va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | sub => exact ⟨_, alu_step hpres.head h9 h10 (alu_sub va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | mul => exact ⟨_, alu_step hpres.head h9 h10 (alu_mul va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | and => exact ⟨_, alu_step hpres.head h9 h10 (alu_and va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | or => exact ⟨_, alu_step hpres.head h9 h10 (alu_or va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | xor => exact ⟨_, alu_step hpres.head h9 h10 (alu_xor va vb), rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | shl => exact ⟨_, alu_step hpres.head h9 h10 (shift_shl va vb).symm, rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | lshr => exact ⟨_, alu_step hpres.head h9 h10 (shift_lshr va vb).symm, rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | ashr => exact ⟨_, alu_step hpres.head h9 h10 (shift_ashr va vb).symm, rfl,
      by simp only [Asm.next_mem, Asm.set_mem], rfl⟩
  | eq => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
          exact ⟨s', hr, by rw [hg]; exact (cset_eq va vb).symm, hm, hp⟩
  | ne => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
          exact ⟨s', hr, by rw [hg]; exact (cset_ne va vb).symm, hm, hp⟩
  | lt => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
          exact ⟨s', hr, by rw [hg]; exact (cset_lt va vb).symm, hm, hp⟩
  | le => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
          exact ⟨s', hr, by rw [hg]; exact (cset_le va vb).symm, hm, hp⟩
  | ltu => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
           exact ⟨s', hr, by rw [hg]; exact (cset_ltu va vb).symm, hm, hp⟩
  | leu => obtain ⟨s', hr, hg, hm, hp⟩ := cmp_cset_step hpres.head hpres.tail.head h9 h10
           exact ⟨s', hr, by rw [hg]; exact (cset_leu va vb).symm, hm, hp⟩
  | div => exact div_step hpres.head hpres.tail.head hf h9 h10
  | mod => exact mod_step hpres.head hpres.tail.head hpres.tail.tail.head hf h9 h10

/-- **`emitExpr` simulation (forward, item 1).** With the emitted instructions at consecutive pcs from
    `s.pc`, the fault block reachable, and the frame holding the store, running `emitExpr vs faultPc e`
    evaluates `e`: leaving `encode (eval σ e)` in `x9` (frame untouched, pc advanced by the block length)
    when `eval σ e` succeeds, or faulting when it is `none` (div/mod by zero). Composes `loadAtom_correct`
    (×1 or ×2), `unArm_correct`, and `binArm_correct` via `run_running_add`. -/
theorem emitExpr_correct {prog : Asm.Prog} {vs : List Var} {faultPc : Nat} {e : Expr}
    {σ : Store} {s : Asm.State}
    (hpres : Asm.Embeds prog s.pc (emitExpr vs faultPc e)) (hf : prog[faultPc]? = some .abort)
    (hmem : ∀ v, s.mem (slot vs v) = encode (σ v)) :
    match eval σ e with
    | some v => ∃ s', Asm.run prog (emitExpr vs faultPc e).length s = .running s'
                  ∧ s'.get 9 = encode v ∧ s'.mem = s.mem
                  ∧ s'.pc = s.pc + (emitExpr vs faultPc e).length
    | none => Asm.run prog (emitExpr vs faultPc e).length s = .faulted := by
  cases e with
  | atom a =>
    simp only [emitExpr, eval] at hpres ⊢
    have hlenA : (loadAtom vs 9 a).length = 1 := by cases a <;> rfl
    have hiA : prog[s.pc]? = (loadAtom vs 9 a)[0]? := hpres.get0 (by rw [hlenA]; omega)
    refine ⟨(s.set 9 (encode (evalAtom σ a))).next, ?_, rfl,
            by simp only [Asm.next_mem, Asm.set_mem], ?_⟩
    · rw [hlenA]; exact loadAtom_correct (by decide) hiA hmem
    · rw [hlenA]; rfl
  | una op a =>
    simp only [emitExpr, eval] at hpres ⊢
    have hlenA : (loadAtom vs 9 a).length = 1 := by cases a <;> rfl
    have hlenU : (unArm op).length = 1 := by cases op <;> rfl
    have hlen : (loadAtom vs 9 a ++ unArm op).length = 2 := by
      simp only [List.length_append, hlenA, hlenU]
    have hiA : prog[s.pc]? = (loadAtom vs 9 a)[0]? :=
      hpres.append_left.get0 (by rw [hlenA]; omega)
    have hrunA : Asm.run prog 1 s = .running ((s.set 9 (encode (evalAtom σ a))).next) :=
      loadAtom_correct (by decide) hiA hmem
    have hiU : prog[((s.set 9 (encode (evalAtom σ a))).next).pc]? = (unArm op)[0]? := by
      show prog[s.pc + 1]? = (unArm op)[0]?
      have := (hpres.append_right (l₁ := loadAtom vs 9 a)).get0 (by rw [hlenU]; omega)
      rwa [hlenA] at this
    have hrunU := unArm_correct hiU
      (show ((s.set 9 (encode (evalAtom σ a))).next).get 9 = encode (evalAtom σ a) from rfl)
    refine ⟨(((s.set 9 (encode (evalAtom σ a))).next).set 9
              (encode (Unop.denote op (evalAtom σ a)))).next, ?_, rfl,
            by simp only [Asm.next_mem, Asm.set_mem], ?_⟩
    · rw [hlen, show (2 : Nat) = 1 + 1 from rfl, Asm.run_running_add 1 1 hrunA]; exact hrunU
    · rw [hlen]; rfl
  | bin op a b =>
    simp only [emitExpr] at hpres ⊢
    have hlenA : (loadAtom vs 9 a).length = 1 := by cases a <;> rfl
    have hlenB : (loadAtom vs 10 b).length = 1 := by cases b <;> rfl
    have hlen : (loadAtom vs 9 a ++ loadAtom vs 10 b ++ binArm faultPc op).length
        = 2 + (binArm faultPc op).length := by
      simp only [List.length_append, hlenA, hlenB]
    have hiA : prog[s.pc]? = (loadAtom vs 9 a)[0]? :=
      hpres.append_left.append_left.get0 (by rw [hlenA]; omega)
    have hrunA : Asm.run prog 1 s = .running ((s.set 9 (encode (evalAtom σ a))).next) :=
      loadAtom_correct (by decide) hiA hmem
    have hiB : prog[((s.set 9 (encode (evalAtom σ a))).next).pc]? = (loadAtom vs 10 b)[0]? := by
      show prog[s.pc + 1]? = (loadAtom vs 10 b)[0]?
      have := (hpres.append_left.append_right (l₁ := loadAtom vs 9 a)).get0 (by rw [hlenB]; omega)
      rwa [hlenA] at this
    have hrunB : Asm.run prog 1 ((s.set 9 (encode (evalAtom σ a))).next)
        = .running (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next) :=
      loadAtom_correct (by decide) hiB hmem
    have hrun2 : Asm.run prog 2 s
        = .running (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next) := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Asm.run_running_add 1 1 hrunA]; exact hrunB
    have h9s2 : (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next).get 9
        = encode (evalAtom σ a) := by
      rw [Asm.next_get, Asm.get9_set_ne _ 10 _ (by decide), Asm.next_get]
      exact Asm.get_set_same _ 9 _ (by decide)
    have h10s2 : (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next).get 10
        = encode (evalAtom σ b) := by
      rw [Asm.next_get]; exact Asm.get_set_same _ 10 _ (by decide)
    have hmem2 : (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next).mem
        = s.mem := by simp only [Asm.next_mem, Asm.set_mem]
    have hpc2 : (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next).pc
        = s.pc + 2 := rfl
    have hbinEmb : Asm.Embeds prog
        (((s.set 9 (encode (evalAtom σ a))).next.set 10 (encode (evalAtom σ b))).next).pc
        (binArm faultPc op) := by
      rw [hpc2]
      have := hpres.append_right (l₁ := loadAtom vs 9 a ++ loadAtom vs 10 b)
      rwa [show (loadAtom vs 9 a ++ loadAtom vs 10 b).length = 2 from by
        rw [List.length_append, hlenA, hlenB]] at this
    have hb := binArm_correct hbinEmb hf h9s2 h10s2
    simp only [eval]
    cases hd : op.denote (evalAtom σ a) (evalAtom σ b) with
    | none =>
      rw [hd] at hb
      rw [hlen, Asm.run_running_add 2 (binArm faultPc op).length hrun2]; exact hb
    | some v =>
      rw [hd] at hb
      obtain ⟨s3, hr3, hg3, hm3, hp3⟩ := hb
      refine ⟨s3, ?_, hg3, ?_, ?_⟩
      · rw [hlen, Asm.run_running_add 2 (binArm faultPc op).length hrun2]; exact hr3
      · rw [hm3]; exact hmem2
      · rw [hp3, hpc2, hlen]; omega

end TacToAsm

end BaseLanguage
