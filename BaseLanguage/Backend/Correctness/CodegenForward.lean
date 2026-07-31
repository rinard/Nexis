-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Backend.Correctness.CodegenSim
import BaseLanguage.Backend.Correctness.CodegenEmit

namespace BaseLanguage

/-!
# `CodegenForward` — the per-block forward simulation (capstone, proved: `codegen_simulates`)

Bridges the two finished layers:
* **layout** (`CodegenSim`): `codegen P` is a sequence of fixed-`B`-size blocks, so model pc `nd*B + j`
  selects the `j`-th instruction of node `nd`'s block (`codegen_block_get`);
* **expressions** (`CodegenEmit`): running `emitExpr` evaluates the RHS into `x9` (`emitExpr_correct`).

This file lands the connection tissue — the simulation relation `StateRel`, the block embedding
`block_embeds` (node `nd`'s block is `Asm.Embeds`ded at `nd*B`), and the fault block `fault_abort`
(`(codegen P)[faultPc]? = abort`) — on which the per-block step lemmas (`assign`/`ifz`/`noop`/`halt`)
and the whole-program `Steps`-induction are built.
-/

namespace TacToAsm

open Tac Semantics Asm

/-- **The simulation relation.** Model state `s` realises IR config `c`: the pc sits at the head of
    node `c.node`'s block, and the frame holds the (encoded) store. Registers/flags are unconstrained at
    block boundaries — each block reloads what it needs from the frame. -/
def StateRel (P : Program) (c : Config) (s : Asm.State) : Prop :=
  s.pc = c.node * B ∧ ∀ v, s.mem (slot (collectVars P) v) = encode (c.store v)

/-- **Node `nd`'s block is embedded at pc `nd*B`.** The pad-`abort`s past the real block are never
    indexed (we only consume `k < (blockFor …).length`), so this exposes exactly the real instructions. -/
theorem block_embeds (P : Program) (nd : Nat) (hnd : nd < P.code.size) :
    Asm.Embeds (codegen P) (nd * B)
      (blockFor (collectVars P) (P.code.size * B) (P.code[nd]!)) := by
  intro k hk
  have hkB : k < B := Nat.lt_of_lt_of_le hk (blockFor_length_le _ _ _)
  rw [codegen_block_get P nd k hnd hkB, pad, List.getElem?_append_left hk]

/-- **The fault block is an `abort` at `faultPc = numNodes * B`.** Division/modulo by zero's `cbz`
    branches here, so the run faults. -/
theorem fault_abort (P : Program) : (codegen P)[P.code.size * B]? = some .abort := by
  have hlen := length_flatMap_const (fun i => block_length P i) P.code.size
  simp only [codegen, List.getElem?_toArray]
  rw [List.getElem?_append_right (by omega), hlen, Nat.sub_self]
  simp [pad]

/-- From `fetch nd = some instr`: the node is in range and `P.code[nd]!` is `instr`
    (so `block_embeds`/`block_length`, stated on `P.code[nd]!`, apply). -/
theorem fetch_code {P : Program} {nd : Nat} {instr : Tac.Cmd} (hf : P.fetch nd = some instr) :
    nd < P.code.size ∧ P.code[nd]! = instr := by
  have hlt : nd < P.code.size := Semantics.fetch_lt hf
  refine ⟨hlt, ?_⟩
  have hg : P.fetch nd = some P.code[nd] := Array.getElem?_eq_getElem hlt
  rw [hg] at hf
  rw [getElem!_pos P.code nd hlt]; exact Option.some.inj hf

/-! ## `collectVars` completeness (the assigned var is collected, so `x ∈ vs`) -/

theorem memV_true_iff {vs : List Var} {v : Var} : memV vs v = true ↔ v ∈ vs := by
  unfold memV; rw [List.any_eq_true]
  constructor
  · rintro ⟨u, hu, he⟩; rw [decide_eq_true_eq] at he; exact he ▸ hu
  · intro h; exact ⟨v, h, by simp⟩

theorem mem_addVar_self (vs : List Var) (v : Var) : v ∈ addVar vs v := by
  unfold addVar; split
  · rename_i h; exact memV_true_iff.mp h
  · exact List.mem_append_right _ (by simp)

theorem subset_addVar (vs : List Var) (v : Var) : vs ⊆ addVar vs v := by
  unfold addVar; split
  · exact List.Subset.refl vs
  · exact List.subset_append_left vs [v]

theorem subset_atomVars (vs : List Var) (a : Atom) : vs ⊆ atomVars vs a := by
  cases a with
  | var v => exact subset_addVar vs v
  | imm n => exact List.Subset.refl vs

theorem subset_exprVars (vs : List Var) (e : Expr) : vs ⊆ exprVars vs e := by
  cases e with
  | atom a => exact subset_atomVars vs a
  | una op a => exact subset_atomVars vs a
  | bin op a b => exact (subset_atomVars vs a).trans (subset_atomVars _ b)

theorem subset_instrVars (vs : List Var) (instr : Tac.Cmd) : vs ⊆ instrVars vs instr := by
  cases instr with
  | assign x e next => exact (subset_addVar vs x).trans (subset_exprVars _ e)
  | ifz x a b => exact subset_addVar vs x
  | noop next => exact List.Subset.refl vs
  | halt => exact List.Subset.refl vs

theorem mem_instrVars_assign (vs : List Var) (x : Var) (e : Expr) (next : Nat) :
    x ∈ instrVars vs (.assign x e next) :=
  subset_exprVars (addVar vs x) e (mem_addVar_self vs x)

theorem subset_foldl {α} {f : List Var → α → List Var} (hf : ∀ ws a, ws ⊆ f ws a) :
    ∀ (l : List α) (ws : List Var), ws ⊆ l.foldl f ws := by
  intro l
  induction l with
  | nil => intro ws; exact List.Subset.refl ws
  | cons b rest ih => intro ws; exact (hf ws b).trans (ih (f ws b))

theorem mem_foldl_of_step {α} {f : List Var → α → List Var} (hf : ∀ ws a, ws ⊆ f ws a)
    {x : Var} {a : α} (hstep : ∀ ws, x ∈ f ws a) :
    ∀ (l : List α) (ws : List Var), a ∈ l → x ∈ l.foldl f ws := by
  intro l
  induction l with
  | nil => intro ws ha; exact absurd ha (by simp)
  | cons b rest ih =>
    intro ws ha
    rcases List.mem_cons.mp ha with hb | hr
    · exact subset_foldl hf rest (f ws b) (hb ▸ hstep ws)
    · exact ih (f ws b) hr

theorem collectVars_mem_of_assign {P : Program} {nd : Nat} {x : Var} {e : Expr} {next : Nat}
    (hf : P.fetch nd = some (.assign x e next)) : x ∈ collectVars P := by
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hain : (Tac.Cmd.assign x e next) ∈ P.code.toList := by
    rw [← hcode, getElem!_pos P.code nd hnd]; exact Array.getElem_mem_toList hnd
  have hx1 : x ∈ P.code.toList.foldl instrVars [] :=
    mem_foldl_of_step subset_instrVars (fun ws => mem_instrVars_assign ws x e next) _ [] hain
  exact subset_foldl subset_addVar P.obs _ hx1

/-! ## Slot injectivity (for the `assign` frame update) -/

/-- `idxV` is injective on members: equal indices ⇒ equal vars (the index lands on the var). -/
theorem idxV_inj_of_mem {vs : List Var} {x : Var} (hx : x ∈ vs) {v : Var}
    (h : idxV vs v = idxV vs x) : v = x := by
  unfold idxV at h
  have hxlt : vs.findIdx (fun u => decide (u = x)) < vs.length :=
    List.findIdx_lt_length_of_exists ⟨x, hx, by simp⟩
  have hvlt : vs.findIdx (fun u => decide (u = v)) < vs.length := h ▸ hxlt
  have hev : vs[vs.findIdx (fun u => decide (u = v))] = v := by
    have := @List.findIdx_getElem _ (fun u => decide (u = v)) vs hvlt; simpa using this
  have hex : vs[vs.findIdx (fun u => decide (u = x))] = x := by
    have := @List.findIdx_getElem _ (fun u => decide (u = x)) vs hxlt; simpa using this
  have hev' : vs[vs.findIdx (fun u => decide (u = v))]? = some v := by
    rw [List.getElem?_eq_getElem hvlt, hev]
  have hex' : vs[vs.findIdx (fun u => decide (u = x))]? = some x := by
    rw [List.getElem?_eq_getElem hxlt, hex]
  rw [h] at hev'
  exact Option.some.inj (hev'.symm.trans hex')

/-- **`slot` is injective on `vs`-members.** Equal slots ⇒ equal vars, when one is in `vs`. The
    frame-update soundness for `assign` (the written var is collected, so `x ∈ vs`). -/
theorem slot_inj_of_mem {vs : List Var} {x : Var} (hx : x ∈ vs) {v : Var}
    (h : slot vs v = slot vs x) : v = x := by
  apply idxV_inj_of_mem hx
  simp only [slot, slotOff] at h; omega

/-! ## Per-block forward steps (control-flow cases — frame untouched) -/

/-- **`noop` block.** One `b`-step jumps to the successor block; the frame is unchanged. -/
theorem forward_noop {P : Program} {nd next : Nat} {σ : Store} {s : Asm.State}
    (hrel : StateRel P ⟨nd, σ⟩ s) (hf : P.fetch nd = some (.noop next)) :
    ∃ s', Asm.run (codegen P) 1 s = .running s' ∧ StateRel P ⟨next, σ⟩ s' := by
  obtain ⟨hpc, hmem⟩ := hrel
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hemb := block_embeds P nd hnd
  rw [hcode] at hemb
  simp only [blockFor] at hemb
  have hi : (codegen P)[s.pc]? = some (.b (next * B)) := by rw [hpc]; exact hemb.head
  have hstep : Asm.step (codegen P) s = .cont { s with pc := next * B } := by
    simp only [Asm.step, hi]
  exact ⟨{ s with pc := next * B }, by rw [Asm.run_one_cont 0 hstep]; rfl, rfl, hmem⟩

/-- **`halt` block.** The single `halt` instruction halts the machine in-place. -/
theorem forward_halt {P : Program} {nd : Nat} {σ : Store} {s : Asm.State}
    (hrel : StateRel P ⟨nd, σ⟩ s) (hf : P.fetch nd = some .halt) :
    Asm.run (codegen P) 1 s = .halted s := by
  obtain ⟨hpc, hmem⟩ := hrel
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hemb := block_embeds P nd hnd
  rw [hcode] at hemb
  simp only [blockFor] at hemb
  have hi : (codegen P)[s.pc]? = some .halt := by rw [hpc]; exact hemb.head
  have hstep : Asm.step (codegen P) s = .halt s := by simp only [Asm.step, hi]
  simp only [Asm.run, hstep]

/-- **`ifz` block, taken branch** (`σ x = 0`). `ldrSlot x9 ← x ; cbz x9, z*B`: loads `encode (σ x) = 0`,
    the `cbz` branches to block `z`. Frame unchanged. -/
theorem forward_ifzT {P : Program} {nd z nz : Nat} {x : Var} {σ : Store} {s : Asm.State}
    (hrel : StateRel P ⟨nd, σ⟩ s) (hf : P.fetch nd = some (.ifz x z nz)) (hzx : σ x = 0) :
    ∃ s', Asm.run (codegen P) 2 s = .running s' ∧ StateRel P ⟨z, σ⟩ s' := by
  obtain ⟨hpc, hmem⟩ := hrel
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hemb := block_embeds P nd hnd
  rw [hcode] at hemb; simp only [blockFor] at hemb
  have hi0 : (codegen P)[s.pc]? = some (.ldrSlot 9 (slot (collectVars P) x)) := by
    rw [hpc]; exact hemb.head
  have hstep0 : Asm.step (codegen P) s
      = .cont ((s.set 9 (s.mem (slot (collectVars P) x))).next) := by simp only [Asm.step, hi0]
  have hi1 : (codegen P)[((s.set 9 (s.mem (slot (collectVars P) x))).next).pc]?
      = some (.cbz 9 (z * B)) := by
    show (codegen P)[s.pc + 1]? = some (.cbz 9 (z * B)); rw [hpc]; exact hemb.tail.head
  have h9z : ((s.set 9 (s.mem (slot (collectVars P) x))).next).get 9 = (0 : Asm.Word) := by
    rw [show ((s.set 9 (s.mem (slot (collectVars P) x))).next).get 9
          = s.mem (slot (collectVars P) x) from rfl, hmem x]
    show encode (σ x) = 0; rw [hzx]; rfl
  have hstep1 : Asm.step (codegen P) ((s.set 9 (s.mem (slot (collectVars P) x))).next)
      = .cont { (s.set 9 (s.mem (slot (collectVars P) x))).next with pc := z * B } := by
    simp only [Asm.step, hi1]; rw [h9z]; rfl
  refine ⟨{ (s.set 9 (s.mem (slot (collectVars P) x))).next with pc := z * B }, ?_, rfl, hmem⟩
  rw [show (2 : Nat) = 1 + 1 from rfl, Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep0]; rfl),
      Asm.run_one_cont 0 hstep1]; rfl

/-- **`ifz` block, fall-through branch** (`σ x ≠ 0`). The `cbz` falls through, then `b nz*B` jumps to
    block `nz`. Frame unchanged. -/
theorem forward_ifzF {P : Program} {nd z nz : Nat} {x : Var} {σ : Store} {s : Asm.State}
    (hrel : StateRel P ⟨nd, σ⟩ s) (hf : P.fetch nd = some (.ifz x z nz)) (hzx : σ x ≠ 0) :
    ∃ s', Asm.run (codegen P) 3 s = .running s' ∧ StateRel P ⟨nz, σ⟩ s' := by
  obtain ⟨hpc, hmem⟩ := hrel
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hemb := block_embeds P nd hnd
  rw [hcode] at hemb; simp only [blockFor] at hemb
  have hi0 : (codegen P)[s.pc]? = some (.ldrSlot 9 (slot (collectVars P) x)) := by
    rw [hpc]; exact hemb.head
  have hstep0 : Asm.step (codegen P) s
      = .cont ((s.set 9 (s.mem (slot (collectVars P) x))).next) := by simp only [Asm.step, hi0]
  have hi1 : (codegen P)[((s.set 9 (s.mem (slot (collectVars P) x))).next).pc]?
      = some (.cbz 9 (z * B)) := by
    show (codegen P)[s.pc + 1]? = some (.cbz 9 (z * B)); rw [hpc]; exact hemb.tail.head
  have hbz : (((s.set 9 (s.mem (slot (collectVars P) x))).next).get 9 == (0 : Asm.Word)) = false := by
    rw [beq_eq_false_iff_ne, show ((s.set 9 (s.mem (slot (collectVars P) x))).next).get 9
          = s.mem (slot (collectVars P) x) from rfl, hmem x]
    intro he; exact hzx (Int64.toBitVec_inj.mp he)
  have hstep1 : Asm.step (codegen P) ((s.set 9 (s.mem (slot (collectVars P) x))).next)
      = .cont (((s.set 9 (s.mem (slot (collectVars P) x))).next).next) := by
    simp only [Asm.step, hi1]; rw [hbz]; rfl
  have hi2 : (codegen P)[(((s.set 9 (s.mem (slot (collectVars P) x))).next).next).pc]?
      = some (.b (nz * B)) := by
    show (codegen P)[s.pc + 2]? = some (.b (nz * B)); rw [hpc]; exact hemb.tail.tail.head
  have hstep2 : Asm.step (codegen P) (((s.set 9 (s.mem (slot (collectVars P) x))).next).next)
      = .cont { ((s.set 9 (s.mem (slot (collectVars P) x))).next).next with pc := nz * B } := by
    simp only [Asm.step, hi2]
  refine ⟨{ ((s.set 9 (s.mem (slot (collectVars P) x))).next).next with pc := nz * B }, ?_, rfl, hmem⟩
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl,
      Asm.run_running_add (1 + 1) 1 (by
        rw [Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep0]; rfl),
            Asm.run_one_cont 0 hstep1]; rfl),
      Asm.run_one_cont 0 hstep2]; rfl

/-- **`assign` block.** `emitExpr e` evaluates the RHS into `x9` (`emitExpr_correct`); `strSlot x9 → x`
    writes it to the frame; `b next*B` jumps. The frame update is sound because `x` is collected
    (`slot_inj_of_mem`). (`eval σ e = some v`; the `none`/fault case is a non-`Step` faulting config.) -/
theorem forward_assign {P : Program} {nd next : Nat} {x : Var} {e : Expr} {v : Val}
    {σ : Store} {s : Asm.State}
    (hrel : StateRel P ⟨nd, σ⟩ s) (hf : P.fetch nd = some (.assign x e next))
    (hev : eval σ e = some v) :
    ∃ s', Asm.run (codegen P) ((emitExpr (collectVars P) (P.code.size * B) e).length + 2) s
            = .running s' ∧ StateRel P ⟨next, σ.update x v⟩ s' := by
  obtain ⟨hpc, hmem⟩ := hrel
  have hmem' : ∀ w, s.mem (slot (collectVars P) w) = encode (σ w) := hmem
  obtain ⟨hnd, hcode⟩ := fetch_code hf
  have hxmem : x ∈ collectVars P := collectVars_mem_of_assign hf
  have hemb := block_embeds P nd hnd
  rw [hcode] at hemb; simp only [blockFor] at hemb
  have hembE : Asm.Embeds (codegen P) s.pc (emitExpr (collectVars P) (P.code.size * B) e) := by
    rw [hpc]; exact hemb.append_left
  have hE := emitExpr_correct hembE (fault_abort P) hmem'
  rw [hev] at hE
  obtain ⟨s1, hr1, hg1, hm1, hp1⟩ := hE
  have hembR := hemb.append_right (l₁ := emitExpr (collectVars P) (P.code.size * B) e)
  have hi_str : (codegen P)[s1.pc]? = some (.strSlot 9 (slot (collectVars P) x)) := by
    rw [hp1, hpc]; exact hembR.head
  have hstep_str : Asm.step (codegen P) s1
      = .cont ((s1.store (slot (collectVars P) x) (s1.get 9)).next) := by simp only [Asm.step, hi_str]
  have hi_b : (codegen P)[((s1.store (slot (collectVars P) x) (s1.get 9)).next).pc]?
      = some (.b (next * B)) := by
    show (codegen P)[s1.pc + 1]? = some (.b (next * B)); rw [hp1, hpc]; exact hembR.tail.head
  have hstep_b : Asm.step (codegen P) ((s1.store (slot (collectVars P) x) (s1.get 9)).next)
      = .cont { (s1.store (slot (collectVars P) x) (s1.get 9)).next with pc := next * B } := by
    simp only [Asm.step, hi_b]
  refine ⟨{ (s1.store (slot (collectVars P) x) (s1.get 9)).next with pc := next * B }, ?_, rfl, ?_⟩
  · rw [Asm.run_running_add (emitExpr (collectVars P) (P.code.size * B) e).length 2 hr1,
        show (2 : Nat) = 1 + 1 from rfl,
        Asm.run_running_add 1 1 (by rw [Asm.run_one_cont 0 hstep_str]; rfl),
        Asm.run_one_cont 0 hstep_b]; rfl
  · intro w
    by_cases hw : slot (collectVars P) w = slot (collectVars P) x
    · have hwx : w = x := slot_inj_of_mem hxmem hw
      rw [hwx]
      show (s1.store (slot (collectVars P) x) (s1.get 9)).mem (slot (collectVars P) x)
          = encode ((σ.update x v) x)
      rw [hg1]; simp [State.store, Store.update]
    · have hwx : w ≠ x := fun h => hw (by rw [h])
      show (s1.store (slot (collectVars P) x) (s1.get 9)).mem (slot (collectVars P) w)
          = encode ((σ.update x v) w)
      rw [show (s1.store (slot (collectVars P) x) (s1.get 9)).mem (slot (collectVars P) w)
            = s1.mem (slot (collectVars P) w) from by simp [State.store, hw], hm1, hmem' w]
      simp [Store.update, hwx]

/-- **The per-block forward simulation step.** Each IR `Step` is realised by some number of machine
    steps that re-establishes `StateRel`. Dispatches to the four block-case lemmas. -/
theorem forward_step {P : Program} {c c' : Config} {s : Asm.State}
    (hrel : StateRel P c s) (hstep : Step P c c') :
    ∃ fuel s', Asm.run (codegen P) fuel s = .running s' ∧ StateRel P c' s' := by
  cases hstep with
  | assign hf hev => obtain ⟨s', hr, hrel'⟩ := forward_assign hrel hf hev; exact ⟨_, s', hr, hrel'⟩
  | ifzT hf hz => obtain ⟨s', hr, hrel'⟩ := forward_ifzT hrel hf hz; exact ⟨_, s', hr, hrel'⟩
  | ifzF hf hz => obtain ⟨s', hr, hrel'⟩ := forward_ifzF hrel hf hz; exact ⟨_, s', hr, hrel'⟩
  | noop hf => obtain ⟨s', hr, hrel'⟩ := forward_noop hrel hf; exact ⟨_, s', hr, hrel'⟩

/-! ## Whole-program threading -/

/-- **Forward simulation over `Steps`.** A whole IR run `c ⟶* c'` is realised by some machine run that
    re-establishes `StateRel` at `c'`. Induction on `Steps`, composing `forward_step` with
    `run_running_add`. -/
theorem forward_steps {P : Program} {c c' : Config} {s : Asm.State}
    (hrel : StateRel P c s) (hsteps : Steps P c c') :
    ∃ fuel s', Asm.run (codegen P) fuel s = .running s' ∧ StateRel P c' s' := by
  induction hsteps with
  | refl => exact ⟨0, s, rfl, hrel⟩
  | tail _ hstep ih =>
    obtain ⟨fuel1, s1, hr1, hrel1⟩ := ih
    obtain ⟨fuel2, s2, hr2, hrel2⟩ := forward_step hrel1 hstep
    exact ⟨fuel1 + fuel2, s2, by rw [Asm.run_running_add fuel1 fuel2 hr1]; exact hr2, hrel2⟩

/-- **The machine halts whenever the IR run reaches a terminal (`halt`) config**, in a state still
    realising the final config (frame holds the final store). Threads `forward_steps` to the final
    config, then the single `halt` step (which leaves the state unchanged). -/
theorem forward_halts {P : Program} {c cf : Config} {s : Asm.State}
    (hrel : StateRel P c s) (hsteps : Steps P c cf) (hfin : Final P cf) :
    ∃ fuel sf, Asm.run (codegen P) fuel s = .halted sf ∧ StateRel P cf sf := by
  obtain ⟨fuel1, s1, hr1, hrel1⟩ := forward_steps hrel hsteps
  exact ⟨fuel1 + 1, s1, by rw [Asm.run_running_add fuel1 1 hr1]; exact forward_halt hrel1 hfin, hrel1⟩

/-! ## Base case + headline -/

/-- **The initial machine state realises the initial config.** With the conventional all-zero
    initial store, the freshly-laid frame realises it: collected vars resolve via `find?` (slot
    injectivity), the rest are `0` — and `encode 0 = 0`, so every slot matches. -/
theorem initRel (P : Program) : StateRel P ⟨P.entry, Store.init⟩ (initState P Store.init) := by
  refine ⟨rfl, ?_⟩
  intro v
  show (initState P Store.init).mem (slot (collectVars P) v) = encode (Store.init v)
  simp only [initState, Store.init]
  cases (collectVars P).find? (fun w => slot (collectVars P) w == slot (collectVars P) v) <;> rfl

/-- **Forward codegen simulation (headline).** If the IR run from the entry on the all-zero store
    reaches a terminal (`halt`) configuration `cf`, then `codegen P` run from `initState` halts, in a
    machine state whose frame holds `cf`'s store under `encode`. The verified backend reproduces the
    source semantics' halting and final store. -/
theorem codegen_simulates {P : Program} {cf : Config}
    (hsteps : Steps P ⟨P.entry, Store.init⟩ cf) (hfin : Final P cf) :
    ∃ fuel sf, Asm.run (codegen P) fuel (initState P Store.init) = .halted sf
            ∧ ∀ v, sf.mem (slot (collectVars P) v) = encode (cf.store v) := by
  obtain ⟨fuel, sf, hrun, _, hframe⟩ := forward_halts (initRel P) hsteps hfin
  exact ⟨fuel, sf, hrun, hframe⟩

end TacToAsm

end BaseLanguage
