-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
import BaseLanguage.Frontend.Ast

namespace BaseLanguage

/-!
# `AstToTac` — lowering the surface AST to the three-address CFG IR

The `lower` pass takes the structured surface AST (`Ast.Stmt`) to the flat CFG `Program` (TAC), a
**mutation-free** construction with **absolute node labels computed by size functions** (`sz*`) rather
than an in-place builder.

The block for a construct laid at base `b` occupies node indices `[b, b + sz… )`; every successor label is
either the external continuation `cont` or an index inside that range. This makes the output's
`WellFormed` (and reachability) provable by clean structural induction (no `StateM`/`Array.set!`
reasoning).

Temps are `.tmp` of the op-node's own index — unique by construction, hence fresh.
-/

namespace AstToTac

open Tac Ast

/-! ## Size functions — the instruction count of each lowered block (label-independent). -/

/-- Cmd count of `layE e` (compute `e` into a fresh temp). -/
def szE : Ast.Expr → Nat
  | .atom _      => 0
  | .una _ e     => szE e + 1
  | .bin _ e₁ e₂ => szE e₂ + szE e₁ + 1

/-- Cmd count of `layI x e` (compute `e` straight into `x`). -/
def szI : Ast.Expr → Nat
  | .atom _      => 1
  | .una _ e     => szE e + 1
  | .bin _ e₁ e₂ => szE e₂ + szE e₁ + 1

/-- Cmd count of `layC c` (materialize a condition into a `Var`). -/
def szC : Ast.Expr → Nat
  | .atom (.var _) => 0
  | c              => szI c

/-- Cmd count of `layS s`. -/
def szS : Stmt → Nat
  | .skip        => 0
  | .assign _ e  => szI e
  | .seq s₁ s₂   => szS s₁ + szS s₂
  | .ite c t e   => szC c + 1 + szS t + szS e
  | .while c b   => szC c + 1 + szS b

/-! ## Layout — pure functions returning `(code, …, entry)`; block placed at `[base, base+sz…)`. -/

/-- Lower `e` into a fresh temp, flowing to `cont`. (Projection style — `v.1`/`v.2.2` — so the nested
    recursive entry term `(layE e …).2.2` appears as the SAME atom in goal and IH for `omega`.) -/
def layE : Ast.Expr → Node → Node → (List Cmd × Atom × Node)
  | .atom a, cont, _b => ([], a, cont)
  | .una op e, cont, b =>
      let opNode := b + szE e
      let v := layE e opNode b
      (v.1 ++ [.assign (.tmp opNode) (.una op v.2.1) cont], .var (.tmp opNode), v.2.2)
  | .bin op e₁ e₂, cont, b =>
      let opNode := b + szE e₁ + szE e₂
      let v₂ := layE e₂ opNode (b + szE e₁)
      let v₁ := layE e₁ v₂.2.2 b
      (v₁.1 ++ v₂.1 ++ [.assign (.tmp opNode) (.bin op v₁.2.1 v₂.2.1) cont], .var (.tmp opNode), v₁.2.2)

/-- Lower `e` writing the result straight into `x`, flowing to `cont`. -/
def layI (x : Var) : Ast.Expr → Node → Node → (List Cmd × Node)
  | .atom a, cont, b => ([.assign x (.atom a) cont], b)
  | .una op e, cont, b =>
      let opNode := b + szE e
      let v := layE e opNode b
      (v.1 ++ [.assign x (.una op v.2.1) cont], v.2.2)
  | .bin op e₁ e₂, cont, b =>
      let opNode := b + szE e₁ + szE e₂
      let v₂ := layE e₂ opNode (b + szE e₁)
      let v₁ := layE e₁ v₂.2.2 b
      (v₁.1 ++ v₂.1 ++ [.assign x (.bin op v₁.2.1 v₂.2.1) cont], v₁.2.2)

/-- Materialize a condition into a `Var` (reuse a bare variable; else a fresh temp at the block start). -/
def layC : Ast.Expr → Node → Node → (Var × List Cmd × Node)
  | .atom (.var x), cont, _b => (x, [], cont)
  | .atom (.imm n), cont, b  => (.tmp b, [.assign (.tmp b) (.atom (.imm n)) cont], b)
  | .una op e, cont, b       => let r := layI (.tmp b) (.una op e) cont b; (.tmp b, r.1, r.2)
  | .bin op e₁ e₂, cont, b   => let r := layI (.tmp b) (.bin op e₁ e₂) cont b; (.tmp b, r.1, r.2)

/-- Lower statement `s`, flowing to `cont`. -/
def layS : Stmt → Node → Node → (List Cmd × Node)
  | .skip, cont, _b => ([], cont)
  | .assign x e, cont, b => layI x e cont b
  | .seq s₁ s₂, cont, b =>
      let v₂ := layS s₂ cont (b + szS s₁)
      let v₁ := layS s₁ v₂.2 b
      (v₁.1 ++ v₂.1, v₁.2)
  | .ite c t e, cont, b =>
      let ifNode := b + szC c
      let vT := layS t cont (ifNode + 1)
      let vE := layS e cont (ifNode + 1 + szS t)
      let vC := layC c ifNode b
      (vC.2.1 ++ [.ifz vC.1 vE.2 vT.2] ++ vT.1 ++ vE.1, vC.2.2)
  | .while c b', cont, b =>
      let ifNode := b + szC c
      let vC := layC c ifNode b
      -- the loop back-edge targets the condition entry `vC.2.2` (re-evaluate the condition each
      -- iteration); a stale back-edge to `ifNode` would never recompute a *computed* condition.
      let vB := layS b' vC.2.2 (ifNode + 1)
      (vC.2.1 ++ [.ifz vC.1 cont vB.2] ++ vB.1, vC.2.2)

/-- The source (`.orig`) variables occurring in an expression. Immediates and any `.tmp` (none can
    occur in a surface expression anyway) contribute nothing. -/
def origsE : Ast.Expr → List Var
  | .atom (.var (.orig s)) => [.orig s]
  | .atom _ => []
  | .una _ e => origsE e
  | .bin _ a b => origsE a ++ origsE b

/-- The source (`.orig`) variables occurring in a statement — the program's observable interface. -/
def origs : Stmt → List Var
  | .skip => []
  | .assign x e => (match x with | .orig s => [.orig s] | _ => []) ++ origsE e
  | .seq a b => origs a ++ origs b
  | .ite c t e => origsE c ++ origs t ++ origs e
  | .while c b => origsE c ++ origs b

/-- **Lower a statement to TAC.** Node `0` is `halt`; the statement is laid at base `1` continuing to
    `0`. The program's observables are exactly the source variables (`origs s`); the holding
    temporaries this pass introduces (`.tmp`) are deliberately **not** observable — see
    `lower_obs_orig` / `lower_obs_no_tmp`. -/
def lower (s : Stmt) : Program :=
  let (code, entry) := layS s 0 1
  { entry := entry, code := (Cmd.halt :: code).toArray, obs := (origs s).eraseDups }

/-! ## Observability contract: observables are exactly the source variables; no inserted temp leaks.
-/

/-- Every variable collected from an expression is a source (`.orig`) variable. -/
theorem origsE_orig : ∀ (e : Ast.Expr) (v : Var), v ∈ origsE e → ∃ s, v = .orig s := by
  intro e
  induction e with
  | atom a =>
      intro v hv
      cases a with
      | var x => cases x with
        | orig s => simp only [origsE, List.mem_singleton] at hv; exact ⟨s, hv⟩
        | tmp i  => simp [origsE] at hv
      | imm n => simp [origsE] at hv
  | una op e ih => intro v hv; simp only [origsE] at hv; exact ih v hv
  | bin op a b iha ihb =>
      intro v hv; simp only [origsE] at hv
      rcases List.mem_append.mp hv with h | h
      · exact iha v h
      · exact ihb v h

/-- Every variable collected from a statement is a source (`.orig`) variable. -/
theorem origs_orig : ∀ (s : Stmt) (v : Var), v ∈ origs s → ∃ name, v = .orig name := by
  intro s
  induction s with
  | skip => intro v hv; simp [origs] at hv
  | assign x e =>
      intro v hv
      simp only [origs] at hv
      rcases List.mem_append.mp hv with h | h
      · cases x with
        | orig s => simp only [List.mem_singleton] at h; exact ⟨s, h⟩
        | tmp i  => simp at h
      · exact origsE_orig e v h
  | seq a b iha ihb =>
      intro v hv; simp only [origs] at hv
      rcases List.mem_append.mp hv with h | h
      · exact iha v h
      · exact ihb v h
  | ite c t e iht ihe =>
      intro v hv; simp only [origs] at hv
      rcases List.mem_append.mp hv with h | h
      · rcases List.mem_append.mp h with h | h
        · exact origsE_orig c v h
        · exact iht v h
      · exact ihe v h
  | «while» c b ihb =>
      intro v hv; simp only [origs] at hv
      rcases List.mem_append.mp hv with h | h
      · exact origsE_orig c v h
      · exact ihb v h

/-- **Observables are source variables.** Every variable in the lowered program's `obs` is a source
    (`.orig`) variable — the frontend exposes exactly the program's source-level interface. -/
theorem lower_obs_orig (s : Stmt) : ∀ v ∈ (lower s).obs, ∃ name, v = .orig name := by
  intro v hv
  simp only [lower, List.mem_eraseDups] at hv
  exact origs_orig s v hv

/-- **No inserted temporary is observable.** The `.tmp` holding variables `AstToTac` introduces never
    appear in the lowered program's `obs`. -/
theorem lower_obs_no_tmp (s : Stmt) (i : Nat) : Var.tmp i ∉ (lower s).obs := by
  intro hv
  obtain ⟨_, h⟩ := lower_obs_orig s _ hv
  simp at h

/-! ## Coherence: the laid block's length equals its size function. -/

theorem layE_len (e : Ast.Expr) (cont b : Node) : (layE e cont b).1.length = szE e := by
  induction e generalizing cont b with
  | atom a => rfl
  | una op e ih => simp [layE, szE, ih]
  | bin op e₁ e₂ ih₁ ih₂ => simp [layE, szE, ih₁, ih₂]; omega

theorem layI_len (x : Var) (e : Ast.Expr) (cont b : Node) : (layI x e cont b).1.length = szI e := by
  cases e with
  | atom a => rfl
  | una op e => simp [layI, szI, layE_len]
  | bin op e₁ e₂ => simp [layI, szI, layE_len]; omega

theorem layC_len (c : Ast.Expr) (cont b : Node) : (layC c cont b).2.1.length = szC c := by
  cases c with
  | atom a => cases a with
    | var x => rfl
    | imm n => rfl
  | una op e => simp [layC, szC, layI_len]
  | bin op e₁ e₂ => simp [layC, szC, layI_len]

theorem layS_len (s : Stmt) (cont b : Node) : (layS s cont b).1.length = szS s := by
  induction s generalizing cont b with
  | skip => rfl
  | assign x e => simp [layS, szS, layI_len]
  | seq s₁ s₂ ih₁ ih₂ => simp [layS, szS, ih₁, ih₂]
  | ite c t e ihT ihE => simp [layS, szS, ihT, ihE, layC_len]; omega
  | «while» c b' ihB => simp [layS, szS, ihB, layC_len]; omega

/-! ## `WellFormed`: every successor label of the laid block is in `[b, b+sz…)` or the exit `cont`.

⚠ **omega cannot see `Node`** (it is `abbrev Node := Nat`, but omega's frontend syntactically requires
`Nat`/`Int`, so every node-label comparison reads as "no usable constraints"). All node-label arithmetic
goes through `Nat.*` lemmas (which unify with `Node` by `rfl`); omega is used *only* on the pure-`Nat`
size obligations after the base node `b` is stripped (`simp only [Nat.add_assoc]; Nat.add_le_add_left …`). -/

/-- Lift a `< B ∨ = c` bound to a wider `< B' ∨ = cont` when the sub-block fits (`B ≤ B'`) and its
    own continuation `c` is itself bounded (`c < B' ∨ c = cont`). The one chaining lemma for the whole
    proof; stated on `Nat`, applies to `Node` terms by `rfl`. -/
theorem orlt_mono {a c B B' cont : Nat}
    (h : a < B ∨ a = c) (hBB : B ≤ B') (hc : c < B' ∨ c = cont) : a < B' ∨ a = cont := by
  rcases h with h | h
  · exact Or.inl (Nat.lt_of_lt_of_le h hBB)
  · rw [h]; exact hc

theorem layE_bounds (e : Ast.Expr) (cont b : Node) :
    ((layE e cont b).2.2 < b + szE e ∨ (layE e cont b).2.2 = cont)
  ∧ (∀ i ∈ (layE e cont b).1, ∀ x ∈ i.succs, x < b + szE e ∨ x = cont) := by
  induction e generalizing cont b with
  | atom a => exact ⟨Or.inr rfl, by intro i hi; simp [layE] at hi⟩
  | una op e ih =>
      have hE := ih (b + szE e) b
      refine ⟨?_, ?_⟩
      · exact orlt_mono hE.1 (Nat.le_succ _) (Or.inl (Nat.lt_succ_self _))
      · intro i hi x hx
        simp only [layE] at hi
        rcases List.mem_append.1 hi with hi | hi
        · exact orlt_mono (hE.2 i hi x hx) (Nat.le_succ _) (Or.inl (Nat.lt_succ_self _))
        · simp only [List.mem_singleton] at hi; subst hi
          simp only [Cmd.succs, List.mem_singleton] at hx; subst hx; exact Or.inr rfl
  | bin op e₁ e₂ ih₁ ih₂ =>
      have h2 := ih₂ (b + szE e₁ + szE e₂) (b + szE e₁)
      have h1 := ih₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b
      have hBB1 : b + szE e₁ ≤ b + szE (.bin op e₁ e₂) := by
        simp only [szE, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hBB2 : b + szE e₁ + szE e₂ ≤ b + szE (.bin op e₁ e₂) := by
        simp only [szE, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hc2 : b + szE e₁ + szE e₂ < b + szE (.bin op e₁ e₂)
              ∨ b + szE e₁ + szE e₂ = cont :=
        Or.inl (by simp only [szE, Nat.add_assoc]; exact Nat.add_lt_add_left (by omega) b)
      have hc1 := orlt_mono h2.1 hBB2 hc2
      refine ⟨?_, ?_⟩
      · exact orlt_mono h1.1 hBB1 hc1
      · intro i hi x hx
        simp only [layE] at hi
        rcases List.mem_append.1 hi with hi | hi
        · rcases List.mem_append.1 hi with hi | hi
          · exact orlt_mono (h1.2 i hi x hx) hBB1 hc1
          · exact orlt_mono (h2.2 i hi x hx) hBB2 hc2
        · simp only [List.mem_singleton] at hi; subst hi
          simp only [Cmd.succs, List.mem_singleton] at hx; subst hx; exact Or.inr rfl

theorem layI_bounds (x : Var) (e : Ast.Expr) (cont b : Node) :
    ((layI x e cont b).2 < b + szI e ∨ (layI x e cont b).2 = cont)
  ∧ (∀ i ∈ (layI x e cont b).1, ∀ y ∈ i.succs, y < b + szI e ∨ y = cont) := by
  cases e with
  | atom a =>
      refine ⟨Or.inl ?_, ?_⟩
      · show b < b + szI (.atom a); simp only [szI]; exact Nat.lt_succ_self b
      · intro i hi y hy; simp only [layI, List.mem_singleton] at hi; subst hi
        simp only [Cmd.succs, List.mem_singleton] at hy; subst hy; exact Or.inr rfl
  | una op e =>
      have hE := layE_bounds e (b + szE e) b
      refine ⟨?_, ?_⟩
      · exact orlt_mono hE.1 (Nat.le_succ _) (Or.inl (Nat.lt_succ_self _))
      · intro i hi y hy
        simp only [layI] at hi
        rcases List.mem_append.1 hi with hi | hi
        · exact orlt_mono (hE.2 i hi y hy) (Nat.le_succ _) (Or.inl (Nat.lt_succ_self _))
        · simp only [List.mem_singleton] at hi; subst hi
          simp only [Cmd.succs, List.mem_singleton] at hy; subst hy; exact Or.inr rfl
  | bin op e₁ e₂ =>
      have h2 := layE_bounds e₂ (b + szE e₁ + szE e₂) (b + szE e₁)
      have h1 := layE_bounds e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b
      have hBB1 : b + szE e₁ ≤ b + szI (.bin op e₁ e₂) := by
        simp only [szI, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hBB2 : b + szE e₁ + szE e₂ ≤ b + szI (.bin op e₁ e₂) := by
        simp only [szI, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hc2 : b + szE e₁ + szE e₂ < b + szI (.bin op e₁ e₂)
              ∨ b + szE e₁ + szE e₂ = cont :=
        Or.inl (by simp only [szI, Nat.add_assoc]; exact Nat.add_lt_add_left (by omega) b)
      have hc1 := orlt_mono h2.1 hBB2 hc2
      refine ⟨?_, ?_⟩
      · exact orlt_mono h1.1 hBB1 hc1
      · intro i hi y hy
        simp only [layI] at hi
        rcases List.mem_append.1 hi with hi | hi
        · rcases List.mem_append.1 hi with hi | hi
          · exact orlt_mono (h1.2 i hi y hy) hBB1 hc1
          · exact orlt_mono (h2.2 i hi y hy) hBB2 hc2
        · simp only [List.mem_singleton] at hi; subst hi
          simp only [Cmd.succs, List.mem_singleton] at hy; subst hy; exact Or.inr rfl

theorem layC_bounds (c : Ast.Expr) (cont b : Node) :
    ((layC c cont b).2.2 < b + szC c ∨ (layC c cont b).2.2 = cont)
  ∧ (∀ i ∈ (layC c cont b).2.1, ∀ y ∈ i.succs, y < b + szC c ∨ y = cont) := by
  cases c with
  | atom a =>
      cases a with
      | var x => exact ⟨Or.inr rfl, by intro i hi; simp [layC] at hi⟩
      | imm n =>
          refine ⟨Or.inl ?_, ?_⟩
          · show b < b + szC (.atom (.imm n)); simp only [szC, szI]; exact Nat.lt_succ_self b
          · intro i hi y hy; simp only [layC, List.mem_singleton] at hi; subst hi
            simp only [Cmd.succs, List.mem_singleton] at hy; subst hy; exact Or.inr rfl
  | una op e => simpa only [layC, szC] using layI_bounds (.tmp b) (.una op e) cont b
  | bin op e₁ e₂ => simpa only [layC, szC] using layI_bounds (.tmp b) (.bin op e₁ e₂) cont b

theorem layS_bounds (s : Stmt) (cont b : Node) :
    ((layS s cont b).2 < b + szS s ∨ (layS s cont b).2 = cont)
  ∧ (∀ i ∈ (layS s cont b).1, ∀ y ∈ i.succs, y < b + szS s ∨ y = cont) := by
  induction s generalizing cont b with
  | skip => exact ⟨Or.inr rfl, by intro i hi; simp [layS] at hi⟩
  | assign x e => simpa only [layS, szS] using layI_bounds x e cont b
  | seq s₁ s₂ ih₁ ih₂ =>
      have h2 := ih₂ cont (b + szS s₁)
      have h1 := ih₁ (layS s₂ cont (b + szS s₁)).2 b
      have hBB1 : b + szS s₁ ≤ b + szS (.seq s₁ s₂) := by
        simp only [szS]; exact Nat.add_le_add_left (by omega) b
      have hBB2 : b + szS s₁ + szS s₂ ≤ b + szS (.seq s₁ s₂) := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hc1 := orlt_mono h2.1 hBB2 (Or.inr rfl)
      refine ⟨?_, ?_⟩
      · exact orlt_mono h1.1 hBB1 hc1
      · intro i hi y hy
        simp only [layS] at hi
        rcases List.mem_append.1 hi with hi | hi
        · exact orlt_mono (h1.2 i hi y hy) hBB1 hc1
        · exact orlt_mono (h2.2 i hi y hy) hBB2 (Or.inr rfl)
  | ite c t e ihT ihE =>
      have hC := layC_bounds c (b + szC c) b
      have hT := ihT cont (b + szC c + 1)
      have hE := ihE cont (b + szC c + 1 + szS t)
      have hBBc : b + szC c ≤ b + szS (.ite c t e) := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hcc : b + szC c < b + szS (.ite c t e) ∨ b + szC c = cont :=
        Or.inl (by simp only [szS, Nat.add_assoc]; exact Nat.add_lt_add_left (by omega) b)
      have hBBt : b + szC c + 1 + szS t ≤ b + szS (.ite c t e) := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hBBe : b + szC c + 1 + szS t + szS e ≤ b + szS (.ite c t e) := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      refine ⟨?_, ?_⟩
      · exact orlt_mono hC.1 hBBc hcc
      · intro i hi y hy
        simp only [layS] at hi
        rcases List.mem_append.1 hi with hi | hi
        · rcases List.mem_append.1 hi with hi | hi
          · rcases List.mem_append.1 hi with hi | hi
            · exact orlt_mono (hC.2 i hi y hy) hBBc hcc
            · simp only [List.mem_singleton] at hi; subst hi
              simp only [Cmd.succs, List.mem_cons, List.not_mem_nil,
                or_false] at hy
              rcases hy with hy | hy <;> subst hy
              · exact orlt_mono hE.1 hBBe (Or.inr rfl)
              · exact orlt_mono hT.1 hBBt (Or.inr rfl)
          · exact orlt_mono (hT.2 i hi y hy) hBBt (Or.inr rfl)
        · exact orlt_mono (hE.2 i hi y hy) hBBe (Or.inr rfl)
  | «while» c b' ihB =>
      have hC := layC_bounds c (b + szC c) b
      have hB := ihB (layC c (b + szC c) b).2.2 (b + szC c + 1)
      have hBBc : b + szC c ≤ b + szS (.while c b') := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      have hcc : b + szC c < b + szS (.while c b') ∨ b + szC c = cont :=
        Or.inl (by simp only [szS, Nat.add_assoc]; exact Nat.add_lt_add_left (by omega) b)
      -- the body now continues to the condition entry `cEntry`, itself bounded by `hC.1`
      have hccB := orlt_mono hC.1 hBBc hcc
      have hBBb : b + szC c + 1 + szS b' ≤ b + szS (.while c b') := by
        simp only [szS, Nat.add_assoc]; exact Nat.add_le_add_left (by omega) b
      refine ⟨?_, ?_⟩
      · exact orlt_mono hC.1 hBBc hcc
      · intro i hi y hy
        simp only [layS] at hi
        rcases List.mem_append.1 hi with hi | hi
        · rcases List.mem_append.1 hi with hi | hi
          · exact orlt_mono (hC.2 i hi y hy) hBBc hcc
          · simp only [List.mem_singleton] at hi; subst hi
            simp only [Cmd.succs, List.mem_cons, List.not_mem_nil,
              or_false] at hy
            rcases hy with hy | hy <;> subst hy
            · exact Or.inr rfl
            · exact orlt_mono hB.1 hBBb hccB
        · exact orlt_mono (hB.2 i hi y hy) hBBb hccB

/-- The lowered program has `szS s + 1` nodes (the `halt` plus the laid block). -/
theorem lower_size (s : Stmt) : (lower s).size = szS s + 1 := by
  simp only [lower, Program.size, List.size_toArray, List.length_cons, layS_len]

/-- A `< 1 + szS s ∨ = 0` bound (the `cont = 0`, `b = 1` instance of `layS_bounds`) puts a label below
    `szS s + 1 = (lower s).size`. Done by hand (`omega` cannot see `Node`). -/
private theorem lt_size_of_bound {s : Stmt} {m : Node}
    (h : m < 1 + szS s ∨ m = 0) : m < szS s + 1 := by
  rcases h with h | h
  · rw [Nat.add_comm]; exact h
  · rw [h]; exact Nat.succ_pos _

/-- The lowered program is `WellFormed` (no control edge leaves the graph). -/
theorem lower_wellFormed (s : Stmt) : WellFormed (lower s) := by
  have hb := layS_bounds s 0 1
  constructor
  · -- entry in range
    rw [lower_size]
    show (layS s 0 1).2 < szS s + 1
    exact lt_size_of_bound hb.1
  · -- successors in range
    intro n instr s' hf hs'
    rw [lower_size]
    -- `lower`'s code is `(halt :: laidCode).toArray`
    have hfetch : (lower s).fetch n
        = (Cmd.halt :: (layS s 0 1).1).toArray[n]? := rfl
    rw [hfetch, List.getElem?_toArray] at hf
    cases n with
    | zero =>
        rw [List.getElem?_cons_zero] at hf
        injection hf with hf; subst hf; simp [Cmd.succs] at hs'
    | succ k =>
        rw [List.getElem?_cons_succ] at hf
        -- `instr` is the `k`-th laid instruction; use its membership in the code list
        have hk : k < (layS s 0 1).1.length := by
          rcases Nat.lt_or_ge k (layS s 0 1).1.length with h | h
          · exact h
          · rw [List.getElem?_eq_none h] at hf; exact absurd hf (by simp)
        have hmem : instr ∈ (layS s 0 1).1 := by
          rw [List.getElem?_eq_getElem hk] at hf; injection hf with hf
          exact hf ▸ List.getElem_mem hk
        exact lt_size_of_bound (hb.2 instr hmem s' hs')

end AstToTac

end BaseLanguage
