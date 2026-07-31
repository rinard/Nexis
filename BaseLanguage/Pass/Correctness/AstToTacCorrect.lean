-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.AstToTac
import BaseLanguage.Backend.Correctness.CodegenForward

namespace BaseLanguage

/-!
# `AstToTacCorrect` — forward simulation for the AST→TAC lowering (`lower_correct`)

The frontend half of the AST→ASM pipeline. We prove that whenever the reference interpreter
`Ast.evalS` runs the surface statement `s` to a result store `σ'`, the lowered CFG `lower s` *steps*
(`Semantics.Steps`) from its entry to a `halt`, in a TAC store agreeing with `σ'` on the **source**
(`.orig`) variables. Composed with the backend's `TacToAsm.codegen_simulates`, this yields the
end-to-end `ast_to_asm` headline.

Layout of the proof:
* **A** — `CodeAt`, a `fetch`-based code-embedding predicate (analogue of the backend's `Asm.Embeds`).
* **B/C** — expression simulation for `layE`/`layI`/`layC`, threading a freshness frame.
* **D** — statement simulation `layS_correct`, the main induction.
* **E** — `lower_correct` and the composed `ast_to_asm`.
-/

namespace AstToTac

open Tac Ast Semantics

/-! ## A. `CodeAt` — `P` contains the instruction list `l` at consecutive nodes from `b`.

The `fetch`-based mirror of the backend's `Asm.Embeds`; the lemmas track it one-for-one. -/

/-- `P` contains the instruction list `l` at consecutive nodes from `b`. -/
def CodeAt (P : Program) (b : Nat) (l : List Cmd) : Prop :=
  ∀ k, k < l.length → P.fetch (b + k) = l[k]?

theorem CodeAt.head {P : Program} {b : Nat} {i : Cmd} {l : List Cmd}
    (h : CodeAt P b (i :: l)) : P.fetch b = some i := by
  have := h 0 (by simp); simpa using this

theorem CodeAt.get0 {P : Program} {b : Nat} {l : List Cmd}
    (h : CodeAt P b l) (hl : 0 < l.length) : P.fetch b = l[0]? := by
  have := h 0 hl; rwa [Nat.add_zero] at this

theorem CodeAt.tail {P : Program} {b : Nat} {i : Cmd} {l : List Cmd}
    (h : CodeAt P b (i :: l)) : CodeAt P (b + 1) l := by
  intro k hk
  have := h (k + 1) (by simp only [List.length_cons]; omega)
  rwa [show b + (k + 1) = b + 1 + k from by omega, List.getElem?_cons_succ] at this

theorem CodeAt.append_left {P : Program} {b : Nat} {l₁ l₂ : List Cmd}
    (h : CodeAt P b (l₁ ++ l₂)) : CodeAt P b l₁ := by
  intro k hk
  have := h k (by rw [List.length_append]; omega)
  rwa [List.getElem?_append_left hk] at this

theorem CodeAt.append_right {P : Program} {b : Nat} {l₁ l₂ : List Cmd}
    (h : CodeAt P b (l₁ ++ l₂)) : CodeAt P (b + l₁.length) l₂ := by
  intro k hk
  have := h (l₁.length + k) (by rw [List.length_append]; omega)
  rw [show b + (l₁.length + k) = b + l₁.length + k from by omega,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at this
  exact this

/-- Value-fetch at a position inside the embedded list. -/
theorem CodeAt.get {P : Program} {b : Nat} {l : List Cmd} {k : Nat}
    (h : CodeAt P b l) (hk : k < l.length) : P.fetch (b + k) = some l[k] := by
  rw [h k hk, List.getElem?_eq_getElem hk]

/-! ### `lower` setup: node 0 is `halt`; the laid block sits at base 1. -/

/-- The lowered program's node `0` holds `halt`. -/
theorem lower_fetch_zero (s : Stmt) : (lower s).fetch 0 = some .halt := by
  show (Cmd.halt :: (layS s 0 1).1).toArray[0]? = some .halt
  rw [List.getElem?_toArray]; rfl

/-- The laid statement block is embedded at base node `1` of the lowered program. -/
theorem lower_codeAt (s : Stmt) : CodeAt (lower s) 1 (layS s 0 1).1 := by
  intro k hk
  show (Cmd.halt :: (layS s 0 1).1).toArray[1 + k]? = (layS s 0 1).1[k]?
  rw [List.getElem?_toArray, Nat.add_comm 1 k, List.getElem?_cons_succ]

/-- One step is a (one-element) run. -/
theorem Steps.singleton {P : Program} {c c' : Config} (h : Step P c c') : Steps P c c' :=
  Steps.tail Steps.refl h

/-- Transitivity of `Steps` (local copy; avoids depending on the opt-pass modules). -/
theorem Steps.trans {P : Program} {a b c : Config}
    (h1 : Steps P a b) (h2 : Steps P b c) : Steps P a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact Steps.tail ih hstep

/-! ## B. Source well-formedness, store agreement, and the freshness frame.

Surface expressions/statements mention only source (`.orig`) variables and immediates — never a
`.tmp`, whose namespace `AstToTac` reserves for its scratch holding variables. `noTmp` captures this
surface invariant; without it a source read of `.tmp i` could alias an inserted temp. -/

/-- An atom mentions no temporary. -/
def Atom.noTmp : Atom → Prop
  | .var (.tmp _) => False
  | _             => True

/-- A surface expression mentions no temporary (only source vars / immediates). -/
def Expr.noTmp : Ast.Expr → Prop
  | .atom a      => Atom.noTmp a
  | .una _ e     => Expr.noTmp e
  | .bin _ e₁ e₂ => Expr.noTmp e₁ ∧ Expr.noTmp e₂

/-- A surface statement mentions no temporary. -/
def Stmt.noTmp : Stmt → Prop
  | .skip        => True
  | .assign x e  => (∀ i, x ≠ .tmp i) ∧ Expr.noTmp e
  | .seq s₁ s₂   => Stmt.noTmp s₁ ∧ Stmt.noTmp s₂
  | .ite c t e   => Expr.noTmp c ∧ Stmt.noTmp t ∧ Stmt.noTmp e
  | .while c b   => Expr.noTmp c ∧ Stmt.noTmp b

/-- The TAC store agrees with the AST store on all **source** (`.orig`) variables. The two stores share
    the `Var`/`Store` type; temporaries are scratch and need not agree. -/
def AgreeOrig (σT σ : Store) : Prop := ∀ s : String, σT (.orig s) = σ (.orig s)

/-- A variable is **untouched below `b`**: a source var, or a temp with index `< b`. The freshness
    frame preserves exactly these. -/
def Untouched (b : Nat) : Var → Prop
  | .orig _ => True
  | .tmp i  => i < b

/-- **Freshness frame**: `σ'` agrees with `σ` on every variable untouched below `b` — i.e. lowering a
    block at base `b` writes only temps with index `≥ b`. -/
def Frame (b : Nat) (σ σ' : Store) : Prop := ∀ x, Untouched b x → σ' x = σ x

theorem Frame.refl {b : Nat} {σ : Store} : Frame b σ σ := fun _ _ => rfl

/-- A frame at a lower base is also a frame at a higher base, on its (smaller) untouched set. -/
theorem Frame.mono {b b' : Nat} {σ σ' : Store} (h : Frame b σ σ') (hbb : b' ≤ b) :
    Frame b' σ σ' := by
  intro x hx
  refine h x ?_
  cases x with
  | orig _ => exact trivial
  | tmp i  => exact Nat.lt_of_lt_of_le hx hbb

/-- An atom is **stable below `B`**: evaluating it is unaffected by writes at temps `≥ B`. -/
def AtomStable (B : Nat) : Atom → Prop
  | .imm _          => True
  | .var (.orig _)  => True
  | .var (.tmp j)   => j < B

/-- A frame below `B` preserves the value of any atom stable below `B`. -/
theorem evalAtom_frame {B : Nat} {σ σ' : Store} {a : Atom}
    (hf : Frame B σ σ') (ha : AtomStable B a) :
    Semantics.evalAtom σ' a = Semantics.evalAtom σ a := by
  cases a with
  | imm n => rfl
  | var x =>
      cases x with
      | orig s => exact hf (.orig s) trivial
      | tmp j  => exact hf (.tmp j) ha

/-- Source-variable agreement preserves the value of any temp-free atom. -/
theorem evalAtom_agree {σT σ : Store} {a : Atom}
    (hag : AgreeOrig σT σ) (ha : Atom.noTmp a) :
    Semantics.evalAtom σT a = Semantics.evalAtom σ a := by
  cases a with
  | imm n => rfl
  | var x =>
      cases x with
      | orig s => exact hag s
      | tmp j  => exact absurd ha (by simp [Atom.noTmp])

/-! ## C. Expression simulation — `layE`, `layI`, `layC`.

The result atom of `layE e _ b` lies "below `b + szE e`" (an immediate, a source var, or a temp with
index `< b + szE e`), so a later sibling laid at base `b + szE e` cannot clobber it. -/

/-- The result atom of `layE e cont b` is stable below `b + szE e`. -/
theorem layE_result_stable (e : Ast.Expr) (cont b : Nat) (hnt : Expr.noTmp e) :
    AtomStable (b + szE e) (layE e cont b).2.1 := by
  cases e with
  | atom a =>
      cases a with
      | imm n => exact trivial
      | var x =>
          cases x with
          | orig s => exact trivial
          | tmp j  => exact absurd hnt (by simp [Expr.noTmp, Atom.noTmp])
  | una op e =>
      show AtomStable (b + szE (.una op e)) (.var (.tmp (b + szE e)))
      simp only [AtomStable, szE]; omega
  | bin op e₁ e₂ =>
      show AtomStable (b + szE (.bin op e₁ e₂)) (.var (.tmp (b + szE e₁ + szE e₂)))
      simp only [AtomStable, szE]; omega

/-- The AST and TAC atom evaluators coincide (they share the definition). -/
theorem ast_evalAtom_eq (σ : Store) (a : Atom) : Ast.evalAtom σ a = Semantics.evalAtom σ a := by
  cases a <;> rfl

theorem Store.update_ne {σ : Store} {x y : Var} {v : Val} (h : y ≠ x) :
    (σ.update x v) y = σ y := by simp only [Store.update, if_neg h]

theorem Store.update_self {σ : Store} {x : Var} {v : Val} : (σ.update x v) x = v := by
  simp [Store.update]

/-- Forward decomposition of a faulting-free `bin` evaluation (left-to-right). -/
theorem evalE_bin {σ : Store} {op : Binop} {e₁ e₂ : Ast.Expr} {v : Val}
    (h : evalE σ (.bin op e₁ e₂) = some v) :
    ∃ a b', evalE σ e₁ = some a ∧ evalE σ e₂ = some b' ∧ op.denote a b' = some v := by
  simp only [evalE] at h
  cases hee₁ : evalE σ e₁ with
  | none => rw [hee₁] at h; simp at h
  | some a =>
    cases hee₂ : evalE σ e₂ with
    | none => rw [hee₁, hee₂] at h; simp at h
    | some b' => rw [hee₁, hee₂] at h; exact ⟨a, b', rfl, rfl, h⟩

/-- **Expression simulation (`layE`).** If `evalE σ e = some v`, the TAC store `σT` agrees with `σ` on
    source vars, and `P` embeds the block `(layE e cont b).1` at base `b`, then `P` steps from the
    block entry `(layE e cont b).2.2` to the continuation `cont`, in a store `σT'` that (i) still agrees
    with `σ` on source vars, (ii) differs from `σT` only on temps `≥ b` (freshness frame), and (iii)
    holds `v` in the result atom `(layE e cont b).2.1`. -/
theorem layE_correct {P : Program} :
    ∀ (e : Ast.Expr) {cont b : Nat} {σT σ : Store} {v : Val},
      Expr.noTmp e →
      CodeAt P b (layE e cont b).1 →
      AgreeOrig σT σ →
      evalE σ e = some v →
    ∃ σT', Steps P ⟨(layE e cont b).2.2, σT⟩ ⟨cont, σT'⟩
         ∧ AgreeOrig σT' σ
         ∧ Frame b σT σT'
         ∧ Semantics.evalAtom σT' (layE e cont b).2.1 = v := by
  intro e
  induction e with
  | atom a =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [evalE] at hv
      refine ⟨σT, Steps.refl, hag, Frame.refl, ?_⟩
      show Semantics.evalAtom σT a = v
      rw [evalAtom_agree hag hnt, ← ast_evalAtom_eq]
      exact Option.some.inj hv
  | una op e ih =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [evalE, Option.map_eq_some_iff] at hv
      obtain ⟨a, hea, hva⟩ := hv
      -- unfold the una layout
      simp only [layE] at hcode ⊢
      -- sub-block embeds at base b; final assign at node opNode = b + szE e
      have hcode_e : CodeAt P b (layE e (b + szE e) b).1 := hcode.append_left
      obtain ⟨σ1, hsteps, hag1, hfr1, hval1⟩ := ih (cont := b + szE e) (b := b) hnt hcode_e hag hea
      -- fetch the final assign
      have hassign : P.fetch (b + szE e) = some (.assign (.tmp (b + szE e)) (.una op (layE e (b + szE e) b).2.1) cont) := by
        have h := hcode.append_right (l₁ := (layE e (b + szE e) b).1)
        rw [layE_len] at h
        exact h.head
      refine ⟨σ1.update (.tmp (b + szE e)) v, ?_, ?_, ?_, ?_⟩
      · refine Steps.trans hsteps (Steps.singleton (Step.assign hassign ?_))
        show Semantics.eval σ1 (.una op (layE e (b + szE e) b).2.1) = some v
        simp only [Semantics.eval, hval1, hva]
      · intro s
        show (σ1.update (.tmp (b + szE e)) v) (.orig s) = σ (.orig s)
        rw [Store.update_ne (by simp)]; exact hag1 s
      · intro x hx
        show (σ1.update (.tmp (b + szE e)) v) x = σT x
        have hne : x ≠ .tmp (b + szE e) := by
          cases x with
          | orig _ => simp
          | tmp j  => simp only [Untouched] at hx; intro h; injection h with h; omega
        rw [Store.update_ne hne]; exact hfr1 x hx
      · show Semantics.evalAtom (σ1.update (.tmp (b + szE e)) v) (.var (.tmp (b + szE e))) = v
        show (σ1.update (.tmp (b + szE e)) v) (.tmp (b + szE e)) = v
        rw [Store.update_self]
  | bin op e₁ e₂ ih₁ ih₂ =>
      intro cont b σT σ v hnt hcode hag hv
      obtain ⟨hnt₁, hnt₂⟩ := hnt
      -- decompose the AST evaluation left-to-right
      obtain ⟨a, b', hee₁, hee₂, hv⟩ := evalE_bin hv   -- hv : op.denote a b' = some v
      simp only [layE] at hcode ⊢
      -- reassociate the embedded code  (A ++ B) ++ C  ↦  A ++ (B ++ C)
      rw [List.append_assoc] at hcode
      -- e₁ embeds at base b, continuing to e₂'s entry
      have hcode₁ : CodeAt P b
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1 :=
        hcode.append_left
      obtain ⟨σ1, hsteps1, hag1, hfr1, hval1⟩ :=
        ih₁ (cont := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2) (b := b)
          hnt₁ hcode₁ hag hee₁
      -- e₂ embeds at base b + szE e₁, continuing to opNode
      have hBC := hcode.append_right
        (l₁ := (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1)
      rw [layE_len] at hBC
      have hcode₂ : CodeAt P (b + szE e₁) (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1 :=
        hBC.append_left
      obtain ⟨σ2, hsteps2, hag2, hfr2, hval2⟩ :=
        ih₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
      -- fetch the final assign at opNode = b + szE e₁ + szE e₂
      have hassign : P.fetch (b + szE e₁ + szE e₂)
          = some (.assign (.tmp (b + szE e₁ + szE e₂))
              (.bin op (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
                       (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) cont) := by
        have hC := hBC.append_right (l₁ := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1)
        rw [layE_len] at hC
        exact hC.head
      -- e₁'s result atom is stable below b + szE e₁, so e₂'s frame preserves its value
      have hstable₁ : AtomStable (b + szE e₁)
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 :=
        layE_result_stable e₁ _ b hnt₁
      have hval1' : Semantics.evalAtom σ2
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 = a := by
        rw [evalAtom_frame hfr2 hstable₁]; exact hval1
      refine ⟨σ2.update (.tmp (b + szE e₁ + szE e₂)) v, ?_, ?_, ?_, ?_⟩
      · refine Steps.trans hsteps1 (Steps.trans hsteps2 (Steps.singleton (Step.assign hassign ?_)))
        show Semantics.eval σ2 (.bin op
              (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
              (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) = some v
        simp only [Semantics.eval, hval1', hval2]; exact hv
      · intro s
        show (σ2.update (.tmp (b + szE e₁ + szE e₂)) v) (.orig s) = σ (.orig s)
        rw [Store.update_ne (by simp)]; exact hag2 s
      · intro x hx
        show (σ2.update (.tmp (b + szE e₁ + szE e₂)) v) x = σT x
        have hne : x ≠ .tmp (b + szE e₁ + szE e₂) := by
          cases x with
          | orig _ => simp
          | tmp j  => simp only [Untouched] at hx; intro h; injection h with h; omega
        rw [Store.update_ne hne]
        -- compose the two frames down to base b
        have hx2 : Untouched (b + szE e₁) x := by
          cases x with
          | orig _ => exact trivial
          | tmp j  => simp only [Untouched] at hx ⊢; omega
        rw [hfr2 x hx2]; exact hfr1 x hx
      · show Semantics.evalAtom (σ2.update (.tmp (b + szE e₁ + szE e₂)) v)
          (.var (.tmp (b + szE e₁ + szE e₂))) = v
        show (σ2.update (.tmp (b + szE e₁ + szE e₂)) v) (.tmp (b + szE e₁ + szE e₂)) = v
        rw [Store.update_self]

/-- **`layI` simulation.** Like `layE`, but writes the result straight into `x`: running the block
    reaches `cont` in a store holding `v` at `x`, with everything off `x` and below base `b` preserved.
    (No induction — delegates to `layE_correct` on the sub-expressions.) -/
theorem layI_correct {P : Program} (x : Var) :
    ∀ (e : Ast.Expr) {cont b : Nat} {σT σ : Store} {v : Val},
      Expr.noTmp e →
      CodeAt P b (layI x e cont b).1 →
      AgreeOrig σT σ →
      evalE σ e = some v →
    ∃ σT', Steps P ⟨(layI x e cont b).2, σT⟩ ⟨cont, σT'⟩
         ∧ σT' x = v
         ∧ ∀ y, y ≠ x → Untouched b y → σT' y = σT y := by
  intro e
  cases e with
  | atom a =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [evalE] at hv
      simp only [layI] at hcode ⊢
      have hfetch : P.fetch b = some (.assign x (.atom a) cont) := hcode.head
      have heval : Semantics.eval σT (.atom a) = some v := by
        show some (Semantics.evalAtom σT a) = some v
        rw [evalAtom_agree hag hnt, ← ast_evalAtom_eq]; exact hv
      exact ⟨σT.update x v, Steps.singleton (Step.assign hfetch heval), Store.update_self,
        fun y hy _ => Store.update_ne hy⟩
  | una op e =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [evalE, Option.map_eq_some_iff] at hv
      obtain ⟨a, hea, hva⟩ := hv
      simp only [layI] at hcode ⊢
      have hcode_e : CodeAt P b (layE e (b + szE e) b).1 := hcode.append_left
      obtain ⟨σ1, hsteps, hag1, hfr1, hval1⟩ :=
        layE_correct e (cont := b + szE e) (b := b) hnt hcode_e hag hea
      have hassign : P.fetch (b + szE e)
          = some (.assign x (.una op (layE e (b + szE e) b).2.1) cont) := by
        have h := hcode.append_right (l₁ := (layE e (b + szE e) b).1)
        rw [layE_len] at h
        exact h.head
      refine ⟨σ1.update x v, ?_, Store.update_self, ?_⟩
      · refine Steps.trans hsteps (Steps.singleton (Step.assign hassign ?_))
        show Semantics.eval σ1 (.una op (layE e (b + szE e) b).2.1) = some v
        simp only [Semantics.eval, hval1, hva]
      · intro y hy hyu; rw [Store.update_ne hy]; exact hfr1 y hyu
  | bin op e₁ e₂ =>
      intro cont b σT σ v hnt hcode hag hv
      obtain ⟨hnt₁, hnt₂⟩ := hnt
      obtain ⟨a, b', hee₁, hee₂, hv⟩ := evalE_bin hv
      simp only [layI] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcode₁ : CodeAt P b
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1 :=
        hcode.append_left
      obtain ⟨σ1, hsteps1, hag1, hfr1, hval1⟩ :=
        layE_correct e₁ (cont := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2) (b := b)
          hnt₁ hcode₁ hag hee₁
      have hBC := hcode.append_right
        (l₁ := (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1)
      rw [layE_len] at hBC
      have hcode₂ : CodeAt P (b + szE e₁) (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1 :=
        hBC.append_left
      obtain ⟨σ2, hsteps2, hag2, hfr2, hval2⟩ :=
        layE_correct e₂ (cont := b + szE e₁ + szE e₂) (b := b + szE e₁) hnt₂ hcode₂ hag1 hee₂
      have hassign : P.fetch (b + szE e₁ + szE e₂)
          = some (.assign x
              (.bin op (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
                       (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) cont) := by
        have hC := hBC.append_right (l₁ := (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1)
        rw [layE_len] at hC
        exact hC.head
      have hstable₁ : AtomStable (b + szE e₁)
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 :=
        layE_result_stable e₁ _ b hnt₁
      have hval1' : Semantics.evalAtom σ2
          (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1 = a := by
        rw [evalAtom_frame hfr2 hstable₁]; exact hval1
      refine ⟨σ2.update x v, ?_, Store.update_self, ?_⟩
      · refine Steps.trans hsteps1 (Steps.trans hsteps2 (Steps.singleton (Step.assign hassign ?_)))
        show Semantics.eval σ2 (.bin op
              (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).2.1
              (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.1) = some v
        simp only [Semantics.eval, hval1', hval2]; exact hv
      · intro y hy hyu
        rw [Store.update_ne hy]
        have hyu2 : Untouched (b + szE e₁) y := by
          cases y with
          | orig _ => exact trivial
          | tmp j  => simp only [Untouched] at hyu ⊢; omega
        rw [hfr2 y hyu2]; exact hfr1 y hyu

/-- **`layC` simulation.** Materialises the condition value into the result var `(layC c cont b).1`:
    running the block reaches `cont` with that var holding `v`, source vars still agreeing, and
    everything off the result var and below `b` preserved. -/
theorem layC_correct {P : Program} :
    ∀ (c : Ast.Expr) {cont b : Nat} {σT σ : Store} {v : Val},
      Expr.noTmp c →
      CodeAt P b (layC c cont b).2.1 →
      AgreeOrig σT σ →
      evalE σ c = some v →
    ∃ σT', Steps P ⟨(layC c cont b).2.2, σT⟩ ⟨cont, σT'⟩
         ∧ σT' (layC c cont b).1 = v
         ∧ AgreeOrig σT' σ
         ∧ ∀ y, y ≠ (layC c cont b).1 → Untouched b y → σT' y = σT y := by
  intro c
  cases c with
  | atom a =>
      cases a with
      | var x =>
          intro cont b σT σ v hnt hcode hag hv
          simp only [evalE] at hv
          simp only [layC]
          refine ⟨σT, Steps.refl, ?_, hag, fun y _ _ => rfl⟩
          show σT x = v
          cases x with
          | orig s => rw [hag s]; exact Option.some.inj hv
          | tmp j  => simp [Expr.noTmp, Atom.noTmp] at hnt
      | imm n =>
          intro cont b σT σ v hnt hcode hag hv
          simp only [evalE] at hv
          simp only [layC] at hcode ⊢
          have hfetch : P.fetch b = some (.assign (.tmp b) (.atom (.imm n)) cont) := hcode.head
          have heval : Semantics.eval σT (.atom (.imm n)) = some v := by
            show some (Semantics.evalAtom σT (.imm n)) = some v
            exact hv
          refine ⟨σT.update (.tmp b) v, Steps.singleton (Step.assign hfetch heval),
            Store.update_self, ?_, fun y hy _ => Store.update_ne hy⟩
          intro s; rw [Store.update_ne (by simp)]; exact hag s
  | una op e =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [layC] at hcode ⊢
      obtain ⟨σT', hsteps, hxv, hfr⟩ := layI_correct (.tmp b) (.una op e) hnt hcode hag hv
      refine ⟨σT', hsteps, hxv, ?_, fun y hy hyu => hfr y hy hyu⟩
      intro s; rw [hfr (.orig s) (by simp) trivial]; exact hag s
  | bin op e₁ e₂ =>
      intro cont b σT σ v hnt hcode hag hv
      simp only [layC] at hcode ⊢
      obtain ⟨σT', hsteps, hxv, hfr⟩ := layI_correct (.tmp b) (.bin op e₁ e₂) hnt hcode hag hv
      refine ⟨σT', hsteps, hxv, ?_, fun y hy hyu => hfr y hy hyu⟩
      intro s; rw [hfr (.orig s) (by simp) trivial]; exact hag s

/-! ## D. Statement simulation — `layS_correct` (the main induction). -/

/-- After an `assign x ↦ v`, source agreement is restored: the TAC store (holding `v` at `x` and
    otherwise frame-preserved) agrees with the updated AST store `upd σ x v` on all source vars. -/
theorem agree_after_assign {σT' σT σ : Store} {xv : Var} {bv : Val} {b' : Nat}
    (hag : AgreeOrig σT σ) (hval : σT' xv = bv)
    (hfr : ∀ y, y ≠ xv → Untouched b' y → σT' y = σT y) :
    AgreeOrig σT' (Ast.upd σ xv bv) := by
  intro s
  show σT' (.orig s) = (if (Var.orig s) = xv then bv else σ (.orig s))
  by_cases h : (Var.orig s) = xv
  · rw [if_pos h, h]; exact hval
  · rw [if_neg h, hfr (.orig s) h trivial]; exact hag s

/-- A nonzero condition value (`¬ (bv == 0)`) is propositionally nonzero. -/
theorem val_ne_zero_of_beq_false {bv : Val} (h : ¬ (bv == 0) = true) : bv ≠ 0 := by
  intro hb; apply h; rw [hb]; decide

/-- **Statement simulation.** If the reference interpreter runs `s` (with loop-fuel `fuel`) from `σ` to
    `σ'`, the TAC store `σT` agrees with `σ` on source vars, and `P` embeds the block `(layS s cont b).1`
    at base `b`, then `P` steps from the block entry `(layS s cont b).2` to `cont` in a store still
    agreeing with `σ'` on source vars. Proved by `evalS.induct` (structural on `s`, fuel-decreasing on
    `while`). -/
theorem layS_correct {P : Program} (fuel : Nat) (s : Stmt) (σ : Store) :
    ∀ {cont b : Nat} {σT σ' : Store},
      Stmt.noTmp s →
      CodeAt P b (layS s cont b).1 →
      AgreeOrig σT σ →
      evalS fuel s σ = .ok σ' →
    ∃ σT', Steps P ⟨(layS s cont b).2, σT⟩ ⟨cont, σT'⟩ ∧ AgreeOrig σT' σ' := by
  induction fuel, s, σ using evalS.induct with
  | case1 fuel σ =>   -- skip
      intro cont b σT σ' hnt hcode hag hev
      simp only [evalS] at hev
      injection hev with hev; subst hev
      simp only [layS]
      exact ⟨σT, Steps.refl, hag⟩
  | case2 fuel xv e σ bv heq =>   -- assign, evalE = some
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨_, hnte⟩ := hnt
      simp only [evalS, heq] at hev
      simp only [layS] at hcode ⊢
      obtain ⟨σT', hsteps, hxv, hfr⟩ := layI_correct xv e hnte hcode hag heq
      injection hev with hev; subst hev
      exact ⟨σT', hsteps, agree_after_assign hag hxv hfr⟩
  | case3 fuel xv e σ heq =>   -- assign, evalE = none (faults — vacuous)
      intro cont b σT σ' hnt hcode hag hev
      simp [evalS, heq] at hev
  | case4 fuel s1 s2 σ σmid hmid ih1 ih2 =>   -- seq, first ok
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨hnt1, hnt2⟩ := hnt
      simp only [evalS, hmid] at hev
      simp only [layS] at hcode ⊢
      have hcode1 : CodeAt P b (layS s1 (layS s2 cont (b + szS s1)).2 b).1 := hcode.append_left
      have hcode2 := hcode.append_right (l₁ := (layS s1 (layS s2 cont (b + szS s1)).2 b).1)
      rw [layS_len] at hcode2
      obtain ⟨σ1, hs1, hag1⟩ := ih1 hnt1 hcode1 hag hmid
      obtain ⟨σ2, hs2, hag2⟩ := ih2 hnt2 hcode2 hag1 hev
      exact ⟨σ2, Steps.trans hs1 hs2, hag2⟩
  | case5 fuel s1 s2 σ hfail ih1 =>   -- seq, first not ok (vacuous)
      intro cont b σT σ' hnt hcode hag hev
      simp only [evalS] at hev
      cases hm : evalS fuel s1 σ with
      | ok σmid => exact (hfail σmid hm).elim
      | fault => rw [hm] at hev; simp at hev
      | timeout => rw [hm] at hev; simp at hev
  | case6 fuel c t e σ bv heq hz ihe =>   -- ite, cond = 0 (else branch)
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨hntc, hntt, hnte⟩ := hnt
      simp only [evalS, heq, hz] at hev
      simp only [layS] at hcode ⊢
      -- reassociate ((A ++ B) ++ C) ++ D ↦ A ++ (B ++ (C ++ D))
      rw [List.append_assoc, List.append_assoc] at hcode
      -- A = layC code; materialize the condition
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      -- B = [ifz];  ifz at b + szC c
      have hBCD := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBCD
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1
          (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2) := hBCD.head
      -- C = t-block, D = e-block;  CodeAt for the e-block (taken branch)
      have hCD := hBCD.tail
      have hcodeE0 := hCD.append_right (l₁ := (layS t cont (b + szC c + 1)).1)
      rw [layS_len] at hcodeE0
      -- run the e-branch
      have hcz : σTc (layC c (b + szC c) b).1 = 0 := by rw [hxc]; exact eq_of_beq hz
      obtain ⟨σ2, hsE, hag2⟩ := ihe hnte hcodeE0 hagc hev
      refine ⟨σ2, ?_, hag2⟩
      exact Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzT hifz hcz)) hsE)
  | case7 fuel c t e σ bv heq hnz iht =>   -- ite, cond ≠ 0 (then branch)
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨hntc, hntt, hnte⟩ := hnt
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
      -- run the t-branch
      have hcne : σTc (layC c (b + szC c) b).1 ≠ 0 := by
        rw [hxc]; exact val_ne_zero_of_beq_false (by rw [hnz]; exact Bool.false_ne_true)
      obtain ⟨σ2, hsT, hag2⟩ := iht hntt hcodeT0 hagc hev
      refine ⟨σ2, ?_, hag2⟩
      exact Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzF hifz hcne)) hsT)
  | case8 fuel c t e σ heq =>   -- ite, cond faults (vacuous)
      intro cont b σT σ' hnt hcode hag hev
      simp [evalS, heq] at hev
  | case9 c bd σ =>   -- while, fuel = 0 (timeout — vacuous)
      intro cont b σT σ' hnt hcode hag hev
      simp [evalS] at hev
  | case10 fuel c bd σ bv heq hz =>   -- while, cond = 0 (exit)
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      simp only [evalS, heq, hz] at hev
      injection hev with hev; subst hev
      simp only [layS] at hcode ⊢
      rw [List.append_assoc] at hcode
      have hcodeC : CodeAt P b (layC c (b + szC c) b).2.1 := hcode.append_left
      obtain ⟨σTc, hsC, hxc, hagc, _⟩ := layC_correct c hntc hcodeC hag heq
      have hBC := hcode.append_right (l₁ := (layC c (b + szC c) b).2.1)
      rw [layC_len] at hBC
      have hifz : P.fetch (b + szC c) = some (.ifz (layC c (b + szC c) b).1 cont
          (layS bd (layC c (b + szC c) b).2.2 (b + szC c + 1)).2) := hBC.head
      have hcz : σTc (layC c (b + szC c) b).1 = 0 := by rw [hxc]; exact eq_of_beq hz
      exact ⟨σTc, Steps.trans hsC (Steps.singleton (Step.ifzT hifz hcz)), hagc⟩
  | case11 fuel c bd σ bv heq hnz σmid hbody ihb ihw =>   -- while, cond ≠ 0 (iterate)
      intro cont b σT σ' hnt hcode hag hev
      obtain ⟨hntc, hntb⟩ := hnt
      rw [Bool.not_eq_true] at hnz
      have hcode0 := hcode
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
      -- run body to the loop head, then loop via the fuel-IH
      obtain ⟨σ1, hsB, hag1⟩ := ihb hntb hcodeB hagc hbody
      obtain ⟨σ2, hsW, hag2⟩ := ihw ⟨hntc, hntb⟩ hcode0 hag1 hev
      refine ⟨σ2, ?_, hag2⟩
      exact Steps.trans hsC (Steps.trans (Steps.singleton (Step.ifzF hifz hcne))
        (Steps.trans hsB hsW))
  | case12 fuel c bd σ bv heq hnz hfail ihb =>   -- while, body not ok (vacuous)
      intro cont b σT σ' hnt hcode hag hev
      rw [Bool.not_eq_true] at hnz
      simp only [evalS, heq, hnz] at hev
      cases hm : evalS fuel bd σ with
      | ok σmid => exact (hfail σmid hm).elim
      | fault => rw [hm] at hev; simp at hev
      | timeout => rw [hm] at hev; simp at hev
  | case13 fuel c bd σ heq =>   -- while (fuel+1), cond faults (vacuous)
      intro cont b σT σ' hnt hcode hag hev
      simp [evalS, heq] at hev

/-! ## E. Compose — `lower_correct` and the end-to-end `ast_to_asm`. -/

/-- **Frontend correctness (`lower_correct`).** If the reference interpreter runs the surface
    statement `s` from the initial store to `σ'`, then `lower s` steps from its entry to a `halt`
    configuration whose store agrees with `σ'` on the source (`.orig`) variables. (Requires the surface
    well-formedness `s.noTmp`: surface programs use only source vars, never the `.tmp` namespace lowering
    reserves for scratch.) -/
theorem lower_correct (s : Stmt) (fuel : Nat) (σ' : Store)
    (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ cf, Semantics.Steps (lower s) ⟨(lower s).entry, Store.init⟩ cf
        ∧ Semantics.Final (lower s) cf
        ∧ ∀ x, (∃ t, x = Var.orig t) → cf.store x = σ' x := by
  obtain ⟨σT', hsteps, hag'⟩ :=
    layS_correct fuel s Store.init (cont := 0) (b := 1) (σT := Store.init)
      hnt (lower_codeAt s) (fun _ => rfl) h
  refine ⟨⟨0, σT'⟩, ?_, lower_fetch_zero s, ?_⟩
  · show Semantics.Steps (lower s) ⟨(lower s).entry, Store.init⟩ ⟨0, σT'⟩
    have he : (lower s).entry = (layS s 0 1).2 := rfl
    rw [he]; exact hsteps
  · intro x hx; obtain ⟨t, rfl⟩ := hx; exact hag' t

/-- **End-to-end AST→ASM forward simulation.** If the reference interpreter runs `s` to `σ'`, then the
    ARM64 program `codegen (lower s)` (backend ∘ frontend) runs from its initial state to a `halted`
    machine state whose frame holds `σ'`'s values for every source (`.orig`) variable under `encode`.
    Composes `lower_correct` (frontend) with `TacToAsm.codegen_simulates` (backend). -/
theorem ast_to_asm (s : Stmt) (fuel : Nat) (σ' : Store)
    (hnt : Stmt.noTmp s)
    (h : Ast.evalS fuel s Store.init = .ok σ') :
    ∃ f sf, Asm.run (TacToAsm.codegen (lower s)) f (TacToAsm.initState (lower s) Store.init)
              = .halted sf
          ∧ ∀ x t, x = Var.orig t →
              sf.mem (TacToAsm.slot (TacToAsm.collectVars (lower s)) x) = TacToAsm.encode (σ' x) := by
  obtain ⟨cf, hsteps, hfin, hframe⟩ := lower_correct s fuel σ' hnt h
  obtain ⟨f, sf, hrun, hmem⟩ := TacToAsm.codegen_simulates hsteps hfin
  refine ⟨f, sf, hrun, ?_⟩
  intro x t hx
  rw [hmem x, hframe x ⟨t, hx⟩]

end AstToTac

end BaseLanguage
