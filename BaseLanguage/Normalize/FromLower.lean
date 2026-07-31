-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.AstToTac
import BaseLanguage.Normalize.Normalize

/-!
# `Normalize.FromLower` — the `AstToTac.lower` output satisfies the normal-form preconditions

The frontend's structural reachability proofs, reformulated against our `Normalize`
predicates: `lower s` is forward-reachable from its entry
(`lower_allReachable`). Combined with `lower_wellFormed`, this discharges both preconditions of
`normalize_wellNormalized`, giving the zero-hypothesis pipeline pass `normalize_lower_wellNormalized`.

Everything here is structural: `Agrees P code b` ("`P` fetches `code` at `[b, b+len)`") is pure index
bookkeeping; the `lay*` inductions reuse the `AstToTac` size lemmas. No analysis, no dataflow.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics Ast AstToTac

/-! ## Agreement: `P` fetches `code` at `[b, b+code.length)`. -/

/-- `P` lays `code` starting at node `b`. -/
def Agrees (P : Program) (code : List Cmd) (b : Node) : Prop :=
  ∀ j, j < code.length → P.fetch (b + j) = code[j]?

theorem Agrees_append_left {P : Program} {c1 c2 : List Cmd} {b : Node}
    (h : Agrees P (c1 ++ c2) b) : Agrees P c1 b := by
  intro j hj
  have hjt : j < (c1 ++ c2).length := by rw [List.length_append]; omega
  rw [h j hjt, List.getElem?_append_left hj]

theorem Agrees_append_right {P : Program} {c1 c2 : List Cmd} {b : Node}
    (h : Agrees P (c1 ++ c2) b) : Agrees P c2 (b + c1.length) := by
  intro j hj
  have hjt : c1.length + j < (c1 ++ c2).length := by rw [List.length_append]; omega
  have hf := h (c1.length + j) hjt
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hf
  rwa [← Nat.add_assoc] at hf

theorem Agrees_single {P : Program} {instr : Cmd} {b : Node}
    (h : Agrees P [instr] b) : P.fetch b = some instr := by
  have := h 0 (by simp); simpa using this

/-! ## Forward reachability across the layout -/

theorem freach_append {P : Program} {c1 c2 : List Cmd} {b : Node}
    (h1 : ∀ j, j < c1.length → FReach P (b + j))
    (h2 : ∀ j, j < c2.length → FReach P (b + c1.length + j)) :
    ∀ j, j < (c1 ++ c2).length → FReach P (b + j) := by
  intro j hj
  rw [List.length_append] at hj
  rcases Nat.lt_or_ge j c1.length with hlt | hge
  · exact h1 j hlt
  · have hj2 : j - c1.length < c2.length := by omega
    have := h2 (j - c1.length) hj2
    rwa [show b + c1.length + (j - c1.length) = b + j from by
      rw [Nat.add_assoc]; congr 1; omega] at this

theorem freach_step_single {P : Program} {b m : Node} {instr : Cmd}
    (hf : P.fetch b = some instr) (hm : m ∈ instr.succs) (h : FReach P b) : FReach P m :=
  FReach.step h (by rw [succList_eq hf]; exact hm)

theorem freach_layE (e : Ast.Expr) (cont b : Node) (P : Program)
    (hag : Agrees P (layE e cont b).1 b) (hentry : FReach P (layE e cont b).2.2) :
    FReach P cont ∧ ∀ j, j < (layE e cont b).1.length → FReach P (b + j) := by
  induction e generalizing cont b with
  | atom a => exact ⟨hentry, by intro j hj; simp [layE] at hj⟩
  | una op e ih =>
      simp only [layE] at hag
      have hlen : (layE e (b + szE e) b).1.length = szE e := layE_len ..
      have hagE := Agrees_append_left hag
      have hagA := Agrees_append_right hag
      rw [hlen] at hagA
      have hassign := Agrees_single hagA
      have ihE := ih (b + szE e) b hagE hentry
      have hopReach : FReach P (b + szE e) := ihE.1
      refine ⟨freach_step_single hassign (by simp [Cmd.succs]) hopReach, ?_⟩
      refine freach_append ihE.2 ?_
      intro j hj
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hlen]; simpa using hopReach
  | bin op e₁ e₂ ih₁ ih₂ =>
      simp only [layE] at hag
      have hlen1 : (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1.length = szE e₁ :=
        layE_len ..
      have hlen2 : (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1.length = szE e₂ := layE_len ..
      have hag12 := Agrees_append_left hag
      have hagA := Agrees_append_right hag
      have hag1 := Agrees_append_left hag12
      have hag2 := Agrees_append_right hag12
      rw [hlen1] at hag2
      rw [show ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length
          = szE e₁ + szE e₂ from by rw [List.length_append, hlen1, hlen2],
        ← Nat.add_assoc] at hagA
      have hassign := Agrees_single hagA
      have ihE1 := ih₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b hag1 hentry
      have ihE2 := ih₂ (b + szE e₁ + szE e₂) (b + szE e₁) hag2 ihE1.1
      have hopReach : FReach P (b + szE e₁ + szE e₂) := ihE2.1
      refine ⟨freach_step_single hassign (by simp [Cmd.succs]) hopReach, ?_⟩
      have hnodes12 : ∀ j, j < ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length → FReach P (b + j) := by
        refine freach_append ihE1.2 ?_
        intro j hj; rw [hlen1]; exact ihE2.2 j hj
      refine freach_append hnodes12 ?_
      intro j hj
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [show ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length
          = szE e₁ + szE e₂ from by rw [List.length_append, hlen1, hlen2]]
      rw [← Nat.add_assoc, Nat.add_zero]; exact hopReach

theorem freach_layI (x : Var) (e : Ast.Expr) (cont b : Node) (P : Program)
    (hag : Agrees P (layI x e cont b).1 b) (hentry : FReach P (layI x e cont b).2) :
    FReach P cont ∧ ∀ j, j < (layI x e cont b).1.length → FReach P (b + j) := by
  cases e with
  | atom a =>
      have hf : P.fetch b = some (.assign x (.atom a) cont) := Agrees_single (by
        have : Agrees P (layI x (.atom a) cont b).1 b := hag
        simpa only [layI] using this)
      refine ⟨freach_step_single hf (by simp [Cmd.succs]) hentry, ?_⟩
      intro j hj
      have hj0 : j = 0 := by simp only [layI, List.length_singleton] at hj; omega
      subst hj0
      rw [Nat.add_zero]; exact hentry
  | una op e =>
      simp only [layI] at hag
      have hlen : (layE e (b + szE e) b).1.length = szE e := layE_len ..
      have hagE := Agrees_append_left hag
      have hagA := Agrees_append_right hag
      rw [hlen] at hagA
      have hassign := Agrees_single hagA
      have ihE := freach_layE e (b + szE e) b P hagE hentry
      have hopReach : FReach P (b + szE e) := ihE.1
      refine ⟨freach_step_single hassign (by simp [Cmd.succs]) hopReach, ?_⟩
      refine freach_append ihE.2 ?_
      intro j hj
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [hlen]; simpa using hopReach
  | bin op e₁ e₂ =>
      simp only [layI] at hag
      have hlen1 : (layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1.length = szE e₁ :=
        layE_len ..
      have hlen2 : (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1.length = szE e₂ := layE_len ..
      have hag12 := Agrees_append_left hag
      have hagA := Agrees_append_right hag
      have hag1 := Agrees_append_left hag12
      have hag2 := Agrees_append_right hag12
      rw [hlen1] at hag2
      rw [show ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length
          = szE e₁ + szE e₂ from by rw [List.length_append, hlen1, hlen2],
        ← Nat.add_assoc] at hagA
      have hassign := Agrees_single hagA
      have ihE1 := freach_layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b P hag1 hentry
      have ihE2 := freach_layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁) P hag2 ihE1.1
      have hopReach : FReach P (b + szE e₁ + szE e₂) := ihE2.1
      refine ⟨freach_step_single hassign (by simp [Cmd.succs]) hopReach, ?_⟩
      have hnodes12 : ∀ j, j < ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length → FReach P (b + j) := by
        refine freach_append ihE1.2 ?_
        intro j hj; rw [hlen1]; exact ihE2.2 j hj
      refine freach_append hnodes12 ?_
      intro j hj
      simp only [List.length_singleton] at hj
      have hj0 : j = 0 := by omega
      subst hj0
      rw [show ((layE e₁ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).2.2 b).1
            ++ (layE e₂ (b + szE e₁ + szE e₂) (b + szE e₁)).1).length
          = szE e₁ + szE e₂ from by rw [List.length_append, hlen1, hlen2]]
      rw [← Nat.add_assoc, Nat.add_zero]; exact hopReach

theorem freach_layC (c : Ast.Expr) (cont b : Node) (P : Program)
    (hag : Agrees P (layC c cont b).2.1 b) (hentry : FReach P (layC c cont b).2.2) :
    FReach P cont ∧ ∀ j, j < (layC c cont b).2.1.length → FReach P (b + j) := by
  cases c with
  | atom a =>
      cases a with
      | var x => exact ⟨hentry, by intro j hj; simp [layC] at hj⟩
      | imm n =>
          have hf : P.fetch b = some (.assign (.tmp b) (.atom (.imm n)) cont) := Agrees_single (by
            have : Agrees P (layC (.atom (.imm n)) cont b).2.1 b := hag
            simpa only [layC] using this)
          refine ⟨freach_step_single hf (by simp [Cmd.succs]) hentry, ?_⟩
          intro j hj
          have hj0 : j = 0 := by simp only [layC, List.length_singleton] at hj; omega
          subst hj0
          rw [Nat.add_zero]; exact hentry
  | una op e =>
      exact freach_layI (.tmp b) (.una op e) cont b P (by
        have : Agrees P (layC (.una op e) cont b).2.1 b := hag
        simpa only [layC] using this) hentry
  | bin op e₁ e₂ =>
      exact freach_layI (.tmp b) (.bin op e₁ e₂) cont b P (by
        have : Agrees P (layC (.bin op e₁ e₂) cont b).2.1 b := hag
        simpa only [layC] using this) hentry

theorem freach_layS (s : Stmt) (cont b : Node) (P : Program)
    (hag : Agrees P (layS s cont b).1 b) (hentry : FReach P (layS s cont b).2) :
    FReach P cont ∧ ∀ j, j < (layS s cont b).1.length → FReach P (b + j) := by
  induction s generalizing cont b with
  | skip => exact ⟨hentry, by intro j hj; simp [layS] at hj⟩
  | assign x e =>
      exact freach_layI x e cont b P (by
        have : Agrees P (layS (.assign x e) cont b).1 b := hag
        simpa only [layS] using this) hentry
  | seq s₁ s₂ ih₁ ih₂ =>
      simp only [layS] at hag
      have hlen1 : (layS s₁ (layS s₂ cont (b + szS s₁)).2 b).1.length = szS s₁ := layS_len ..
      have hag1 := Agrees_append_left hag
      have hag2 := Agrees_append_right hag
      rw [hlen1] at hag2
      have ihS1 := ih₁ (layS s₂ cont (b + szS s₁)).2 b hag1 hentry
      have ihS2 := ih₂ cont (b + szS s₁) hag2 ihS1.1
      refine ⟨ihS2.1, ?_⟩
      refine freach_append ihS1.2 ?_
      intro j hj; rw [hlen1]; exact ihS2.2 j hj
  | ite c t e ihT ihE =>
      simp only [layS] at hag
      have hlenC : (layC c (b + szC c) b).2.1.length = szC c := layC_len ..
      have hlenT : (layS t cont (b + szC c + 1)).1.length = szS t := layS_len ..
      have hagE := Agrees_append_right hag
      have hag3 := Agrees_append_left hag
      have hagT := Agrees_append_right hag3
      have hag2 := Agrees_append_left hag3
      have hagIfz := Agrees_append_right hag2
      have hagC := Agrees_append_left hag2
      rw [List.length_append, List.length_singleton, hlenC] at hagT
      rw [List.length_append, List.length_append, hlenC, List.length_singleton, hlenT,
        ← Nat.add_assoc, ← Nat.add_assoc] at hagE
      rw [hlenC] at hagIfz
      have hifz := Agrees_single hagIfz
      have ihCb := freach_layC c (b + szC c) b P hagC hentry
      have hifNode : FReach P (b + szC c) := ihCb.1
      have htE : FReach P (layS t cont (b + szC c + 1)).2 :=
        freach_step_single hifz (by simp [Cmd.succs]) hifNode
      have heE : FReach P (layS e cont (b + szC c + 1 + szS t)).2 :=
        freach_step_single hifz (by simp [Cmd.succs]) hifNode
      have ihTb := ihT cont (b + szC c + 1) hagT htE
      have ihEb := ihE cont (b + szC c + 1 + szS t) hagE heE
      refine ⟨ihTb.1, ?_⟩
      have hCifz : ∀ j, j < ((layC c (b + szC c) b).2.1
            ++ [Cmd.ifz (layC c (b + szC c) b).1
                  (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2]).length
          → FReach P (b + j) := by
        refine freach_append ihCb.2 ?_
        intro j hj
        simp only [List.length_singleton] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hlenC, Nat.add_zero]; exact hifNode
      have hCifzT : ∀ j, j < (((layC c (b + szC c) b).2.1
            ++ [Cmd.ifz (layC c (b + szC c) b).1
                  (layS e cont (b + szC c + 1 + szS t)).2 (layS t cont (b + szC c + 1)).2])
            ++ (layS t cont (b + szC c + 1)).1).length → FReach P (b + j) := by
        refine freach_append hCifz ?_
        intro j hj
        have := ihTb.2 j hj
        simp only [List.length_append, List.length_singleton, layC_len,
          Nat.add_assoc] at this ⊢
        exact this
      refine freach_append hCifzT ?_
      intro j hj
      have := ihEb.2 j hj
      simp only [List.length_append, List.length_singleton, layC_len, layS_len,
        Nat.add_assoc] at this ⊢
      exact this
  | «while» c b' ihB =>
      simp only [layS] at hag
      have hlenC : (layC c (b + szC c) b).2.1.length = szC c := layC_len ..
      have hag2 := Agrees_append_left hag
      have hagB := Agrees_append_right hag
      have hagIfz := Agrees_append_right hag2
      have hagC := Agrees_append_left hag2
      rw [hlenC] at hagIfz
      have hifz := Agrees_single hagIfz
      have ihCb := freach_layC c (b + szC c) b P hagC hentry
      have hifNode : FReach P (b + szC c) := ihCb.1
      have hcontReach : FReach P cont :=
        freach_step_single hifz (by simp [Cmd.succs]) hifNode
      have hbE : FReach P (layS b' (layC c (b + szC c) b).2.2 (b + szC c + 1)).2 :=
        freach_step_single hifz (by simp [Cmd.succs]) hifNode
      rw [List.length_append, List.length_singleton, hlenC] at hagB
      have ihBb := ihB (layC c (b + szC c) b).2.2 (b + szC c + 1) hagB hbE
      refine ⟨hcontReach, ?_⟩
      have hCifz : ∀ j, j < ((layC c (b + szC c) b).2.1
            ++ [Cmd.ifz (layC c (b + szC c) b).1 cont
                  (layS b' (layC c (b + szC c) b).2.2 (b + szC c + 1)).2]).length
          → FReach P (b + j) := by
        refine freach_append ihCb.2 ?_
        intro j hj
        simp only [List.length_singleton] at hj
        have hj0 : j = 0 := by omega
        subst hj0
        rw [hlenC, Nat.add_zero]; exact hifNode
      refine freach_append hCifz ?_
      intro j hj
      have := ihBb.2 j hj
      simp only [List.length_append, List.length_singleton, layC_len,
        Nat.add_assoc] at this ⊢
      exact this

/-! ## `lower`'s output satisfies the normal-form preconditions -/

/-- `lower s` lays its body at base `1` (node `0` is `halt`); the laid code agrees with the program. -/
theorem lower_agrees (s : Stmt) : Agrees (lower s) (layS s 0 1).1 1 := by
  intro j hj
  have hfetch : (lower s).fetch (1 + j) = (Cmd.halt :: (layS s 0 1).1).toArray[1 + j]? := rfl
  rw [hfetch, List.getElem?_toArray, show 1 + j = j + 1 from by omega, List.getElem?_cons_succ]

/-- **Every node of `lower s` is forward-reachable from the entry.** -/
theorem lower_allReachable (s : Stmt) : AllReachable (lower s) := by
  have hentry : FReach (lower s) (layS s 0 1).2 := FReach.entry
  have hbody := freach_layS s 0 1 (lower s) (lower_agrees s) hentry
  intro nd hnd
  rw [lower_size] at hnd
  cases nd with
  | zero => exact hbody.1
  | succ k =>
      have hk : k < szS s := Nat.lt_of_succ_lt_succ hnd
      have := hbody.2 k (by rw [layS_len]; exact hk)
      rwa [show (1 : Node) + k = k + 1 from Nat.add_comm 1 k] at this

/-! ## The turnkey pipeline pass -/

/-- **`normalize ∘ lower` produces a `WellNormalized` program — unconditionally**, for any surface
    statement. The two preconditions of `normalize_wellNormalized` are discharged by `lower`'s
    structural guarantees (`lower_wellFormed`, `lower_allReachable`). This is the drop-in pass to run
    right after `AstToTac.lower`. -/
theorem normalize_lower_wellNormalized (s : Stmt) : WellNormalized (normalize (lower s)) :=
  normalize_wellNormalized (lower s) (lower_wellFormed s) (lower_allReachable s)

end Normalize
end BaseLanguage
