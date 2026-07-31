-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Normalize.Constraints

/-!
# `Normalize.SelfRead` — the self-read-elimination pre-pass

Rewrites each self-reading numbered compute `x := e[x] → next` into a two-node chain
`fresh := e[x] → c ; c: x := fresh → next` (with `c` an appended copy node), so the result satisfies
`NoSelfRead`. This is the one pre-pass whose successor *sets* genuinely change, so reachability
preservation is by induction on the source derivation (routing the self-reading step through the
inserted copy node) rather than a successor-set congruence. Structural facts only; dataflow-free.
-/

namespace BaseLanguage
namespace Normalize
open Tac Semantics

/-- A **self-reading numbered** assignment: numbered RHS that mentions its own def var. -/
def isSelfRead : Cmd → Bool
  | .assign x e _ => isNumbered e && exprReadsVar e x
  | _             => false

/-- The self-reading numbered nodes of `P`, in node order. -/
def selfNodes (P : Program) : List Node :=
  (List.range P.size).filter (fun nd => (P.fetch nd).elim false isSelfRead)

/-- The appended copy half for a self-reading node `nd : x := e[x] → next`: `x := t → next`
    (`t := fresh nd`). -/
def normCopy (P : Program) (fresh : Node → Var) (nd : Node) : Cmd :=
  match P.fetch nd with
  | some (.assign x _ next) => .assign x (.atom (.var (fresh nd))) next
  | _                       => .halt

/-- The appended copy label of self-reading node `nd` (its index in `selfNodes`, offset by size). -/
def normLabel (P : Program) (nd : Node) : Node :=
  if (P.fetch nd).elim false isSelfRead
  then P.size + (selfNodes P).idxOf nd
  else P.entry

/-- The in-place rewrite of a `[0, size)` node: a self-reading `x := e[x] → next` becomes
    `t := e[x] → (copy label)`; everything else verbatim. -/
def normInplace (P : Program) (fresh : Node → Var) (nd : Node) : Cmd → Cmd
  | .assign x e next =>
      if isNumbered e && exprReadsVar e x
      then .assign (fresh nd) e (normLabel P nd)
      else .assign x e next
  | other => other

/-- **The self-reading normalization pass.** -/
def normalizeSelfRead (P : Program) (fresh : Node → Var) : Program where
  entry := P.entry
  code  := (Array.ofFn (n := P.size) (fun i => normInplace P fresh i.val (P.code[i.val]'i.isLt)))
            ++ ((selfNodes P).map (normCopy P fresh)).toArray
  obs   := P.obs

/-! ## Size / fetch lemmas -/

@[simp] theorem normalize_size (P : Program) (fresh : Node → Var) :
    (normalizeSelfRead P fresh).size = P.size + (selfNodes P).length := by
  show ((Array.ofFn (n := P.size) _) ++ _).size = _
  rw [Array.size_append, Array.size_ofFn]; simp

theorem normalize_fetch_kept (P : Program) (fresh : Node → Var) {nd : Node} (h : nd < P.size) :
    (normalizeSelfRead P fresh).fetch nd = some (normInplace P fresh nd (P.code[nd]'h)) := by
  have hk : nd < (Array.ofFn (n := P.size)
      (fun i => normInplace P fresh i.val (P.code[i.val]'i.isLt))).size := by
    rw [Array.size_ofFn]; exact h
  show ((Array.ofFn _) ++ _)[nd]? = _
  rw [Array.getElem?_append_left hk, Array.getElem?_eq_getElem hk, Array.getElem_ofFn]

theorem normalize_fetch_appended (P : Program) (fresh : Node → Var) {nd : Node} (h : P.size ≤ nd) :
    (normalizeSelfRead P fresh).fetch nd
      = ((selfNodes P).map (normCopy P fresh)).toArray[nd - P.size]? := by
  have hk : (Array.ofFn (n := P.size)
      (fun i => normInplace P fresh i.val (P.code[i.val]'i.isLt))).size ≤ nd := by
    rw [Array.size_ofFn]; exact h
  show ((Array.ofFn _) ++ _)[nd]? = _
  rw [Array.getElem?_append_right hk]; congr 1; rw [Array.size_ofFn]

/-! ## `selfNodes` membership characterisation -/

/-- Membership in `selfNodes` exposes: in range, and a self-reading numbered assign. -/
theorem mem_selfNodes (P : Program) {nd : Node} (h : nd ∈ selfNodes P) :
    nd < P.size ∧ ∃ x e next, P.fetch nd = some (.assign x e next) ∧
      isNumbered e = true ∧ exprReadsVar e x = true := by
  unfold selfNodes at h
  rw [List.mem_filter, List.mem_range] at h
  obtain ⟨hlt, hsr⟩ := h
  refine ⟨hlt, ?_⟩
  cases hf : P.fetch nd with
  | none => rw [hf] at hsr; simp at hsr
  | some instr =>
      cases instr with
      | assign x e next =>
          rw [hf] at hsr
          simp only [Option.elim, isSelfRead, Bool.and_eq_true] at hsr
          exact ⟨x, e, next, rfl, hsr.1, hsr.2⟩
      | ifz x1 z1 nz1 => rw [hf] at hsr; simp [isSelfRead] at hsr
      | noop n1 => rw [hf] at hsr; simp [isSelfRead] at hsr
      | halt => rw [hf] at hsr; simp [isSelfRead] at hsr

/-- A self-reading in-range node is a member of `selfNodes` (converse). -/
theorem mem_selfNodes_of (P : Program) {nd : Node} {x e next} (hk : nd < P.size)
    (hf : P.fetch nd = some (.assign x e next)) (hnum : isNumbered e = true)
    (hrd : exprReadsVar e x = true) : nd ∈ selfNodes P := by
  unfold selfNodes
  rw [List.mem_filter, List.mem_range]
  refine ⟨hk, ?_⟩
  rw [hf]; simp only [Option.elim, isSelfRead, Bool.and_eq_true]; exact ⟨hnum, hrd⟩

/-- With no self-reading numbered compute, the self-node list is empty. -/
theorem selfNodes_nil (P : Program) (h : NoSelfRead P) : selfNodes P = [] := by
  unfold selfNodes
  rw [List.filter_eq_nil_iff]
  intro nd hmem
  rw [List.mem_range] at hmem
  cases hf : P.fetch nd with
  | none => simp
  | some instr =>
      cases instr with
      | assign x e next =>
          simp only [Option.elim, isSelfRead, Bool.not_eq_true, Bool.and_eq_false_iff]
          by_cases hn : isNumbered e = true
          · exact Or.inr (h hf hn)
          · exact Or.inl (Bool.not_eq_true _ ▸ hn)
      | ifz x z nz => simp [isSelfRead]
      | noop nx => simp [isSelfRead]
      | halt => simp [isSelfRead]

/-! ## The output is self-reading-free -/

/-- Every appended instruction is a copy whose RHS is an atom, hence not numbered. -/
theorem appended_not_numbered (P : Program) (fresh : Node → Var) {j : Nat} {instr : Cmd}
    (hf : ((selfNodes P).map (normCopy P fresh)).toArray[j]? = some instr)
    {x e next} (he : instr = .assign x e next) : isNumbered e = false := by
  have hmem : instr ∈ (selfNodes P).map (normCopy P fresh) := by
    have := Array.mem_of_getElem? hf; simpa using this
  rw [List.mem_map] at hmem
  obtain ⟨m, _, hcopy⟩ := hmem
  rw [← hcopy] at he
  unfold normCopy at he
  cases hfm : P.fetch m with
  | none => rw [hfm] at he; simp at he
  | some im =>
      cases im with
      | assign x0 e0 next0 => rw [hfm] at he; injection he with _ he _; rw [← he]; rfl
      | ifz x1 z1 nz1 => rw [hfm] at he; simp at he
      | noop n1 => rw [hfm] at he; simp at he
      | halt => rw [hfm] at he; simp at he

/-- **The output is self-reading-free**, given the fresh supply avoids each node's RHS operands. -/
theorem normalize_noSelfRead (P : Program) (fresh : Node → Var)
    (hfresh : ∀ {nd x e next}, P.fetch nd = some (.assign x e next) →
      exprReadsVar e (fresh nd) = false) :
    NoSelfRead (normalizeSelfRead P fresh) := by
  intro nd x e next hf hn
  by_cases hk : nd < P.size
  · rw [normalize_fetch_kept P fresh hk] at hf
    have hcfetch : P.fetch nd = some (P.code[nd]'hk) := fetch_eq_getElem hk
    cases hc : (P.code[nd]'hk) with
    | assign x0 e0 next0 =>
        simp only [hc, normInplace] at hf
        by_cases hsr : (isNumbered e0 && exprReadsVar e0 x0) = true
        · rw [if_pos hsr] at hf
          injection hf with hassign; injection hassign with hx he _
          subst hx; subst he
          exact hfresh (by rw [hcfetch, hc])
        · rw [if_neg hsr] at hf
          injection hf with hassign; injection hassign with hx he _
          subst hx; subst he
          rw [Bool.and_eq_true, not_and] at hsr
          exact Bool.not_eq_true _ ▸ hsr hn
    | ifz x1 z1 nz1 => rw [hc] at hf; simp [normInplace] at hf
    | noop n1 => rw [hc] at hf; simp [normInplace] at hf
    | halt => rw [hc] at hf; simp [normInplace] at hf
  · rw [normalize_fetch_appended P fresh (Nat.le_of_not_lt hk)] at hf
    rw [appended_not_numbered P fresh hf rfl] at hn
    exact absurd hn (by simp)

/-! ## Well-formedness preservation -/

theorem normalize_wellFormed (P : Program) (fresh : Node → Var) (hwf : WellFormed P) :
    WellFormed (normalizeSelfRead P fresh) where
  entry_lt := by
    rw [normalize_size]; exact Nat.lt_of_lt_of_le hwf.entry_lt (Nat.le_add_right _ _)
  succ_lt := by
    intro nd instr s hf hs
    rw [normalize_size]
    by_cases hk : nd < P.size
    · rw [normalize_fetch_kept P fresh hk] at hf
      injection hf with hinstr; subst hinstr
      have hsfetch : P.fetch nd = some (P.code[nd]'hk) := fetch_eq_getElem hk
      cases hc : (P.code[nd]'hk) with
      | assign x0 e0 next0 =>
          rw [hc] at hs; simp only [normInplace] at hs
          by_cases hsr : (isNumbered e0 && exprReadsVar e0 x0) = true
          · rw [if_pos hsr] at hs
            simp only [Cmd.succs, List.mem_singleton] at hs; subst hs
            rw [Bool.and_eq_true] at hsr
            have hmem := mem_selfNodes_of P hk (by rw [hsfetch, hc]) hsr.1 hsr.2
            have hcond : (P.fetch nd).elim false isSelfRead = true := by
              rw [hsfetch, hc]; simp only [Option.elim, isSelfRead, Bool.and_eq_true]; exact hsr
            rw [normLabel, if_pos hcond]
            exact Nat.add_lt_add_left (List.idxOf_lt_length_of_mem hmem) P.size
          · rw [if_neg hsr] at hs
            simp only [Cmd.succs, List.mem_singleton] at hs; subst hs
            exact Nat.lt_of_lt_of_le (hwf.succ_lt (by rw [hsfetch, hc]) (by simp [Cmd.succs]))
              (Nat.le_add_right _ _)
      | ifz x1 z1 nz1 =>
          rw [hc] at hs; simp only [normInplace] at hs
          exact Nat.lt_of_lt_of_le (hwf.succ_lt (by rw [hsfetch, hc]) hs) (Nat.le_add_right _ _)
      | noop n1 =>
          rw [hc] at hs; simp only [normInplace] at hs
          exact Nat.lt_of_lt_of_le (hwf.succ_lt (by rw [hsfetch, hc]) hs) (Nat.le_add_right _ _)
      | halt => rw [hc] at hs; simp [normInplace, Cmd.succs] at hs
    · rw [normalize_fetch_appended P fresh (Nat.le_of_not_lt hk)] at hf
      have hmem : instr ∈ (selfNodes P).map (normCopy P fresh) := by
        have h0 := Array.mem_of_getElem? hf; simpa using h0
      rw [List.mem_map] at hmem
      obtain ⟨m, hmem_m, hcopy⟩ := hmem
      obtain ⟨hmlt, x0, e0, next0, hfm, _, _⟩ := mem_selfNodes P hmem_m
      have hcopyeq : normCopy P fresh m = .assign x0 (.atom (.var (fresh m))) next0 := by
        unfold normCopy; rw [hfm]
      rw [hcopyeq] at hcopy; subst hcopy
      simp only [Cmd.succs, List.mem_singleton] at hs; subst hs
      exact Nat.lt_of_lt_of_le (hwf.succ_lt hfm (by simp [Cmd.succs])) (Nat.le_add_right _ _)

/-! ## Successor structure of the normalized program -/

theorem succList_norm_self (P : Program) (fresh : Node → Var) {p : Node} (hp : p ∈ selfNodes P) :
    succList (normalizeSelfRead P fresh) p = [normLabel P p] := by
  obtain ⟨hlt, x, e, next, hf, hnum, hrd⟩ := mem_selfNodes P hp
  have hcode : P.code[p]'hlt = .assign x e next :=
    Option.some.inj ((fetch_eq_getElem hlt).symm.trans hf)
  have hcond : (isNumbered e && exprReadsVar e x) = true := by simp [hnum, hrd]
  have hfetch : (normalizeSelfRead P fresh).fetch p = some (.assign (fresh p) e (normLabel P p)) := by
    rw [normalize_fetch_kept P fresh hlt, hcode]
    simp only [normInplace, if_pos hcond]
  simp only [succList_eq hfetch, Cmd.succs]

/-- On a duplicate-free list of `Nat`s, `l[l.idxOf a] = a`. -/
theorem getElem_idxOf {l : List Node} {a : Node} (h : a ∈ l) :
    l[l.idxOf a]'(List.idxOf_lt_length_of_mem h) = a := by
  have hlt : l.findIdx (· == a) < l.length := List.idxOf_lt_length_of_mem h
  have := List.findIdx_getElem (xs := l) (p := (· == a)) (w := hlt)
  simpa [List.idxOf] using this

/-- A self-reading node's appended copy label fetches its copy instruction. -/
theorem fetch_normLabel (P : Program) (fresh : Node → Var) {nd : Node} (h : nd ∈ selfNodes P) :
    (normalizeSelfRead P fresh).fetch (normLabel P nd) = some (normCopy P fresh nd) := by
  obtain ⟨hlt, x, e, next, hf, hnum, hrd⟩ := mem_selfNodes P h
  have hcond : (P.fetch nd).elim false isSelfRead = true := by
    rw [hf]; simp [isSelfRead, hnum, hrd]
  have hlabel : normLabel P nd = P.size + (selfNodes P).idxOf nd := by
    unfold normLabel; rw [if_pos hcond]
  rw [hlabel, normalize_fetch_appended P fresh (Nat.le_add_right _ _),
    show P.size + (selfNodes P).idxOf nd - P.size = (selfNodes P).idxOf nd from by omega]
  have hidx : (selfNodes P).idxOf nd < (selfNodes P).length := List.idxOf_lt_length_of_mem h
  rw [List.getElem?_toArray, List.getElem?_eq_getElem (by simpa using hidx), List.getElem_map,
    getElem_idxOf h]

theorem succList_norm_copy (P : Program) (fresh : Node → Var) {p : Node} {x : Var} {e : Expr}
    {next : Node} (hp : p ∈ selfNodes P) (hf : P.fetch p = some (.assign x e next)) :
    succList (normalizeSelfRead P fresh) (normLabel P p) = [next] := by
  have hfetch : (normalizeSelfRead P fresh).fetch (normLabel P p)
      = some (.assign x (.atom (.var (fresh p))) next) := by
    rw [fetch_normLabel P fresh hp]; unfold normCopy; rw [hf]
  simp only [succList_eq hfetch, Cmd.succs]

theorem succList_norm_nonself (P : Program) (fresh : Node → Var) {p : Node} (hlt : p < P.size)
    (hns : p ∉ selfNodes P) : succList (normalizeSelfRead P fresh) p = succList P p := by
  have hsuccs : (normInplace P fresh p (P.code[p]'hlt)).succs = (P.code[p]'hlt).succs := by
    cases hc : P.code[p]'hlt with
    | assign x e next =>
        simp only [normInplace]
        by_cases hcond : (isNumbered e && exprReadsVar e x) = true
        · exfalso
          rw [Bool.and_eq_true] at hcond
          exact hns (mem_selfNodes_of P hlt (by rw [fetch_eq_getElem hlt, hc]) hcond.1 hcond.2)
        · rw [if_neg hcond]
    | ifz x z nz => rfl
    | noop n => rfl
    | halt => rfl
  unfold succList
  rw [normalize_fetch_kept P fresh hlt, fetch_eq_getElem hlt]
  simp only [Option.elim]; exact hsuccs

/-! ## `FReach` / `AllReachable` preservation -/

theorem normalize_freach (P : Program) (fresh : Node → Var) (hwf : WellFormed P) {nd : Node}
    (hr : FReach P nd) : FReach (normalizeSelfRead P fresh) nd := by
  induction hr with
  | entry =>
      have he : (normalizeSelfRead P fresh).entry = P.entry := rfl
      rw [← he]; exact FReach.entry
  | @step p nd hp hs ih =>
      have hplt : p < P.size := FReach_lt hwf hp
      by_cases hself : p ∈ selfNodes P
      · obtain ⟨_, x, e, next, hf, _, _⟩ := mem_selfNodes P hself
        have hsucceq : succList P p = [next] := by simp only [succList_eq hf, Cmd.succs]
        rw [hsucceq, List.mem_singleton] at hs
        subst nd
        have h1 : normLabel P p ∈ succList (normalizeSelfRead P fresh) p := by
          rw [succList_norm_self P fresh hself]; exact List.mem_singleton.mpr rfl
        have h2 : next ∈ succList (normalizeSelfRead P fresh) (normLabel P p) := by
          rw [succList_norm_copy P fresh hself hf]; exact List.mem_singleton.mpr rfl
        exact FReach.step (FReach.step ih h1) h2
      · have hmem : nd ∈ succList (normalizeSelfRead P fresh) p := by
          rw [succList_norm_nonself P fresh hplt hself]; exact hs
        exact FReach.step ih hmem

theorem selfNodes_nodup (P : Program) : (selfNodes P).Nodup :=
  List.Nodup.sublist (List.filter_sublist) List.nodup_range

theorem idxOf_getElem_nodup {l : List Node} (hnd : l.Nodup) {j : Nat} (hj : j < l.length) :
    l.idxOf (l[j]'hj) = j := by
  have hmem : l[j]'hj ∈ l := List.getElem_mem hj
  have h1 : l[l.idxOf (l[j]'hj)]'(List.idxOf_lt_length_of_mem hmem) = l[j]'hj := getElem_idxOf hmem
  exact (List.getElem_inj hnd).mp h1

theorem normLabel_selfNodes_getElem (P : Program) {j : Nat} (hj : j < (selfNodes P).length) :
    normLabel P ((selfNodes P)[j]'hj) = P.size + j := by
  obtain ⟨hlt, x, e, next, hf, hnum, hrd⟩ := mem_selfNodes P (List.getElem_mem hj)
  have hcond : (P.fetch ((selfNodes P)[j]'hj)).elim false isSelfRead = true := by
    rw [hf]; simp [isSelfRead, hnum, hrd]
  unfold normLabel
  rw [if_pos hcond, idxOf_getElem_nodup (selfNodes_nodup P) hj]

/-- **`normalizeSelfRead` preserves `AllReachable`.** -/
theorem normalize_allReach (P : Program) (fresh : Node → Var) (hwf : WellFormed P)
    (har : AllReachable P) : AllReachable (normalizeSelfRead P fresh) := by
  intro nd hnd
  rw [normalize_size] at hnd
  by_cases hk : nd < P.size
  · exact normalize_freach P fresh hwf (har nd hk)
  · have hge : P.size ≤ nd := Nat.le_of_not_lt hk
    obtain ⟨j, rfl⟩ : ∃ j, nd = P.size + j := ⟨nd - P.size, (Nat.add_sub_cancel' hge).symm⟩
    have hjlt : j < (selfNodes P).length := by omega
    have hmem : (selfNodes P)[j]'hjlt ∈ selfNodes P := List.getElem_mem hjlt
    obtain ⟨hmlt, x, e, next, hf, _, _⟩ := mem_selfNodes P hmem
    have hreach_m : FReach (normalizeSelfRead P fresh) ((selfNodes P)[j]'hjlt) :=
      normalize_freach P fresh hwf (har _ hmlt)
    have hsucc : normLabel P ((selfNodes P)[j]'hjlt)
        ∈ succList (normalizeSelfRead P fresh) ((selfNodes P)[j]'hjlt) := by
      rw [succList_norm_self P fresh hmem]; exact List.mem_singleton.mpr rfl
    rw [← normLabel_selfNodes_getElem P hjlt]
    exact FReach.step hreach_m hsucc

end Normalize
end BaseLanguage
