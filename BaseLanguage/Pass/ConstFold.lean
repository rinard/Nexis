-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Pass.BranchFold
import BaseLanguage.Peephole.Simplify
/-!
# `Pass.ConstFold` — substitute known constants into RHSs, then fold (the const-prop alternation).

Runs on the same abstract `CPSpec` as `BranchFold`. At each `assign x e`, it replaces every variable in
`e` that the solution knows is constant with that literal, then constant-folds (`peepholeExpr`) — turning
e.g. `x := y + 1` (with `y` known `c`) into `x := imm (c+1)`, a fresh literal copy the *next*
constant-propagation round picks up. Iterating CP ↔ `constFold` ↔ `branchFold` propagates constants through
arithmetic, without the analysis transfer ever having to evaluate expressions.

Verified fault-exactly: under `CPInv` the substitution preserves `eval` on every store (a variable is only
replaced by the value the store already holds), and `peepholeExpr` preserves `eval` unconditionally — so
every source step is the identical step in the folded program (halt/fault/diverge preserved).
-/
namespace BaseLanguage
namespace Pass
namespace ConstFold

open Tac Tac.Locals Semantics Pass Pass.BranchFold Std

variable {P : Program}

/-- The constant the solution records for `y`, if any. -/
def lookupCP (cp : ConstPairs) (y : Var) : Option Val := (cp.toList.find? (fun p => p.1 == y)).map (·.2)

theorem lookupCP_sound {cp : ConstPairs} {y : Var} {c : Val} (h : lookupCP cp y = some c) : (y, c) ∈ cp := by
  unfold lookupCP at h
  cases hf : cp.toList.find? (fun p => p.1 == y) with
  | none => rw [hf] at h; simp at h
  | some p =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      have hy : p.1 = y := by simpa using List.find?_some hf
      rw [show (y, p.2) = p from by rw [← hy]]; exact Std.HashSet.mem_toList.mp (List.mem_of_find?_eq_some hf)

/-- Replace a variable atom by its known constant. -/
def substAtom (cp : ConstPairs) : Atom → Atom
  | .var y => match lookupCP cp y with | some c => .imm c | none => .var y
  | .imm n => .imm n

def substExpr (cp : ConstPairs) : Expr → Expr
  | .atom a     => .atom (substAtom cp a)
  | .una op a   => .una op (substAtom cp a)
  | .bin op a b => .bin op (substAtom cp a) (substAtom cp b)

theorem substAtom_eval {cp : ConstPairs} {σ : Store} {a : Atom}
    (hcp : ∀ y c, (y, c) ∈ cp → σ y = c) : evalAtom σ (substAtom cp a) = evalAtom σ a := by
  cases a with
  | imm n => rfl
  | var y =>
      simp only [substAtom]
      cases hl : lookupCP cp y with
      | none => rfl
      | some c => simp only [evalAtom]; exact (hcp y c (lookupCP_sound hl)).symm

theorem substExpr_eval {cp : ConstPairs} {σ : Store} {e : Expr}
    (hcp : ∀ y c, (y, c) ∈ cp → σ y = c) : eval σ (substExpr cp e) = eval σ e := by
  cases e <;> simp [substExpr, eval, substAtom_eval hcp]

/-! ## The transform. -/

variable (S : CPSpec P)

/-- Substitute known constants into an assignment's RHS and fold; carry everything else verbatim. -/
def foldCmd (n : Node) : Cmd → Cmd
  | .assign x e next => .assign x (Tac.Peephole.peepholeExpr (substExpr (S.sol n) e)) next
  | other            => other

theorem foldCmd_succs {n : Node} (c : Cmd) : (foldCmd S n c).succs = c.succs := by
  cases c <;> rfl

/-- **Constant-folding pass.** -/
def run (P : Program) (S : CPSpec P) : Program where
  entry := P.entry
  code  := ((List.range P.size).map (fun n => foldCmd S n ((P.fetch n).getD .halt))).toArray
  obs   := P.obs

@[simp] theorem run_entry (P : Program) (S : CPSpec P) : (run P S).entry = P.entry := rfl
@[simp] theorem run_obs (P : Program) (S : CPSpec P) : (run P S).obs = P.obs := rfl
@[simp] theorem run_size (P : Program) (S : CPSpec P) : (run P S).size = P.size := by
  show ((List.range P.size).map _).toArray.size = P.size; simp

theorem run_fetch {n : Node} (h : n < P.size) :
    (run P S).fetch n = some (foldCmd S n ((P.fetch n).getD .halt)) := by
  show ((List.range P.size).map (fun n => foldCmd S n ((P.fetch n).getD .halt))).toArray[n]? = _
  rw [List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem (show n < (List.range P.size).length by simpa using h),
    Option.map_some, List.getElem_range]

theorem run_wellFormed (wf : WellFormed P) : WellFormed (run P S) where
  entry_lt := by rw [run_entry, run_size]; exact wf.entry_lt
  succ_lt := by
    intro n instr s hf hs
    have hn : n < P.size := by have := fetch_lt hf; rwa [run_size] at this
    rw [run_fetch S hn] at hf; injection hf with hf; subst hf
    obtain ⟨c, hc⟩ : ∃ c, P.fetch n = some c := ⟨_, Array.getElem?_eq_getElem hn⟩
    rw [hc, Option.getD_some, foldCmd_succs] at hs
    rw [run_size]; exact wf.succ_lt hc hs

/-! ## Behaviour preservation (fault-exact, under `CPInv`). -/

theorem step_fold {c c' : Config} (hinv : CPInv S c) (h : Step P c c') : Step (run P S) c c' := by
  have hbf := run_fetch S (P := P) (n := c.node) (by cases h <;> exact fetch_lt ‹_›)
  cases h with
  | @assign nd σ x e next v hf hv =>
      rw [hf] at hbf; simp only [Option.getD_some, foldCmd] at hbf
      refine Step.assign hbf ?_
      rw [Tac.Peephole.peepholeExpr_eval, substExpr_eval (fun y c hyc => hinv y c hyc)]; exact hv
  | @ifzT nd σ x z nz hf hz =>
      rw [hf] at hbf; simp only [Option.getD_some, foldCmd] at hbf; exact Step.ifzT hbf hz
  | @ifzF nd σ x z nz hf hz =>
      rw [hf] at hbf; simp only [Option.getD_some, foldCmd] at hbf; exact Step.ifzF hbf hz
  | @noop nd σ next hf =>
      rw [hf] at hbf; simp only [Option.getD_some, foldCmd] at hbf; exact Step.noop hbf

theorem steps_fold {σ : Store} {c : Config} (h : Steps P ⟨P.entry, σ⟩ c) :
    Steps (run P S) ⟨P.entry, σ⟩ c := by
  induction h with
  | refl => exact Steps.refl
  | tail hab hbc ih => exact Steps.tail ih (step_fold S (cpInv_run S hab) hbc)

theorem run_final {c : Config} (h : Final P c) : Final (run P S) c := by
  show (run P S).fetch c.node = some .halt
  rw [run_fetch S (fetch_lt h), h]; rfl

theorem run_faulting {c : Config} (hinv : CPInv S c) (h : Faulting P c) : Faulting (run P S) c := by
  obtain ⟨x, e, next, hf, hev⟩ := h
  refine ⟨x, Tac.Peephole.peepholeExpr (substExpr (S.sol c.node) e), next,
    by rw [run_fetch S (fetch_lt hf), hf]; rfl, ?_⟩
  rw [Tac.Peephole.peepholeExpr_eval, substExpr_eval (fun y c hyc => hinv y c hyc)]; exact hev

/-- **Const-folding preserves halting** (to the identical terminal store). -/
theorem preserves_halt {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ df, Steps (run P S) ⟨(run P S).entry, σ⟩ df ∧ Final (run P S) df
        ∧ ∀ v ∈ P.obs, df.store v = cf.store v :=
  ⟨cf, steps_fold S hrun, run_final S hfin, fun _ _ => rfl⟩

/-- **Const-folding preserves faulting.** -/
theorem preserves_faults {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfault : Faulting P cf) :
    ∃ df, Steps (run P S) ⟨(run P S).entry, σ⟩ df ∧ Faulting (run P S) df :=
  ⟨cf, steps_fold S hrun, run_faulting S (cpInv_run S hrun) hfault⟩

theorem stepSimG : StepSimG P (run P S) (fun c d => CPInv S c ∧ d = c) := by
  intro c c' d _ hR hstep
  obtain ⟨hinv, rfl⟩ := hR
  exact ⟨c', c', step_fold S hinv hstep, Steps.refl, cpInv_step S hinv hstep, rfl⟩

/-- **Const-folding preserves divergence.** -/
theorem preserves_diverges (wf : WellFormed P) {σ : Store}
    (hdiv : Diverges P ⟨P.entry, σ⟩) : Diverges (run P S) ⟨(run P S).entry, σ⟩ := by
  rw [run_entry]
  exact diverges_of_stepsimG (stepSimG S) wf wf.entry_lt ⟨cpInv_entry S, rfl⟩ hdiv

end ConstFold
end Pass
end BaseLanguage
