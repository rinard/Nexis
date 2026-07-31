-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.Peephole.Simplify
import BaseLanguage.Behavior.Outcomes
import BaseLanguage.IR.Cfg
/-!
# Peephole: the program pass + full behaviour preservation.

`peephole : Program → Program` rewrites every assignment's right-hand side by `peepholeExpr`, leaving the
CFG (nodes, successors, entry, observables) **exactly** unchanged — an `Array.map` of a per-instruction
rewrite, the same shape as `Normalize.deDeg`. Because `peepholeExpr_eval` preserves `eval` on every store,
every source `Step` maps one-to-one to a target `Step` to the *identical* config (store relation =
identity). From that single-step simulation the project's generic engine gives **halt / fault / diverge**
preservation:

* `peephole_preserves_halt`     — a halting run halts to a config observably equal on `P.obs`.
* `peephole_preserves_faultSteps` — a run into a faulting config maps to one into a faulting config.
* `peephole_preserves_diverge`  — a divergent run stays divergent.

No new semantics, no fixpoint, no dataflow — a local rewrite lifted through the audited step relation.
-/
namespace BaseLanguage.Tac.Peephole
open BaseLanguage Tac Semantics

/-! ## The transform (CFG-structure preserving). -/

/-- Simplify an assignment's RHS; carry every other instruction verbatim. -/
def peepholeCmd : Cmd → Cmd
  | .assign x e next => .assign x (peepholeExpr e) next
  | other            => other

/-- The peephole pass: same entry / observables; each assignment's RHS simplified. -/
def peephole (P : Program) : Program where
  entry := P.entry
  code  := P.code.map peepholeCmd
  obs   := P.obs

@[simp] theorem peephole_entry (P : Program) : (peephole P).entry = P.entry := rfl
@[simp] theorem peephole_obs   (P : Program) : (peephole P).obs = P.obs := rfl
@[simp] theorem peephole_size  (P : Program) : (peephole P).size = P.size := by
  show (P.code.map peepholeCmd).size = P.code.size; simp

/-- Fetch commutes with the per-instruction rewrite. -/
theorem peephole_fetch (P : Program) (nd : Node) :
    (peephole P).fetch nd = (P.fetch nd).map peepholeCmd := by
  show (P.code.map peepholeCmd)[nd]? = (P.code[nd]?).map peepholeCmd
  rw [Array.getElem?_map]

/-- The rewrite never touches control targets. -/
@[simp] theorem peepholeCmd_succs (instr : Cmd) : (peepholeCmd instr).succs = instr.succs := by
  cases instr <;> rfl

/-- **Well-formedness is preserved** — same entry, same successors. -/
theorem peephole_wellFormed (P : Program) (hwf : WellFormed P) : WellFormed (peephole P) where
  entry_lt := by rw [peephole_entry, peephole_size]; exact hwf.entry_lt
  succ_lt := by
    intro nd instr s hf hs
    rw [peephole_size]
    rw [peephole_fetch] at hf
    cases hpf : P.fetch nd with
    | none => rw [hpf] at hf; simp at hf
    | some instr0 =>
        rw [hpf] at hf; simp only [Option.map_some] at hf; injection hf with hf; subst hf
        rw [peepholeCmd_succs] at hs
        exact hwf.succ_lt hpf hs

/-! ## One-to-one step lift (via `peepholeExpr_eval`). -/

/-- Every source step maps to one `peephole` step to the identical config: assignments evaluate the same
    (`peepholeExpr_eval`); branches/noops are carried verbatim. -/
theorem step_lift {P : Program} {c c' : Config} (h : Step P c c') : Step (peephole P) c c' := by
  cases h with
  | @assign nd σ x e next v hf hv =>
      have hf' : (peephole P).fetch nd = some (.assign x (peepholeExpr e) next) := by
        rw [peephole_fetch, hf]; simp [peepholeCmd]
      exact Step.assign hf' (by rw [peepholeExpr_eval]; exact hv)
  | @ifzT nd σ x z nz hf hz =>
      exact Step.ifzT (show (peephole P).fetch nd = some (.ifz x z nz) by
        rw [peephole_fetch, hf]; simp [peepholeCmd]) hz
  | @ifzF nd σ x z nz hf hz =>
      exact Step.ifzF (show (peephole P).fetch nd = some (.ifz x z nz) by
        rw [peephole_fetch, hf]; simp [peepholeCmd]) hz
  | @noop nd σ next hf =>
      exact Step.noop (show (peephole P).fetch nd = some (.noop next) by
        rw [peephole_fetch, hf]; simp [peepholeCmd])

theorem steps_lift {P : Program} {c c' : Config} (h : Steps P c c') : Steps (peephole P) c c' := by
  induction h with
  | refl => exact Steps.refl
  | tail _ hstep ih => exact Steps.tail ih (step_lift hstep)

/-! ## Behaviour preservation: halt, fault, diverge. -/

/-- **`peephole` preserves a halting run** (to an observably-equal terminal — here, an identical store). -/
theorem peephole_preserves_halt {P : Program} {σ : Store} {cf : Config}
    (hrun : Steps P ⟨P.entry, σ⟩ cf) (hfin : Final P cf) :
    ∃ cf', Steps (peephole P) ⟨(peephole P).entry, σ⟩ cf' ∧ Final (peephole P) cf'
         ∧ ∀ v ∈ P.obs, cf'.store v = cf.store v := by
  refine ⟨cf, ?_, ?_, fun v _ => rfl⟩
  · rw [peephole_entry]; exact steps_lift hrun
  · show (peephole P).fetch cf.node = some .halt
    rw [peephole_fetch, hfin]; simp [peepholeCmd]

/-- The identity step-simulation the generic fault/divergence engine plugs into. -/
theorem peephole_stepSim {P : Program} : StepSim P (peephole P) (fun σT σ => σT = σ) := by
  intro c d σT _ hR hstep; subst hR
  exact ⟨d, d.store, step_lift hstep, Steps.refl, rfl⟩

/-- A source fault reflects into a `peephole` fault at the same node (same RHS, `eval` preserved). -/
theorem peephole_faultRefl {P : Program} {cf : Config} {σT : Store}
    (_ : cf.node < P.size) (hR : σT = cf.store) (hflt : Faulting P cf) :
    ∃ cf', Steps (peephole P) ⟨cf.node, σT⟩ cf' ∧ Faulting (peephole P) cf' := by
  subst hR; obtain ⟨x, e, next, hf, hev⟩ := hflt
  exact ⟨⟨cf.node, cf.store⟩, Steps.refl, x, peepholeExpr e, next,
    by rw [peephole_fetch, hf]; simp [peepholeCmd], by rw [peepholeExpr_eval]; exact hev⟩

/-- **`peephole` preserves divergence.** -/
theorem peephole_preserves_diverge {P : Program} (hwf : WellFormed P) {σ : Store}
    (hd : Diverges P ⟨P.entry, σ⟩) : Diverges (peephole P) ⟨(peephole P).entry, σ⟩ := by
  rw [peephole_entry]
  exact diverges_of_stepsim peephole_stepSim hwf hwf.entry_lt rfl hd

/-- **`peephole` preserves faults** (composable `Steps`-into-`Faulting` form). -/
theorem peephole_preserves_faultSteps {P : Program} (hwf : WellFormed P) {σ : Store} {cf : Config}
    (hs : Steps P ⟨P.entry, σ⟩ cf) (hflt : Faulting P cf) :
    ∃ cf', Steps (peephole P) ⟨(peephole P).entry, σ⟩ cf' ∧ Faulting (peephole P) cf' := by
  rw [peephole_entry]
  exact faultSteps_of_stepsim peephole_stepSim hwf peephole_faultRefl hwf.entry_lt rfl hs hflt

/-! ## Structural (CFG) preservation — the graph is identical, so reachability transfers.

`succList` is preserved exactly (the rewrite touches only assignment RHSs), so `peephole` keeps
`AllReachable` — the reachability precondition `normalize`'s `WellNormalized` output needs. This is what
lets `peephole` sit *before* `normalize` in the optimizing pipeline
(`lower → peephole → normalize → …`). -/

@[simp] theorem peephole_succList (P : Program) (nd : Node) :
    succList (peephole P) nd = succList P nd := by
  simp only [succList, peephole_fetch]
  cases P.fetch nd with
  | none => rfl
  | some instr => simp [peepholeCmd_succs]

/-- Forward reachability transfers (same entry, same successor edges). -/
theorem peephole_FReach {P : Program} {nd : Node} (h : FReach P nd) : FReach (peephole P) nd := by
  induction h with
  | entry => exact FReach.entry
  | step _ hs ih => exact FReach.step ih (by rw [peephole_succList]; exact hs)

theorem peephole_allReachable (P : Program) (har : AllReachable P) : AllReachable (peephole P) :=
  fun nd hlt => peephole_FReach (har nd (by rwa [peephole_size] at hlt))

end BaseLanguage.Tac.Peephole
