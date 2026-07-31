-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

/-!
# `Analysis.Augmented` — augmented operational semantics, Preservation and Progress

The prophecy/history-variables framework (§2 of the prior work), instantiated for this project's
operational ghost specifications.

The paper augments the standard state `⟨l, σ⟩` with a prophecy/history variable `π` drawn from the
analysis domain `α`, giving an augmented state `⟨l, σ, π⟩` and an augmented step `⇒`. It then asks:

* **Preservation (Def 2.1):** `⟨l,σ,π⟩ ⇒ ⟨l',σ',π'⟩` ⟹ `⟨l,σ⟩ → ⟨l',σ'⟩` — the augmentation adds no
  executions.
* **Progress (Def 2.2):** `⟨l,σ⟩ → ⟨l',σ'⟩` ⟹ `⟨l,σ,β•l⟩ ⇒ ⟨l',σ',β•l'⟩` — the analysis result `β`
  (here a family `g : Node → α`, with `β•l = g l`) lifts every standard step.

Together they make `⟨l,σ⟩ ~ ⟨l,σ,β•l⟩` a bisimulation between the standard and augmented semantics.

In our declarative formulation the augmented step is just a standard `Step` carrying `π` and required to
satisfy the ghost's **per-step relation** `R` (for a prophecy variable `R` also carries the prophecy
precondition — its node-local `check`/`floor` clause folded at the source). Hence Preservation is the
trivial projection, and Progress is *exactly* the analysis's validity (`check`/`predict`/`update`) — the
streamlined reasoning the paper advertises. The per-analysis instantiations (the per-step relations
`<ghost>R` and their `<ghost>_drives` witnesses, plus `<ghost>_preservation`/`<ghost>_progress`/
`<ghost>_bisim`) are **emitted by `gen`** (`GenGeneral.emitAugmented`) into `Seam/<name>/Augmented.lean`
for every shipped analysis (each `import`s this framework and the analysis's generated `ValidExtremal`);
there are no hand-written per-analysis `Augmented.lean` files.
-/

namespace BaseLanguage.Analysis
open Tac Semantics
set_option linter.unusedVariables false

/-- An **augmented configuration** `⟨l, σ, π⟩`: a standard `Config` paired with a ghost value `π ∈ α`
    drawn from the analysis domain. -/
structure Aug (α : Type) where
  cfg : Config
  pi  : α

/-- The **augmented step** `⟨l,σ,π⟩ ⇒ ⟨l',σ',π'⟩`: a standard `Step` threaded with the per-step ghost
    transition `R c π c' π'` (which, for a prophecy variable, also encodes the prophecy precondition
    that filters out incorrect predictions). -/
def AugStep {α : Type} (P : Program) (R : Config → α → Config → α → Prop) (a a' : Aug α) : Prop :=
  Step P a.cfg a'.cfg ∧ R a.cfg a.pi a'.cfg a'.pi


/-- **Preservation (Def 2.1).** The augmented semantics introduces no new executions: every augmented
    step projects to a standard step. (Definitional — the augmented step *contains* the standard one.) -/
theorem preservation {α : Type} {P : Program} {R : Config → α → Config → α → Prop} {a a' : Aug α}
    (h : AugStep P R a a') : Step P a.cfg a'.cfg := h.1

/-- An analysis family `g` (`β•l = g l`) **drives** `R` when its values satisfy the per-step transition
    on every standard step. This is precisely the analysis's *validity* — its `check`/`predict`/`update`
    constraints — so a valid analysis drives its own augmented transition. -/
def Drives {α : Type} (P : Program) (R : Config → α → Config → α → Prop) (g : Node → α) : Prop :=
  ∀ c c', Step P c c' → R c (g c.node) c' (g c'.node)

/-- **Progress (Def 2.2).** A valid analysis (one that `Drives` its `R`) lifts every standard step to an
    augmented step over its results `β•l = g (·.node)`. -/
theorem progress {α : Type} {P : Program} {R : Config → α → Config → α → Prop} {g : Node → α}
    (hg : Drives P R g) {c c' : Config} (hs : Step P c c') :
    AugStep P R ⟨c, g c.node⟩ ⟨c', g c'.node⟩ := ⟨hs, hg c c' hs⟩

/-- The bisimulation relation `⟨l,σ⟩ ~ ⟨l,σ,β•l⟩` induced by Preservation + Progress: the augmented
    config is the standard one carrying the analysis result at its node. -/
def Bisim {α : Type} (g : Node → α) (c : Config) (a : Aug α) : Prop :=
  a.cfg = c ∧ a.pi = g c.node

/-- **The bisimulation.** Preservation + Progress: every standard step is matched by an augmented step
    relating bisimilar configurations, and conversely every augmented step projects to a standard step.
    (For a valid analysis `g`.) -/
theorem bisim {α : Type} {P : Program} {R : Config → α → Config → α → Prop} {g : Node → α}
    (hg : Drives P R g) :
    (∀ c c', Step P c c' → AugStep P R ⟨c, g c.node⟩ ⟨c', g c'.node⟩) ∧
    (∀ a a' : Aug α, AugStep P R a a' → Step P a.cfg a'.cfg) :=
  ⟨fun _ _ hs => progress hg hs, fun _ _ h => preservation h⟩

/-! ## Closure metarules (Def 2.3 / 2.4)

Helper conditions on `R` that often discharge Progress: a prophecy `R` is *downward* closed (moving
down the domain order takes fewer future executions into account — at control-flow splits), a history `R`
is *upward* closed (moving up takes more past executions into account — at joins). -/

/-- **Downward-closure metarule (Def 2.3)** — typical of prophecy variables. -/
def DownClosed {α : Type} [LE α] (R : Config → α → Config → α → Prop) : Prop :=
  ∀ c π c' π' π'', R c π c' π' → π'' ≤ π' → R c π c' π''

/-- **Upward-closure metarule (Def 2.4)** — typical of history variables. -/
def UpClosed {α : Type} [LE α] (R : Config → α → Config → α → Prop) : Prop :=
  ∀ c π c' π' π'', R c π c' π' → π' ≤ π'' → R c π c' π''

end BaseLanguage.Analysis
