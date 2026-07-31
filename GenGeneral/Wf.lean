-- Copyright (c) 2026 Martin Rinard
import GenGeneral.Printer

/-!
# `GenGeneral.Wf` — generic structural well-formedness proof

`MTC.Wf` is a clean structural recursion (`Solver/Spec.lean:116`): each leaf obligation is `∀ e x ∈ f e, x ∈ univ`,
discharged by that family's `_sub` lemma. This module prints the `<c>Wf` theorem as **one structural map**
over the `Transfer` — the anonymous-constructor conjunction mirrors the term's `∪`/`∩`/`∖`/gate shape,
each leaf a `Std.HashSet.mem_toList.mpr (<fam>_sub …)`. For every fixpoint quadrant incl. the lcm edge kinds (which thread foreign/bound-param `_sub` hypotheses).
Confluence ghosts carry no `<c>Wf` (their bound is `MeetSpec`/`JoinSpec`).
-/

namespace GenGeneral

/-! ## Leaf `_sub` subset proofs -/

/-- A leaf's subset proof term (a `_.Subset (univ P)`, before applying `x hx`). A program family uses its
    `<name>_sub P <params> <hyps> <nodes>` lemma; a bound param uses its threaded hypothesis `h<name>`; a
    `union`/`sdiff` uses the `union_sub`/`interL_sub` combinators over the sub-proofs. -/
partial def leafSubAtom : Leaf → String
  | .fam name params r =>
    let ps := if params.isEmpty then "" else " " ++ " ".intercalate params
    let hyps := if params.isEmpty then "" else " " ++ " ".intercalate (params.map ("h" ++ ·))
    s!"{name}_sub P{ps}{hyps}{nodesOf r}"
  | .bound name r => s!"h{name}{nodesOf r}"
  | .union a b => s!"union_sub ({leafSubAtom a}) ({leafSubAtom b})"
  | .sdiff a b => s!"sdiff_sub ({leafSubAtom a}) ({leafSubAtom b})"
  -- `.empty`/`.univ` are clamp-bound sentinels only; they never appear inside a transfer term, so these
  -- cases are unreachable — but must be total (and valid `⊆ univ` witnesses if ever hit).
  | .empty     => "(fun _ hx => absurd hx Std.HashSet.not_mem_empty)"
  | .univ _    => "(fun _ hx => hx)"

/-- The Wf obligation for one `const`/`diffc`/gate leaf: `fun (binder) x hx => mem_toList.mpr (<atom> x hx)`. -/
def leafWf (l : Leaf) : String :=
  let binder := if l.readsEdge then "(n, n')" else "(n, _)"
  s!"fun {binder} x hx => Std.HashSet.mem_toList.mpr ({leafSubAtom l} x hx)"

/-- The Wf obligation for an `image`/`gather` atom's universe `U` (`∀ x ∈ U, x ∈ univ`): a single
    quantifier, no node binder. `U` is the analysis universe, so `x ∈ U → x ∈ univ` is `mem_toList`. -/
def atomUnivWf (_U : Leaf) : String := "fun x hx => Std.HashSet.mem_toList.mpr hx"

/-! ## Transfer → the flattened Wf conjunction -/

/-- The Wf proof term — a **structural** recursion mirroring the term's `∧`-tree exactly (`MTC.Wf` of a
    `∪`/`∩`/`∖`/gate is a conjunction of the parts, so the proof is the matching **nested** anonymous
    constructor). `var`⇒`by trivial`; a leaf⇒its `_sub` obligation; an atom⇒its universe obligation. A
    flat conjunct list only closes the right-nested diamond (`gen ∪ (var ∩ transp)`); a general term such
    as `(a ∪ b) ∪ c` is left-nested, so the `⟨…⟩` nesting must follow the term. -/
partial def wfProofTerm : Transfer → String
  | .var        => "by trivial"
  | .const l    => leafWf l
  | .union a b  => s!"⟨{wfProofTerm a}, {wfProofTerm b}⟩"
  | .inter a b  => s!"⟨{wfProofTerm a}, {wfProofTerm b}⟩"
  | .diffc a l  => s!"⟨{wfProofTerm a}, {leafWf l}⟩"
  | .gate s r   => s!"⟨{leafWf s}, {leafWf r}⟩"
  -- atom universe `Wf` (`Solver/Spec.lean`: `image/gather U … => ∀ x ∈ U, x ∈ univ`) — a single quantifier, no
  -- node binder; `U` is the analysis universe, so `x ∈ U → x ∈ univ` is `mem_toList`.
  | .image U _  => atomUnivWf U
  | .gather U _ => atomUnivWf U

/-! ## The `<c>Wf` theorem -/

/-- The subset-hypothesis binders for a transfer's def-abstracted params, matching the `<c>T` signature:
    `(h<name> : ∀ n, (<name> n).Subset (<univ> P))` (arity 1) / `(… ∀ i j, (<name> i j).Subset …)` (arity 2). -/
def wfHyps (univ : String) (ps : List (String × Nat)) : String :=
  String.intercalate "" (ps.map (fun (nm, ar) =>
    if ar == 2 then s!" (h{nm} : ∀ i j, ({nm} i j).Subset ({univ} P))"
    else s!" (h{nm} : ∀ n, ({nm} n).Subset ({univ} P))"))

/-- Emit `theorem <c>Wf … : MTC.Wf (list<Et> P) (<c>T P …) := <proof>` (empty for confluence). -/
def printWf (a : AnalysisIR) : String :=
  if a.mode == .confluence then "" else
  let c := a.carried; let et := a.elem; let univ := a.univ.name
  let ps := collectParams a.transfer
  let sig := groupParams a.dom ps
  let hyps := wfHyps univ ps
  let appl := if ps.isEmpty then "" else " " ++ " ".intercalate (ps.map (·.1))
  s!"theorem {c}Wf (P : Program){sig}{hyps} : MTC.Wf (list{et} P) ({c}T P{appl}) :=\n  {wfProofTerm a.transfer}\n"

end GenGeneral
