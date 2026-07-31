-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.Locals
import BaseLanguage.IR.Fold
import BaseLanguage.IR.SubPeeler
/-!
# `IR.LocalsSub` — the base-family `_sub` library.

Every base `Tac.Locals` gen/transp/gather family is contained in its domain universe. The generator's
`gWf` obligation (`GHOST-SPEC-GUIDE.md §3.3`) is discharged, per leaf, by one of these lemmas — so an
analysis whose clauses reference only base families needs **no** hand-written `_sub`.

Two proof shapes only:
* **gen-family** (`genExprs`/`genDefs`/`genVars`/`usedVars`/`definedVars`/`rhsVars`/`condVars`) —
  a `foldl_union_contrib` into the `union`-fold universe;
* **transp/gather-family** (`transpExprs`/`exposedExprs`/`transpDefs`/`transpGenVars`) —
  a `SetOps.mem_filter'` one-liner (they are `filter`s of the universe).

Both axiom-clean `[propext, Classical.choice, Quot.sound]` across all three domains.
-/
namespace BaseLanguage.Tac.Locals
open BaseLanguage.Tac BaseLanguage.Semantics BaseLanguage.Analysis BaseLanguage.IR.SetFold Std
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ### Exprs domain — universe `allExprs`. -/

theorem genExprs_sub (P : Program) (n : Node) : (genExprs P n).Subset (allExprs P) := by
  fold_sub genExprs P n into allExprs set Exprs close [Exprs.empty]

theorem transpExprs_sub (P : Program) (n : Node) : (transpExprs P n).Subset (allExprs P) := fun x hx => (SetOps.mem_filter'.mp hx).1
theorem exposedExprs_sub (P : Program) (n : Node) : (exposedExprs P n).Subset (allExprs P) := fun x hx => genExprs_sub P n x (SetOps.mem_filter'.mp hx).1

/-! ### Defs domain — universe `allDefs`. -/

theorem genDefs_sub (P : Program) (n : Node) : (genDefs P n).Subset (allDefs P) := by
  fold_sub genDefs P n into allDefs set Defs close [Defs.empty]

theorem obsDefs_sub (P : Program) : (obsDefs P).Subset (allDefs P) :=
  fun x hx => (SetOps.mem_filter'.mp hx).1
theorem dataDeps_sub (P : Program) (z : Node) : (dataDeps P z).Subset (allDefs P) :=
  fun x hx => (SetOps.mem_filter'.mp hx).1

theorem transpDefs_sub (P : Program) (n : Node) : (transpDefs P n).Subset (allDefs P) := fun x hx => (SetOps.mem_filter'.mp hx).1

/-! ### Vars domain — assigned-variable universe `allGenVars`. -/

theorem genVars_sub (P : Program) (n : Node) : (genVars P n).Subset (allGenVars P) := by
  fold_sub genVars P n into allGenVars set Vars close [Vars.empty]

theorem transpGenVars_sub (P : Program) (n : Node) : (transpGenVars P n).Subset (allGenVars P) := fun x hx => (SetOps.mem_filter'.mp hx).1

/-! ### Node domain — reachability universe `allNodes` (every node gens itself). -/

theorem genNode_sub (P : Program) (n : Node) : (genNode P n).Subset (allNodes P) := by
  fold_sub genNode P n into allNodes set Defs close [Defs.empty]

theorem transpAllNodes_sub (P : Program) (n : Node) : (transpAllNodes P n).Subset (allNodes P) := fun x hx => (SetOps.mem_filter'.mp hx).1

/-! ### Constant-propagation domain — universe `allConst` (`⟨var, const⟩` from literal copies). -/

theorem genConst_sub (P : Program) (n : Node) : (genConst P n).Subset (allConst P) := by
  fold_sub genConst P n into allConst set ConstPairs close [ConstPairs.empty]

theorem transpConst_sub (P : Program) (n : Node) : (transpConst P n).Subset (allConst P) := fun x hx => (SetOps.mem_filter'.mp hx).1

/-! ### Vars domain — mentioned-variable universe `allVars` (`= obs ∪ ⋃ₙ (usedVars ∪ definedVars)`). -/

theorem usedVars_sub (P : Program) (n : Node) : (usedVars P n).Subset (allVars P) := by
  fold_sub usedVars P n into allVars set Vars close [usedVarList, Vars.ofList]

theorem definedVars_sub (P : Program) (n : Node) : (definedVars P n).Subset (allVars P) := by
  fold_sub definedVars P n into allVars set Vars close [definedVar, Vars.empty]

theorem rhsVars_sub (P : Program) (n : Node) : (rhsVars P n).Subset (allVars P) := by
  fold_sub rhsVars P n into allVars set Vars close [Vars.empty]

theorem condVars_sub (P : Program) (n : Node) : (condVars P n).Subset (allVars P) := by
  fold_sub condVars P n into allVars set Vars close [Vars.empty]

end BaseLanguage.Tac.Locals
