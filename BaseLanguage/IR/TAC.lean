-- Copyright (c) 2026 Martin Rinard
namespace BaseLanguage

/-!
# `TAC` — the three-address CFG IR and its small-step reference interpreter

The compiler's mid-level IR (`namespace Tac`) together with its standard small-step semantics,
functional reference interpreter (`run`), and no-stuck metatheory (`namespace Semantics`), in one module.
-/


namespace Tac

/-- Machine word: a 64-bit integer matching the host hardware. Wraps on overflow, total. -/
abbrev Val := Int64

/-- Program variables: `orig` = original source variables (observable); `tmp i` = a fresh
    PRE temporary for expression number `i`. The two namespaces are disjoint by
    construction, so temporaries are structurally fresh and never observed. -/
inductive Var where
  | orig (s : String)
  | tmp  (i : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- Control-flow nodes are stable labels (code-array indices). Appending a node does not
    renumber existing ones, so edge insertion is local. -/
abbrev Node := Nat

/-- An atomic operand: a variable or an immediate constant. -/
inductive Atom where
  | var (x : Var)
  | imm (n : Val)
  deriving DecidableEq, Repr, Inhabited

/-- Unary integer operators. Total on `Int64`. -/
inductive Unop where
  | neg            -- two's-complement negation
  | not            -- bitwise complement
  deriving DecidableEq, Repr, Inhabited

/-- Binary integer operators: arithmetic, bitwise, shifts, division, and comparisons.
    All total on `Int64` **except `div`/`mod`, which fault on a zero divisor**:
    so `denote` is *partial* (`Option Val`, `none` = fault). Comparisons yield `1`/`0`.
    Extend this list freely — see `denote`. -/
inductive Binop where
  | add | sub | mul                -- arithmetic
  | div | mod                      -- division — FAULTS on a zero divisor
  | and | or  | xor                -- bitwise
  | shl | lshr | ashr              -- shifts (by the 2nd operand): left, logical-right, arithmetic-right
  | eq  | ne  | lt | le | ltu | leu  -- comparisons (lt/le signed, ltu/leu unsigned) → 1/0
  deriving DecidableEq, Repr, Inhabited

/-- `1` for `true`, `0` for `false` — the integer result of a comparison. -/
@[inline] def Val.ofBool (b : Bool) : Val := if b then 1 else 0

/-- Meaning of a **unary** operator as a total function on values (neither faults). -/
def Unop.denote : Unop → Val → Val
  | neg, a => -a
  | not, a => ~~~a

/-- Meaning of a **binary** operator as a *partial* function on values: `none` is a **fault**.
    Only `div`/`mod` fault, on a zero divisor; every other operator is total
    (`some …`).

    This is the *single* place that mentions individual operators. `eval` and every proof
    apply `op.denote` opaquely (now threading the `Option`), so the abstraction is intact:
    adding an operator extends this table only — it never adds a case to any proof about
    evaluation or the semantics. -/
def Binop.denote : Binop → Val → Val → Option Val
  | add, a, b => some (a + b)
  | sub, a, b => some (a - b)
  | mul, a, b => some (a * b)
  | div, a, b => if b == 0 then none else some (a / b)
  | mod, a, b => if b == 0 then none else some (a - a / b * b)  -- truncated remainder = AArch64 `sdiv;msub`
  | and, a, b => some (a &&& b)
  | or,  a, b => some (a ||| b)
  | xor, a, b => some (a ^^^ b)
  | shl,  a, b => some (a <<< b)
  | lshr, a, b => some (UInt64.toInt64 (a.toUInt64 >>> b.toUInt64))   -- logical: zero-fill
  | ashr, a, b => some (a >>> b)                                      -- arithmetic: sign-fill
  | eq,  a, b => some (Val.ofBool (a == b))
  | ne,  a, b => some (Val.ofBool (!(a == b)))
  | lt,  a, b => some (Val.ofBool (a.toBitVec.slt b.toBitVec))
  | le,  a, b => some (Val.ofBool (a.toBitVec.sle b.toBitVec))
  | ltu, a, b => some (Val.ofBool (a.toBitVec.ult b.toBitVec))
  | leu, a, b => some (Val.ofBool (a.toBitVec.ule b.toBitVec))

/-- **Totality of an operator** — `true` when `denote op` never returns `none`, i.e. the operator
    cannot fault. Kept **immediately beside `denote`** so the operator table stays the single place that
    mentions individual operators: adding an operator extends `denote` and this table together, and
    `denote_isSome_of_isTotal` right below is the one proof that ties them, discharged by `cases`. -/
def Binop.isTotal : Binop → Bool
  | div | mod => false          -- fault on a zero divisor
  | _         => true

/-- A **total** operator always denotes. The single link between `isTotal` and `denote`. -/
theorem Binop.denote_isSome_of_isTotal {op : Binop} (h : op.isTotal = true) (a b : Val) :
    ∃ v, op.denote a b = some v := by
  cases op with
  | div => simp [Binop.isTotal] at h
  | mod => simp [Binop.isTotal] at h
  | _ => exact ⟨_, rfl⟩

/-- Right-hand side of an assignment, in three-address form: at most one operator over its
    atom operands. A bare `atom` covers copies (`x := y`) and constant loads (`x := 5`). -/
inductive Expr where
  | atom (a : Atom)
  | una  (op : Unop)  (a   : Atom)
  | bin  (op : Binop) (a b : Atom)
  deriving DecidableEq, Repr, Inhabited

/-- **Fault-freedom of an expression** — `true` when `e` evaluates in *every* store (`Semantics.
    eval_isSome_of_faultFree`). Since `atom`/`una` are total by construction, this is exactly totality
    of the top-level binary operator. Purely syntactic and decidable, so it can gate a transformation at
    compile time.

    This is what LCM's divergence-preserving mode hoists: an inserted `t := e` with `e.faultFree` cannot
    turn a divergent run into a fault. See `BaseLanguage/LCM/Divergence.lean`. -/
def Expr.faultFree : Expr → Bool
  | .atom _     => true
  | .una _ _    => true
  | .bin op _ _ => op.isTotal

/-- Commands. Each occupies one node; every non-`halt` command names its successor
    node(s) explicitly (RTL-style). `noop next` is an unconditional transfer (subsumes the
    old `goto`); `halt` has no successor and is the sole terminal. -/
inductive Cmd where
  | assign (x : Var) (e : Expr) (next : Node)
  | ifz    (x : Var) (ifZero ifNonzero : Node)
  | noop   (next : Node)
  | halt
  deriving DecidableEq, Repr, Inhabited

/-- Successor labels of an instruction (`halt` has none). -/
def Cmd.succs : Cmd → List Node
  | assign _ _ next => [next]
  | ifz _ z nz      => [z, nz]
  | noop next       => [next]
  | halt            => []

/-! ## Syntactic projections of the IR  (dataflow-free, single-instruction)

Pure read-offs of one `Var`/`Atom`/`Expr`/`Cmd` — the syntactic analogue of `Cmd.succs`: no CFG
context, no analysis domain, no fixpoint. The frontends, the normalization constraints, and every
optimization's spec are stated over these. The *graph* view (successor/predecessor
lists, reachability) that layers on top lives in `IR.Cfg`. -/

/-- `x` is a source (`.orig`) variable, not a pass-introduced temporary. -/
def varIsOrig : Var → Bool
  | .orig _ => true
  | .tmp _  => false

/-- Does the atom read variable `x`? -/
def atomReadsVar : Atom → Var → Bool
  | .var y, x => decide (y = x)
  | .imm _, _ => false

/-- Does expression `e` mention variable `x` as an operand? -/
def exprReadsVar : Expr → Var → Bool
  | .atom a,    x => atomReadsVar a x
  | .una _ a,   x => atomReadsVar a x
  | .bin _ a b, x => atomReadsVar a x || atomReadsVar b x

/-- A "compute": a non-atom right-hand side (`una`/`bin`). Copies/immediates are not computes. -/
def isNumbered : Expr → Bool
  | .atom _ => false
  | _       => true

/-- The variable an atom reads, if any. -/
def atomVar : Atom → Option Var
  | .var x => some x
  | .imm _ => none

/-- The variables an expression reads. -/
def exprVars : Expr → List Var
  | .atom a    => (atomVar a).toList
  | .una _ a   => (atomVar a).toList
  | .bin _ a b => (atomVar a).toList ++ (atomVar b).toList

/-- The variables an instruction reads (uses). -/
def instrUsedVars : Cmd → List Var
  | .assign _ e _ => exprVars e
  | .ifz x _ _    => [x]
  | _             => []

/-- The variable an instruction defines, if any. -/
def instrDefVar : Cmd → Option Var
  | .assign x _ _ => some x
  | _             => none

/-- A variable read by an expression occurs among its variables. -/
theorem readsVar_imp_mem {e : Expr} {v : Var} (h : exprReadsVar e v = true) : v ∈ exprVars e := by
  have hatom : ∀ a : Atom, atomReadsVar a v = true → v ∈ (atomVar a).toList := by
    intro a ha
    cases a with
    | var y =>
        simp only [atomReadsVar, decide_eq_true_eq] at ha
        simp only [atomVar, Option.toList, List.mem_singleton]; exact ha.symm
    | imm n => simp [atomReadsVar] at ha
  cases e with
  | atom a => simp only [exprVars]; exact hatom a (by simpa [exprReadsVar] using h)
  | una op a => simp only [exprVars]; exact hatom a (by simpa [exprReadsVar] using h)
  | bin op a b =>
      simp only [exprReadsVar, Bool.or_eq_true] at h
      simp only [exprVars, List.mem_append]
      rcases h with ha | hb
      · exact Or.inl (hatom a ha)
      · exact Or.inr (hatom b hb)

/-- A program: an entry node, a code array indexed by node label, and the (finite) list of
    **observable variables** (refinement requires only these to agree).

    `obs` is the program's observable interface and is a **required** field: every program comes with
    its list of observables. For this project it is the source program's original variables (the
    frontend sets it; a value-preserving pass carries it forward). A variable a pass introduces that
    is **not** in `obs` — e.g. an `AstToTac` holding temporary — is unobservable, so refinement need
    not preserve it. -/
structure Program where
  entry : Node
  code  : Array Cmd
  obs   : List Var
  deriving Repr, Inhabited, DecidableEq

/-- Number of nodes. -/
@[inline] def Program.size (P : Program) : Nat := P.code.size

/-- Fetch the instruction at a node, if the label is in range. -/
@[inline] def Program.fetch (P : Program) (n : Node) : Option Cmd := P.code[n]?

/-- **Well-formedness**: the entry is a real node, and every successor label is in range
    (no control edge leaves the graph). With explicit successors there is no fall-through,
    so `halt` is the only terminal and no run gets stuck (see `Semantics.no_stuck_reachable`). -/
structure WellFormed (P : Program) : Prop where
  entry_lt : P.entry < P.size
  succ_lt  : ∀ {n instr s}, P.fetch n = some instr → s ∈ instr.succs → s < P.size

/-- Executable Boolean check matching `WellFormed`. -/
def wellFormedb (P : Program) : Bool :=
  decide (P.entry < P.size) &&
  P.code.all (fun instr => instr.succs.all (fun s => decide (s < P.size)))

end Tac

/-!
# Semantics — standard small-step over the CFG IR

A configuration is a current **node** and a store; `Step P c c'` is one machine step that
follows the explicit successor of the instruction at the node. The store is total, but
evaluation is **partial**: `div`/`mod` by zero **faults**, so `eval` returns
`Option Val`. A well-formed program therefore has **three** outcomes — reach `halt`
(terminate), `Faulting` (divide-by-zero), or step forever (diverge); it never gets truly
*stuck* (`no_stuck_reachable`), because every successor label is in range and there is no
positional fall-through. (`Stuck` now means *out-of-range only*; faults are a separate,
legitimate outcome.)
-/

namespace Semantics

open Tac

/-- A store maps every variable to a 64-bit value. Total ⇒ reads never get stuck. -/
abbrev Store := Var → Val

/-- Point update: `σ[x ↦ v]`. -/
def Store.update (σ : Store) (x : Var) (v : Val) : Store :=
  fun y => if y = x then v else σ y

/-- The conventional initial store: every variable starts at `0`. -/
def Store.init : Store := fun _ => 0

/-- Value of an atom under a store. -/
def evalAtom (σ : Store) : Atom → Val
  | .var x => σ x
  | .imm n => n

/-- Evaluate an assignment right-hand side. **Partial** (`Option Val`): `none` is a fault
    (only `div`/`mod` by zero, via `Binop.denote`). Operators are interpreted by
    their denotations, so this has one arm per *expression shape*, never one per operator; the
    `Option` is threaded uniformly. -/
def eval (σ : Store) : Expr → Option Val
  | .atom a     => some (evalAtom σ a)
  | .una op a   => some (op.denote (evalAtom σ a))
  | .bin op a b => op.denote (evalAtom σ a) (evalAtom σ b)

/-- **A fault-free expression always evaluates.** The semantic content of `Expr.faultFree`. -/
theorem eval_isSome_of_faultFree {σ : Store} {e : Expr} (h : e.faultFree = true) :
    ∃ v, eval σ e = some v := by
  cases e with
  | atom a  => exact ⟨_, rfl⟩
  | una op a => exact ⟨_, rfl⟩
  | bin op a b => exact op.denote_isSome_of_isTotal h _ _

/-- A fault-free expression never faults (the `≠ none` form the block-execution lemmas consume). -/
theorem eval_ne_none_of_faultFree {σ : Store} {e : Expr} (h : e.faultFree = true) :
    eval σ e ≠ none := by
  obtain ⟨v, hv⟩ := eval_isSome_of_faultFree (σ := σ) h; rw [hv]; exact Option.some_ne_none v

/-- A machine configuration: the current node and the store. -/
structure Config where
  node  : Node
  store : Store

/-- **Standard small-step semantics.** Read `Step P c c'` as `P ⊢ c ⟶ c'`.
    Deterministic, and defined at every in-range instruction except `halt`. -/
inductive Step (P : Program) : Config → Config → Prop where
  | assign {nd σ x e next v} :
      P.fetch nd = some (.assign x e next) → eval σ e = some v →
      Step P ⟨nd, σ⟩ ⟨next, σ.update x v⟩
  | ifzT {nd σ x z nz} :
      P.fetch nd = some (.ifz x z nz) → σ x = 0 →
      Step P ⟨nd, σ⟩ ⟨z, σ⟩
  | ifzF {nd σ x z nz} :
      P.fetch nd = some (.ifz x z nz) → σ x ≠ 0 →
      Step P ⟨nd, σ⟩ ⟨nz, σ⟩
  | noop {nd σ next} :
      P.fetch nd = some (.noop next) →
      Step P ⟨nd, σ⟩ ⟨next, σ⟩

@[inherit_doc] scoped notation:40 P:41 " ⊢ " c:41 " ⟶ " c':41 => Step P c c'

/-- Reflexive–transitive closure of `Step`: zero or more steps. -/
inductive Steps (P : Program) : Config → Config → Prop where
  | refl {c} : Steps P c c
  | tail {c c' c''} : Steps P c c' → Step P c' c'' → Steps P c c''

@[inherit_doc] scoped notation:40 P:41 " ⊢ " c:41 " ⟶* " c':41 => Steps P c c'

/-- A **terminal** configuration: the node sits on a `halt`. -/
def Final (P : Program) (c : Config) : Prop := P.fetch c.node = some .halt

/-- A **faulting** configuration: the node is an assignment whose right-hand
    side faults (`div`/`mod` by zero). This is a legitimate run outcome, *not* stuckness. -/
def Faulting (P : Program) (c : Config) : Prop :=
  ∃ x e next, P.fetch c.node = some (.assign x e next) ∧ eval c.store e = none

/-- A **stuck** configuration: not terminal, not faulting, and unable to step — i.e. an
    out-of-range node. Under `WellFormed` no reachable configuration is stuck
    (`no_stuck_reachable`); faults are excluded from `Stuck` and handled separately. -/
def Stuck (P : Program) (c : Config) : Prop :=
  ¬ Final P c ∧ ¬ Faulting P c ∧ ¬ ∃ c', Step P c c'

/-! ## Functional interpreter -/

/-- The result of one functional step: a successor, or a terminal classification. -/
inductive Status where
  | next (c : Config)   -- a normal step to `c`
  | halt                -- reached `halt`
  | fault               -- `div`/`mod` by zero
  | stuck               -- out-of-range node (excluded by `WellFormed`)

def Status.isHalt  : Status → Bool | .halt  => true | _ => false
def Status.isFault : Status → Bool | .fault => true | _ => false

/-- One deterministic step as a function, classifying the outcome. -/
def step1 (P : Program) (c : Config) : Status :=
  match P.fetch c.node with
  | some (.assign x e next) =>
      match eval c.store e with
      | some v => .next ⟨next, c.store.update x v⟩
      | none   => .fault
  | some (.ifz x z nz)      => .next (if c.store x = 0 then ⟨z, c.store⟩ else ⟨nz, c.store⟩)
  | some (.noop next)       => .next ⟨next, c.store⟩
  | some .halt              => .halt
  | none                    => .stuck

/-- The functional step agrees with the relation on normal steps. -/
theorem step1_next_iff {P c c'} : step1 P c = .next c' ↔ Step P c c' := by
  rcases c with ⟨nd, σ⟩
  simp only [step1]
  constructor
  · intro h
    split at h
    · next x e nx heq =>
        split at h
        · next v hv => cases h; exact .assign heq hv
        · next hv => simp at h
    · next x z nz heq =>
        split at h
        · next hz => cases h; exact .ifzT heq hz
        · next hz => cases h; exact .ifzF heq hz
    · next nx heq => cases h; exact .noop heq
    · next heq => simp at h
    · next heq => simp at h
  · intro h
    cases h with
    | assign hf hv => simp [hf, hv]
    | ifzT hf hz => simp [hf, hz]
    | ifzF hf hz => simp [hf, hz]
    | noop hf => simp [hf]

/-- `Step` is deterministic. -/
theorem Step.deterministic {P c c₁ c₂} (h₁ : Step P c c₁) (h₂ : Step P c c₂) : c₁ = c₂ := by
  have e₁ := step1_next_iff.mpr h₁
  have e₂ := step1_next_iff.mpr h₂
  rw [e₁] at e₂
  exact Status.next.inj e₂

/-- Run up to `fuel` steps. Returns the reached configuration and the terminal `Status`
    (`.next` ⇒ fuel ran out while still running). -/
def run (P : Program) (c : Config) : Nat → Config × Status
  | 0       => (c, .next c)
  | fuel+1  =>
    match step1 P c with
    | .next c' => run P c' fuel
    | s        => (c, s)

/-! ## Well-formed programs never get stuck -/

/-- `P.fetch n` is defined exactly when `n` is in range. -/
theorem fetch_some_iff_lt {P : Program} {n} :
    (∃ instr, P.fetch n = some instr) ↔ n < P.size := by
  constructor
  · rintro ⟨instr, h⟩
    simp only [Program.fetch] at h
    rcases Nat.lt_or_ge n P.code.size with hlt | hge
    · exact hlt
    · rw [Array.getElem?_eq_none_iff.mpr hge] at h
      simp at h
  · intro h
    exact ⟨P.code[n], Array.getElem?_eq_getElem h⟩

theorem fetch_lt {P : Program} {n instr} (h : P.fetch n = some instr) : n < P.size :=
  fetch_some_iff_lt.mp ⟨instr, h⟩

theorem fetch_some_of_lt {P : Program} {n} (h : n < P.size) :
    ∃ instr, P.fetch n = some instr :=
  fetch_some_iff_lt.mpr h

/-- **Progress**: any in-range instruction other than `halt` either steps or faults. -/
theorem progress {P : Program} {nd σ instr}
    (hf : P.fetch nd = some instr) (hne : instr ≠ .halt) :
    (∃ c', Step P ⟨nd, σ⟩ c') ∨ Faulting P ⟨nd, σ⟩ := by
  cases instr with
  | assign x e next =>
      cases hv : eval σ e with
      | some v => exact Or.inl ⟨_, .assign hf hv⟩
      | none   => exact Or.inr ⟨x, e, next, hf, hv⟩
  | ifz x z nz =>
      by_cases hz : σ x = 0
      · exact Or.inl ⟨_, .ifzT hf hz⟩
      · exact Or.inl ⟨_, .ifzF hf hz⟩
  | noop next => exact Or.inl ⟨_, .noop hf⟩
  | halt => exact absurd rfl hne

/-- **Preservation of in-range**: every step of a well-formed program lands in range,
    because the taken successor is a successor label and `WellFormed` keeps those in range. -/
theorem step_in_range {P : Program} (wf : WellFormed P) {c c'}
    (h : Step P c c') : c'.node < P.size := by
  cases h with
  | assign hf _ => exact wf.succ_lt hf (by simp [Cmd.succs])
  | ifzT hf _  => exact wf.succ_lt hf (by simp [Cmd.succs])
  | ifzF hf _  => exact wf.succ_lt hf (by simp [Cmd.succs])
  | noop hf    => exact wf.succ_lt hf (by simp [Cmd.succs])

/-- Any configuration reachable from an in-range start is itself in range. -/
theorem reachable_in_range {P : Program} (wf : WellFormed P) {c c'}
    (hnd : c.node < P.size) (h : Steps P c c') : c'.node < P.size := by
  induction h with
  | refl => exact hnd
  | tail _ hstep _ => exact step_in_range wf hstep

/-- In range ⇒ not stuck (it is `Final`, faulting, or can step). -/
theorem not_stuck_of_lt {P : Program} {nd σ} (hnd : nd < P.size) :
    ¬ Stuck P ⟨nd, σ⟩ := by
  rintro ⟨hnf, hnfault, hns⟩
  obtain ⟨instr, hf⟩ := fetch_some_of_lt hnd
  by_cases hh : instr = .halt
  · exact hnf (show P.fetch nd = some .halt by rw [hf, hh])
  · rcases progress hf hh with hstep | hfault
    · exact hns hstep
    · exact hnfault hfault

/-- **No reachable stuck states.** From any in-range start, a well-formed program reaches
    only `Final`-or-steppable configurations — every run halts or diverges, never stuck. -/
theorem no_stuck_reachable {P : Program} (wf : WellFormed P) {nd σ c'}
    (hnd : nd < P.size) (h : Steps P ⟨nd, σ⟩ c') : ¬ Stuck P c' := by
  obtain ⟨nd', σ'⟩ := c'
  exact not_stuck_of_lt (reachable_in_range wf hnd h)

/-! ## `wellFormedb` decides `WellFormed` -/

theorem wellFormedb_iff {P : Program} : wellFormedb P = true ↔ WellFormed P := by
  unfold wellFormedb
  rw [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨he, hall⟩
    refine ⟨he, ?_⟩
    intro n instr s hf hmem
    have hlt := fetch_lt hf
    have hp := Array.all_eq_true.mp hall n hlt
    have hgeq : P.code[n] = instr := by
      have hg : P.fetch n = some P.code[n] := Array.getElem?_eq_getElem hlt
      rw [hg] at hf; exact Option.some.inj hf
    rw [hgeq] at hp
    exact of_decide_eq_true (List.all_eq_true.mp hp s hmem)
  · intro wf
    refine ⟨wf.entry_lt, ?_⟩
    rw [Array.all_eq_true]
    intro i hi
    rw [List.all_eq_true]
    intro s hs
    exact decide_eq_true (wf.succ_lt (Array.getElem?_eq_getElem hi) hs)

/-- `WellFormed` is decidable (via the agreeing `Bool` check). -/
instance {P : Program} : Decidable (WellFormed P) :=
  decidable_of_iff _ wellFormedb_iff

/-! ## Worked example

```
node 0: ifz n 4 1      -- while n ≠ 0 (zero ↦ 4, nonzero ↦ 1)
node 1: s := s + n  → 2
node 2: n := n - 1  → 3
node 3: noop        → 0    -- back-edge to node 0
node 4: halt
```
From `n = 3, s = 0` this computes `s = 6`. -/

/-- The summation loop, in CFG form. -/
def sumLoop : Program := {
  entry := 0,
  code  := #[
    .ifz (.orig "n") 4 1,
    .assign (.orig "s") (.bin .add (.var (.orig "s")) (.var (.orig "n"))) 2,
    .assign (.orig "n") (.bin .sub (.var (.orig "n")) (.imm 1)) 3,
    .noop 0,
    .halt ],
  obs   := [.orig "n", .orig "s"] }

/-- Initial store with `n = 3`, all else `0`. -/
def sumInit : Store := Store.init.update (.orig "n") 3

#eval (run sumLoop ⟨sumLoop.entry, sumInit⟩ 1000).1.store (.orig "s")   -- 6
#eval (run sumLoop ⟨sumLoop.entry, sumInit⟩ 1000).2.isHalt              -- true (halted)

/-- A divide-by-zero faulter: `x := a / b` with `b = 0`. -/
def divZero : Program := {
  entry := 0,
  code  := #[
    .assign (.orig "x") (.bin .div (.var (.orig "a")) (.var (.orig "b"))) 1,
    .halt ],
  obs   := [.orig "x", .orig "a", .orig "b"] }

#eval (run divZero ⟨divZero.entry, Store.init⟩ 10).2.isFault            -- true (faulted: b = 0)

/-! ## Shared reference-semantics lemmas

Basic facts about `Steps`, `run`, and `eval` that several passes need. Kept here at the semantics'
definition site so each consumer (`Behavior`, `Normalize`, `LCM`, `PDCE`) shares one copy rather than
re-proving them. -/

/-- Transitivity of the reflexive-transitive step relation. -/
theorem steps_trans {P : Program} {a b c : Config} (h1 : Steps P a b) (h2 : Steps P b c) :
    Steps P a c := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact Steps.tail ih hstep

/-! ### `StepsPlus` — the **non-stuttering** (≥ 1 step) closure

`Steps` admits the empty run, which is fatal for divergence preservation: an infinite source run may
not collapse to a finite target run, so each source step must be matched by **at least one** target
step (`Behavior.Outcomes.StepSimG`). `StepsPlus` is the leading-`Step`-then-`Steps` shape that engine
consumes. It is not derivable after the fact from `Steps P a c` — a self-looping source node has
`a = c` with a genuine one-step target run — so the block-execution lemmas produce it directly. -/

/-- **One or more steps**: a leading `Step` followed by a `Steps` tail. -/
def StepsPlus (P : Program) (a c : Config) : Prop := ∃ mid, Step P a mid ∧ Steps P mid c

/-- Forget the non-stuttering guarantee. -/
theorem StepsPlus.toSteps {P : Program} {a c : Config} (h : StepsPlus P a c) : Steps P a c := by
  obtain ⟨mid, hstep, hsteps⟩ := h
  induction hsteps with
  | refl => exact Steps.tail Steps.refl hstep
  | tail _ hs ih => exact Steps.tail ih hs

/-- A single step is a `StepsPlus`. -/
theorem StepsPlus.single {P : Program} {a c : Config} (h : Step P a c) : StepsPlus P a c :=
  ⟨c, h, Steps.refl⟩

/-- Build from a leading step and a tail. -/
theorem StepsPlus.of_step_steps {P : Program} {a b c : Config}
    (h1 : Step P a b) (h2 : Steps P b c) : StepsPlus P a c := ⟨b, h1, h2⟩

/-- A (possibly empty) prefix followed by a non-empty run is non-empty. -/
theorem steps_trans_plus {P : Program} {a b c : Config}
    (h1 : Steps P a b) (h2 : StepsPlus P b c) : StepsPlus P a c := by
  revert h2
  induction h1 with
  | refl => exact id
  | tail _ hstep ih => exact fun h2 => ih ⟨_, hstep, h2.toSteps⟩

/-- A non-empty run followed by a (possibly empty) suffix is non-empty. -/
theorem stepsPlus_trans {P : Program} {a b c : Config}
    (h1 : StepsPlus P a b) (h2 : Steps P b c) : StepsPlus P a c := by
  obtain ⟨mid, hstep, hsteps⟩ := h1
  exact ⟨mid, hstep, steps_trans hsteps h2⟩

/-- `run` splits additively: if `a` fuel leaves the machine still running at `c'`, then `a + b` fuel is
    `b` fuel from `c'`. (`b` is explicit so `rw [run_add h]` unifies it from the goal.) -/
theorem run_add {P : Program} {c c' : Config} {a : Nat}
    (h : run P c a = (c', .next c')) (b : Nat) : run P c (a + b) = run P c' b := by
  induction a generalizing c with
  | zero =>
      simp only [run, Prod.mk.injEq, Status.next.injEq] at h
      obtain ⟨rfl, _⟩ := h; rw [Nat.zero_add]
  | succ k ih =>
      rw [show k + 1 + b = (k + b) + 1 by omega]
      simp only [run] at h ⊢
      cases hstep : step1 P c with
      | next d =>
          simp only [hstep] at h ⊢
          exact ih h
      | halt => simp only [hstep] at h; exact absurd h (by simp)
      | fault => simp only [hstep] at h; exact absurd h (by simp)
      | stuck => simp only [hstep] at h; exact absurd h (by simp)

/-- `evalAtom` is invariant under updating a variable the atom does not read. -/
theorem evalAtom_update_not_read {σ : Store} {w : Var} {v : Val} {a : Atom}
    (h : atomReadsVar a w = false) : evalAtom (σ.update w v) a = evalAtom σ a := by
  cases a with
  | var x =>
      simp only [atomReadsVar, decide_eq_false_iff_not] at h
      simp only [evalAtom, Store.update, if_neg h]
  | imm n => rfl

/-- `eval` is invariant under updating a variable the expression does not read. -/
theorem eval_update_not_read {σ : Store} {w : Var} {v : Val} {e : Expr}
    (h : exprReadsVar e w = false) : eval (σ.update w v) e = eval σ e := by
  cases e with
  | atom a => simp only [eval, evalAtom_update_not_read (by simpa [exprReadsVar] using h)]
  | una op a => simp only [eval, evalAtom_update_not_read (by simpa [exprReadsVar] using h)]
  | bin op a b =>
      simp only [exprReadsVar, Bool.or_eq_false_iff] at h
      simp only [eval, evalAtom_update_not_read h.1, evalAtom_update_not_read h.2]

end Semantics

end BaseLanguage
