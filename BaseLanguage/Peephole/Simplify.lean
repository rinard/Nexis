-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC
/-!
# Peephole: verified local expression simplification.

A pure, analysis-free rewrite on assignment right-hand sides (`Expr`), justified entirely by a **local**
`eval`-preservation lemma — no dataflow, no spec, no fixpoint (on strict TAC each `Expr` is a single op
over atoms, so simplification is a single pass). `eval` is an `Option Val` where `none` is a fault
(`div`/`mod` by zero); every rule preserves it **exactly**, so no rewrite adds or removes a
fault (`a / a → 1`, `0 / a → 0` are *unsound* and absent by construction).

Design: two independently-verified simplifiers — `foldExpr` (constant folding) and `idExpr` (algebraic
identities) — composed. Each rule is additive: one arm + one proof case; a new rule can never break an
existing one because the correctness lemmas compose. This is the reusable verified core; program-level
lifting (rewrite every `assign` RHS + behaviour preservation) builds on `peepholeExpr_eval`.
-/
namespace BaseLanguage.Tac.Peephole
open BaseLanguage.Tac BaseLanguage.Semantics

/-! ## Constant folding — evaluate an op on literal operands (fault-preserving). -/

/-- Fold a binary op on two literals, but only when it does not fault. -/
def foldBin (op : Binop) (a b : Val) : Expr :=
  match op.denote a b with
  | some v => .atom (.imm v)
  | none   => .bin op (.imm a) (.imm b)

theorem foldBin_eval (σ : Store) (op : Binop) (a b : Val) :
    eval σ (foldBin op a b) = op.denote a b := by
  unfold foldBin; split <;> simp_all [eval, evalAtom]

/-- Constant folding on an expression. -/
def foldExpr : Expr → Expr
  | .una op (.imm c)          => .atom (.imm (op.denote c))
  | .bin op (.imm a) (.imm b) => foldBin op a b
  | e                         => e

theorem foldExpr_eval (σ : Store) (e : Expr) : eval σ (foldExpr e) = eval σ e := by
  cases e with
  | atom a => rfl
  | una op a => cases a with | var x => rfl | imm c => simp [foldExpr, eval, evalAtom]
  | bin op a b =>
    cases a with
    | var x => rfl
    | imm av => cases b with
      | var x => rfl
      | imm bv => simp only [foldExpr]; rw [foldBin_eval]; rfl

/-! ## Canonicalization — move the constant of a commutative op to the right.

`(imm c) op x  →  x op (imm c)` for the commutative ops. This is the highest-value rule for the *global*
passes: it makes syntactically-equal expressions actually equal, so CSE/LCM can dedupe them. Only the
`imm`-on-left / `var`-on-right shape fires (single, idempotent — the result never re-matches). -/
def canonExpr : Expr → Expr
  | .bin .add (.imm c) (.var x) => .bin .add (.var x) (.imm c)
  | .bin .mul (.imm c) (.var x) => .bin .mul (.var x) (.imm c)
  | .bin .and (.imm c) (.var x) => .bin .and (.var x) (.imm c)
  | .bin .or  (.imm c) (.var x) => .bin .or  (.var x) (.imm c)
  | .bin .xor (.imm c) (.var x) => .bin .xor (.var x) (.imm c)
  | e => e

theorem canonExpr_eval (σ : Store) (e : Expr) : eval σ (canonExpr e) = eval σ e := by
  unfold canonExpr <;> split <;>
    simp only [eval, evalAtom, Binop.denote] <;>
    first
      | rfl
      | exact congrArg some (Int64.add_comm _ _)
      | exact congrArg some (Int64.mul_comm _ _)
      | exact congrArg some (Int64.and_comm _ _)
      | exact congrArg some (Int64.or_comm _ _)
      | exact congrArg some (Int64.xor_comm _ _)

/-! ## Same-operand rules — `x op x` where both operands are the *same* atom (incl. self-comparisons). -/
def selfExpr : Expr → Expr
  | .bin .sub a b => if a = b then .atom (.imm 0) else .bin .sub a b
  | .bin .xor a b => if a = b then .atom (.imm 0) else .bin .xor a b
  | .bin .and a b => if a = b then .atom a else .bin .and a b
  | .bin .or  a b => if a = b then .atom a else .bin .or  a b
  | .bin .eq  a b => if a = b then .atom (.imm 1) else .bin .eq  a b
  | .bin .ne  a b => if a = b then .atom (.imm 0) else .bin .ne  a b
  | .bin .lt  a b => if a = b then .atom (.imm 0) else .bin .lt  a b
  | .bin .le  a b => if a = b then .atom (.imm 1) else .bin .le  a b
  | .bin .ltu a b => if a = b then .atom (.imm 0) else .bin .ltu a b
  | .bin .leu a b => if a = b then .atom (.imm 1) else .bin .leu a b
  | e => e

theorem selfExpr_eval (σ : Store) (e : Expr) : eval σ (selfExpr e) = eval σ e := by
  cases e with
  | atom a => rfl
  | una op a => rfl
  | bin op a b =>
    cases op <;> simp only [selfExpr] <;>
    first
      | rfl
      | (split
         · rename_i h; subst h
           simp [eval, evalAtom, Binop.denote, Val.ofBool,
             BitVec.slt, BitVec.sle, BitVec.ult, BitVec.ule,
             Int64.sub_self, Int64.xor_self, Int64.and_self, Int64.or_self,
             Int.lt_irrefl, Nat.lt_irrefl]
         · rfl)

/-! ## Division / shift by the identity constant (fault-safe: `div` by `1 ≠ 0`). -/
def divShiftExpr : Expr → Expr
  | .bin .div a (.imm 1)  => .atom a
  | .bin .lshr a (.imm 0) => .atom a
  | .bin .ashr a (.imm 0) => .atom a
  | e => e

theorem divShiftExpr_eval (σ : Store) (e : Expr) : eval σ (divShiftExpr e) = eval σ e := by
  unfold divShiftExpr <;> split <;>
    first
      | rfl
      | exact congrArg some Int64.div_one.symm                    -- div a 1 → a  (defeq through `if 1==0`)
      | exact congrArg some Int64.shiftRight_zero.symm            -- ashr a 0 → a
      | simp [eval, evalAtom, Binop.denote, UInt64.shiftRight_zero, Int64.toInt64_toUInt64]  -- lshr a 0 → a

/-! ## Algebraic identities — fault-safe, each a local `eval` equality (no analysis). -/

/-- Simplify one binary op via algebraic identities. Only rules whose `eval` equality holds *for every
    store* and *preserves faulting* are included; the fall-through keeps the expression unchanged. -/
def idExpr : Expr → Expr
  -- additive
  | .bin .add a (.imm 0) => .atom a
  | .bin .add (.imm 0) b => .atom b
  | .bin .sub a (.imm 0) => .atom a
  -- multiplicative (annihilator / unit)
  | .bin .mul _ (.imm 0) => .atom (.imm 0)
  | .bin .mul (.imm 0) _ => .atom (.imm 0)
  | .bin .mul a (.imm 1) => .atom a
  | .bin .mul (.imm 1) b => .atom b
  -- bitwise with 0
  | .bin .or  a (.imm 0) => .atom a
  | .bin .or  (.imm 0) b => .atom b
  | .bin .xor a (.imm 0) => .atom a
  | .bin .xor (.imm 0) b => .atom b
  | .bin .and _ (.imm 0) => .atom (.imm 0)
  | .bin .and (.imm 0) _ => .atom (.imm 0)
  -- left shift by 0
  | .bin .shl a (.imm 0) => .atom a
  | e => e
  -- NOTE (additive extensions, each needs one `Int64.*` lemma, Mathlib-free):
  --   div a 1 → a (Int64.div_one), mod _ 1 → 0 (div_one+mul_one+sub_self),
  --   lshr/ashr a 0 → a (logical/arith shift-by-0 + toUInt64 roundtrip),
  --   sub a a → 0, xor a a → 0, and a a → a, or a a → a  (same-operand, needs Atom-eq guard),
  --   comparisons a a → 1/0, canonicalization (commutative operand order).

theorem idExpr_eval (σ : Store) (e : Expr) : eval σ (idExpr e) = eval σ e := by
  unfold idExpr <;> split <;>
    simp only [eval, evalAtom, Binop.denote] <;>
    first
      | rfl
      | exact congrArg some (Int64.add_zero _).symm
      | exact congrArg some (Int64.zero_add _).symm
      | exact congrArg some (Int64.sub_zero _).symm
      | exact congrArg some (Int64.mul_zero _).symm
      | exact congrArg some (Int64.zero_mul _).symm
      | exact congrArg some (Int64.mul_one _).symm
      | exact congrArg some (Int64.one_mul _).symm
      | exact congrArg some (Int64.or_zero _).symm
      | exact congrArg some (Int64.zero_or _).symm
      | exact congrArg some (Int64.xor_zero _).symm
      | exact congrArg some (Int64.zero_xor _).symm
      | exact congrArg some (Int64.and_zero _).symm
      | exact congrArg some (Int64.zero_and _).symm
      | exact congrArg some Int64.shiftLeft_zero.symm
      | exact congrArg some Int64.zero_mul.symm
      | exact congrArg some Int64.or_zero.symm
      | exact congrArg some Int64.zero_or.symm
      | exact congrArg some Int64.xor_zero.symm
      | exact congrArg some Int64.zero_xor.symm
      | exact congrArg some Int64.and_zero.symm
      | exact congrArg some Int64.zero_and.symm

/-! ## The peephole: fold, then simplify. -/

def peepholeExpr (e : Expr) : Expr := idExpr (divShiftExpr (selfExpr (canonExpr (foldExpr e))))

/-- **Local correctness (fault-exact).** The peephole preserves `eval` on every store — including the
    faulting (`none`) outcome — so it is behaviour-preserving as an assignment-RHS rewrite. -/
theorem peepholeExpr_eval (σ : Store) (e : Expr) : eval σ (peepholeExpr e) = eval σ e := by
  rw [peepholeExpr, idExpr_eval, divShiftExpr_eval, selfExpr_eval, canonExpr_eval, foldExpr_eval]

end BaseLanguage.Tac.Peephole
