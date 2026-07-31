-- Copyright (c) 2026 Martin Rinard
import BaseLanguage.IR.TAC

namespace BaseLanguage

/-!
# `Ast` — surface AST with **nested** expressions + a reference interpreter

The verified IR `Tac.Expr` is already three-address (`atom | una op a | bin op a b`,
operators over *atoms*). This module is the **surface layer above** it: expressions nest
arbitrarily, statements are structured (`seq`/`ite`/`while`). `AstToTac.lower` lowers this to the
flat IR (introducing compiler temps); `TextToAst` builds it from text.

This is the **unverified frontend** layer. The `evalS`
interpreter here is the *reference semantics* used to empirically validate lowering (`#eval`).
-/

namespace Ast
open Tac Semantics

/-- Nested surface expression (reuses the IR `Atom`/`Unop`/`Binop`). -/
inductive Expr where
  | atom (a : Atom)
  | una  (op : Unop) (e : Expr)
  | bin  (op : Binop) (e₁ e₂ : Expr)
  deriving Repr, Inhabited

/-- Structured surface statement. `ite`/`while` test their condition with C-style truthiness
    (**nonzero = true**). -/
inductive Stmt where
  | skip
  | assign (x : Var) (e : Expr)
  | seq    (s₁ s₂ : Stmt)
  | ite    (cond : Expr) (thn els : Stmt)   -- if cond ≠ 0 then thn else els
  | while  (cond : Expr) (body : Stmt)      -- while cond ≠ 0 do body
  deriving Repr, Inhabited

/-- Value of an atom under a store. -/
def evalAtom (σ : Store) : Atom → Val
  | .var x => σ x
  | .imm n => n

/-- Reference value of a nested expression: `none` = fault (div/mod by zero), evaluated
    **left-to-right** (so the fault order matches the lowered TAC). -/
def evalE (σ : Store) : Expr → Option Val
  | .atom a       => some (evalAtom σ a)
  | .una op e     => (evalE σ e).map op.denote
  | .bin op e₁ e₂ =>
      match evalE σ e₁ with
      | some a => match evalE σ e₂ with
                  | some b => op.denote a b
                  | none   => none
      | none => none

/-- Point update of a store. -/
def upd (σ : Store) (x : Var) (v : Val) : Store := fun y => if y = x then v else σ y

/-- Run outcome of a statement: terminated with a store, faulted, or ran out of loop fuel. -/
inductive Outcome where
  | ok (σ : Store)
  | fault
  | timeout
  deriving Inhabited

/-- Reference big-step interpreter (loop-fuel `n`). Faults propagate; `timeout` when fuel runs
    out inside a `while`.

    A real **well-founded** `def` (not `partial`) terminating on the lexicographic measure
    `(fuel, sizeOf s)`: `seq`/`ite` recurse with the same `fuel` but a structurally smaller statement;
    `while (fuel+1)` recurses with a strictly smaller `fuel`. This yields the `evalS.eq_*` equation
    lemmas the correctness proof inducts on (a `partial def` is opaque to the kernel — nothing about it
    is provable). Behaviour is identical to the obvious recursion. -/
def evalS : Nat → Stmt → Store → Outcome
  | _,      .skip,        σ => .ok σ
  | _,      .assign x e,  σ => match evalE σ e with | some v => .ok (upd σ x v) | none => .fault
  | fuel,   .seq s₁ s₂,   σ => match evalS fuel s₁ σ with | .ok σ' => evalS fuel s₂ σ' | r => r
  | fuel,   .ite c t e,   σ =>
      match evalE σ c with
      | some v => if v == 0 then evalS fuel e σ else evalS fuel t σ
      | none   => .fault
  | 0,      .while _ _,   _ => .timeout
  | fuel+1, .while c b,   σ =>
      match evalE σ c with
      | some v => if v == 0 then .ok σ
                  else match evalS fuel b σ with
                       | .ok σ' => evalS fuel (.while c b) σ'
                       | r => r
      | none   => .fault
  termination_by fuel s => (fuel, sizeOf s)
  decreasing_by
    all_goals simp_wf
    all_goals first
      | (apply Prod.Lex.right; omega)
      | (apply Prod.Lex.left; omega)

end Ast

end BaseLanguage
