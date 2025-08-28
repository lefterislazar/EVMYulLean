import Mathlib.Data.Finmap

import EvmYul.Yul.Ast
import EvmYul.Yul.State
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps
import EvmYul.Yul.SizeLemmas
import EvmYul.Yul.Exception

import EvmYul.Semantics

namespace EvmYul

namespace Yul

open Ast SizeLemmas

-- ============================================================================
--  INTERPRETER
-- ============================================================================

def head' : Yul.State × List Literal → Yul.State × Literal
  | (s, rets) => (s, List.head! rets)

def cons' (arg : Literal) : Yul.State × List Literal → Yul.State × List Literal
  | (s, args) => (s, arg :: args)

def reverse' : Yul.State × List Literal → Yul.State × List Literal
  | (s, args) => (s, args.reverse)

def multifill' (vars : List Identifier) : Yul.State × List Literal → Yul.State
  | (s, rets) => s.multifill vars rets

/--
TODO: Temporary EvmYul artefact with separate primop implementations.
-/
abbrev primCall (s : Yul.State) (prim : Operation .Yul) (args : List Literal) :=
  step prim .none s args |>.toOption.map (λ (s, lit) ↦ (s, lit.toList)) |>.getD default

mutual
  def evalTail (fuel : Nat) (args : List Expr) : Yul.State × Literal → Yul.State × List Literal
    | (s, arg) => 
      match fuel with
      | 0 => (.OutOfFuel, default)
      | .succ fuel' => cons' arg (evalArgs fuel' args s)

  /--
    `evalArgs` evaluates a list of arguments.
  -/
  def evalArgs (fuel : Nat) (args : List Expr) (s : Yul.State) : Yul.State × List Literal :=
    match fuel with
    | 0 => (.OutOfFuel, default)
    | .succ fuel' =>
      match args with
        | [] => (s, [])
        | arg :: args =>
          evalTail fuel' args (eval fuel' arg s)

  /--
    `call` executes a call of a user-defined function.
  -/
  def call (fuel : Nat) (args : List Literal) (yulFunctionName : YulFunctionName) (s : Yul.State) : Yul.State × List Literal :=
    match fuel with
      | 0 => (.OutOfFuel, default)
      | .succ fuel' =>
        -- This should never return `default` if the state is set up correctly.
        let yulContract := (s.sharedState.accountMap.findD s.toSharedState.executionEnv.codeOwner default).code
        -- This should never return `default` if the state is set up correctly.
        let f := (yulContract.functions.lookup yulFunctionName) |>.getD default
        let s₁ := 👌 s.initcall f.params args
        let s₂ := exec fuel' (.Block f.body) s₁
        let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
    (s₃, List.map s₂.lookup! f.rets)

  -- Safe to call `List.head!` on return values, because the compiler throws an
  -- error when coarity is > 0 in (1) and when coarity is > 1 in all other
  -- cases.

  def evalPrimCall (prim : PrimOp) : Yul.State × List Literal → Yul.State × Literal
    | (s, args) => head' (primCall s prim args)

  def evalCall (fuel : Nat) (f : YulFunctionName) : Yul.State × List Literal → Yul.State × Literal
    | (s, args) =>
      match fuel with
      | 0 => (.OutOfFuel, default)
      | .succ fuel' => head' (call fuel' args f s)

  def execPrimCall (prim : PrimOp) (vars : List Identifier) : Yul.State × List Literal → Yul.State
    | (s, args) => multifill' vars (primCall s prim args)

  def execCall (fuel : Nat) (yulFunctionName : YulFunctionName) (vars : List Identifier) : Yul.State × List Literal → Yul.State
    | (s, args) =>
      match fuel with
      | 0 => .OutOfFuel
      | .succ fuel' => multifill' vars (call fuel' args yulFunctionName s)

  /--
    `execSwitchCases` executes each case of a `switch` statement.
  -/
  def execSwitchCases (fuel : Nat) (s : Yul.State) : List (Literal × List Stmt) → List (Literal × Yul.State)
    | [] => []
    | ((val, stmts) :: cases') =>
      match fuel with
      | 0 => [(default, .OutOfFuel)]
      | .succ fuel' => (val, exec fuel' (.Block stmts) s) :: execSwitchCases fuel' s cases'

  /--
    `eval` evaluates an expression.

    - calls evaluated here are assumed to have coarity 1
  -/
  def eval (fuel : Nat) (expr : Expr) (s : Yul.State) : Yul.State × Literal :=
    match fuel with
    | 0 => (.OutOfFuel, default)
    | .succ fuel' =>
        match expr with

        -- We hit these two cases (`PrimCall` and `Call`) when evaluating:
        --
        --  1. f()                 (expression statements)
        --  2. g(f())              (calls in function arguments)
        --  3. if f() {...}        (if conditions)
        --  4. for {...} f() ...   (for conditions)
        --  5. switch f() ...      (switch conditions)

        | .Call (Sum.inl prim) args => evalPrimCall prim (reverse' (evalArgs fuel' args.reverse s))
        | .Call (Sum.inr yulFunctionName) args        =>
          evalCall fuel' yulFunctionName (reverse' (evalArgs fuel' args.reverse s))
        | .Var id             => (s, s[id]!)
        | .Lit val            => (s, val)

  /--
    `exec` executs a single statement.
  -/
  def exec (fuel : Nat) (stmt : Stmt) (s : Yul.State) : Yul.State :=
    match fuel with
    | 0 => .OutOfFuel
    | .succ fuel' =>
      match stmt with
        | .Block [] => s
        | .Block (stmt :: stmts) =>
          let s₁ := exec fuel' stmt s
          exec fuel' (.Block stmts) s₁

        | .Let vars exprOption =>
            match exprOption with
              | .none =>List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars
              | .some expr =>
                match expr with
                  | .Call (Sum.inl prim) args =>
                    execPrimCall prim vars (reverse' (evalArgs fuel' args.reverse s))
                  | .Call (Sum.inr yulFunctionName) args =>
                    execCall fuel' yulFunctionName vars (reverse' (evalArgs fuel' args.reverse s))
                  | .Var identifier => s.insert vars.head! s[identifier]! -- It should be safe to call head! here if the Yul code is parsed correctly.
                  | .Lit literal => s.insert vars.head! literal -- It should be safe to call head! here if the Yul code is parsed correctly.

        | .If cond body =>
          let (s, cond) := eval fuel' cond s
          if cond ≠ ⟨0⟩ then exec fuel' (.Block body) s else s

        -- "Expressions that are also statements (i.e. at the block level) have
        -- to evaluate to zero values."
        --
        -- (https://docs.soliditylang.org/en/latest/yul.html#restrictions-on-the-grammar)
        --
        -- Thus, we cannot have literals or variables on the RHS.
        | .ExprStmtCall expr =>
             match expr with
               | .Call (Sum.inl prim) args => execPrimCall prim [] (reverse' (evalArgs fuel' args.reverse s))
               | .Call (Sum.inr f) args => execCall fuel' f [] (reverse' (evalArgs fuel' args.reverse s))
               | _ => default -- This case should never occur because we cannot have literals or variables on the RHS, as noted above.

        | .Switch cond cases' default' =>

          let (s₁, cond) := eval fuel' cond s
          let branches := execSwitchCases fuel' s₁ cases'
          let s₂ := exec fuel' (.Block default') s₁
          List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) s₂ branches

        -- A `Break` or `Continue` in the pre or post is a compiler error,
        -- so we assume it can't happen and don't modify the state in these
        -- cases. (https://docs.soliditylang.org/en/v0.8.23/yul.html#loops)
        | .For cond post body => loop fuel' cond post body s
        | .Continue => 🔁 s
        | .Break => 💔 s
        | .Leave => 🚪 s

  /--
    `loop` executes a for-loop.
  -/
  def loop (fuel : Nat) (cond : Expr) (post body : List Stmt) (s : Yul.State) : Yul.State :=
    match fuel with
      | 0 => s.diverge
      | 1 => s.diverge
      | fuel' + 1 + 1 =>
        let (s₁, x) := eval fuel' cond (👌s)
        if x = ⟨0⟩
          then s₁✏️⟦s⟧?
          else
            let s₂ := exec fuel' (.Block body) s₁
            match s₂ with
              | .OutOfFuel                      => s₂✏️⟦s⟧?
              | .Checkpoint (.Break _ _)      => 🧟s₂✏️⟦s⟧?
              | .Checkpoint (.Leave _ _)      => s₂✏️⟦s⟧?
              | .Checkpoint (.Continue _ _)
              | _ =>
                let s₃ := exec fuel' (.Block post) (🧟 s₂)
                let s₄ := s₃✏️⟦s⟧?
                let s₅ := exec fuel' (.For cond post body) s₄
                let s₆ := s₅✏️⟦s⟧?
                s₆

end

notation "🍄" => exec
notation "🌸" => eval

end Yul

end EvmYul
