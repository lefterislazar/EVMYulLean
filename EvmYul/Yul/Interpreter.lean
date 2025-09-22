import Mathlib.Data.Finmap

import EvmYul.Yul.Ast
import EvmYul.Yul.State
import EvmYul.Yul.PrimOps
import EvmYul.Yul.StateOps
import EvmYul.Yul.SizeLemmas
import EvmYul.Yul.Exception

import EvmYul.Semantics

set_option maxHeartbeats 400000 -- Needs more than 200000

namespace EvmYul

namespace Yul

open Ast SizeLemmas

-- ============================================================================
--  INTERPRETER
-- ============================================================================

def head' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
  | .ok (s, rets) => .ok (s, List.head! rets)
  | .error e => .error e

def cons' (arg : Literal) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, arg :: args)
  | .error e => .error e

def reverse' : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × List Literal)
  | .ok (s, args) => .ok (s, args.reverse)
  | .error e => .error e

def multifill' (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
  | .ok (s, rets) => .ok (s.multifill vars rets)
  | .error e => .error e

def setStatic (s : State) (p : Bool) : State :=
  match s with
  | .OutOfFuel => .OutOfFuel
  | .Checkpoint j => .Checkpoint j
  | .Ok sharedState varstore =>
    let executionEnvStatic := { sharedState.executionEnv with
                                perm := p
                              }
    let sharedState' := { sharedState with
                          executionEnv := executionEnvStatic
                        }
    .Ok sharedState' varstore

mutual
/--
TODO: Temporary EvmYul artefact with separate primop implementations.
-/
def primCall (fuel : ℕ) (s₀ : State) (prim : Operation .Yul) (args : List Literal) : Except Yul.Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel₁ => 
      match prim with
      | .CALL =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩
            then .error .StaticModeViolation
            else 
              let address := AccountAddress.ofUInt256 address_arg
              let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
              let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner address value)
              match accountMap₁Opt with
                | .none =>
                  match s₀ with
                    | .OutOfFuel => .error .OutOfFuel
                    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                    | .Ok sharedState₀ varstore =>
                      let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                      .ok (.Ok sharedState₁ varstore, [⟨0⟩]) -- Insufficient funds: return 0 to indicate error, with empty return data 
                | .some accountMap₁ =>
                  if s₀.toSharedState.executionEnv.depth ≥ 1024
                  then
                    match s₀ with
                      | .OutOfFuel => .error .OutOfFuel
                      | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                      | .Ok sharedState₀ varstore =>
                        let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                        .ok (.Ok sharedState₁ varstore, [⟨0⟩])  -- Reached depth limit: return 0 to indicate error, with empty return data 
                  else
                    match s₀ with
                    | .OutOfFuel => .error .OutOfFuel
                    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                    | .Ok sharedState varstore =>
                        match s₀.sharedState.accountMap.find? address with
                          | .none => 
                            match s₀ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₀ varstore =>
                                let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                                .ok (.Ok sharedState₁ varstore, [⟨1⟩])  -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                          | .some yulContract =>
                            let executionEnv₁ := { sharedState.executionEnv with
                                                      calldata := calldata₁,
                                                      code := yulContract.code,
                                                      codeOwner := address,
                                                      source := s₀.executionEnv.codeOwner,
                                                      weiValue := value
                                                      depth := s₀.toSharedState.executionEnv.depth + 1
                                                  }
                            let sharedState₁ := { sharedState with
                                                    executionEnv := executionEnv₁,
                                                    memory := default,
                                                    accountMap := accountMap₁
                                                }
                            let s₁ : State := .Ok sharedState₁ default
                            
                            match callFromCode fuel₁ [] .none s₁ with
                            | .error (.YulHalt s₂ _) => 
                              let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                              match s₂ with
                                | .OutOfFuel => .error .OutOfFuel
                                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                                | .Ok sharedState₂ _ =>
                                
                                  -- Restore ExecutionEnv
                                  let executionEnv₃ := { sharedState₂.executionEnv with
                                                      calldata := default,
                                                      code := s₀.toSharedState.executionEnv.code,
                                                      codeOwner := s₀.toSharedState.executionEnv.codeOwner,
                                                      source := s₀.executionEnv.source,
                                                      weiValue := s₀.executionEnv.weiValue,
                                                  }
                                  let sharedState₃ := { sharedState₂ with
                                                          memory := memory₃,
                                                          returnData := s₂.toMachineState.H_return,
                                                          executionEnv := executionEnv₃
                                                      }
                                  .ok (.Ok sharedState₃ varstore, [⟨1⟩])
                            | .error e => .error e
                            | .ok (s₂, _) =>
                              
                              /- We note here that if:
                                    `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                                  then we are writing beyond the theoretical memory size limit.
                                  The yellow paper is unclear on the semantics of this (at the time of writing).
                                  We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                                  And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                                  In practice, this is essentially impossible to occur due to the
                                    prohibitively large gas cost of allocating this much memory. -/
                              let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                              match s₂ with
                                | .OutOfFuel => .error .OutOfFuel
                                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                                | .Ok sharedState₂ _ =>
                                  let sharedState₃ := { sharedState₂ with
                                                          memory := memory₃,
                                                          returnData := s₂.toMachineState.H_return
                                                      }
                                  .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .STATICCALL =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
                let s₀Static : State := setStatic s₀ false
                if ¬s₀Static.executionEnv.perm ∧ value ≠ ⟨0⟩
                then .error .StaticModeViolation
                else 
                  let address := AccountAddress.ofUInt256 address_arg
                  let calldata₁ := s₀Static.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
                  let accountMap₁Opt := (s₀Static.sharedState.accountMap.transferBalance .Yul s₀Static.executionEnv.codeOwner address value)
                  match accountMap₁Opt with
                    | .none =>
                      match s₀ with
                        | .OutOfFuel => .error .OutOfFuel
                        | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                        | .Ok sharedState₀ varstore =>
                          let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                          .ok (.Ok sharedState₁ varstore, [⟨0⟩]) -- Insufficient funds: return 0 to indicate error, with empty return data 
                    | .some accountMap₁ =>
                      if s₀Static.toSharedState.executionEnv.depth ≥ 1024
                      then
                        match s₀Static with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₀ varstore =>
                            let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                            .ok (.Ok sharedState₁ varstore, [⟨0⟩])  -- Reached depth limit: return 0 to indicate error, with empty return data 
                      else
                        match s₀Static with
                        | .OutOfFuel => .error .OutOfFuel
                        | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                        | .Ok sharedState varstore =>
                            match s₀Static.sharedState.accountMap.find? address with
                              | .none => 
                                match s₀Static with
                                  | .OutOfFuel => .error .OutOfFuel
                                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                                  | .Ok sharedState₀ varstore =>
                                    let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                                    .ok (.Ok sharedState₁ varstore, [⟨1⟩])  -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                              | .some yulContract =>
                                let executionEnv₁ := { sharedState.executionEnv with
                                                          calldata := calldata₁,
                                                          code := yulContract.code,
                                                          codeOwner := address,
                                                          source := s₀Static.executionEnv.codeOwner,
                                                          weiValue := value
                                                          depth := s₀Static.toSharedState.executionEnv.depth + 1
                                                      }
                                let sharedState₁ := { sharedState with
                                                        executionEnv := executionEnv₁,
                                                        memory := default,
                                                        accountMap := accountMap₁
                                                    }
                                let s₁ : State := .Ok sharedState₁ default
                                
                                match callFromCode fuel₁ [] .none s₁ with
                                  | .error e => .error e
                                  | .ok (s₂, _) =>
                                
                                  /- We note here that if:
                                        `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                                      then we are writing beyond the theoretical memory size limit.
                                      The yellow paper is unclear on the semantics of this (at the time of writing).
                                      We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                                      And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                                      In practice, this is essentially impossible to occur due to the
                                        prohibitively large gas cost of allocating this much memory. -/
                                  let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀Static.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                                  match s₂ with
                                    | .OutOfFuel => .error .OutOfFuel
                                    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                                    | .Ok sharedState₂ _ =>
                                      let sharedState₃ := { sharedState₂ with
                                                              memory := memory₃,
                                                              returnData := s₂.toMachineState.H_return
                                                          }
                                      .ok (setStatic (.Ok sharedState₃ varstore) s₀.toSharedState.executionEnv.perm, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .CALLCODE =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩
            then .error .StaticModeViolation
            else 
              let address := AccountAddress.ofUInt256 address_arg
              let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
              let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner s₀.executionEnv.codeOwner value)
              match accountMap₁Opt with
                | .none =>
                    match s₀ with
                      | .OutOfFuel => .error .OutOfFuel
                      | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                      | .Ok sharedState₀ varstore =>
                        let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                        .ok (.Ok sharedState₁ varstore, [⟨0⟩]) -- Insufficient funds: return 0 to indicate error, with empty return data 
                | .some accountMap₁ =>
                  if s₀.toSharedState.executionEnv.depth ≥ 1024
                  then
                    match s₀ with
                      | .OutOfFuel => .error .OutOfFuel
                      | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                      | .Ok sharedState₀ varstore =>
                        let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                        .ok (.Ok sharedState₁ varstore, [⟨0⟩]) -- Reached depth limit: return 0 to indicate error, with empty return data 
                  else
                    match s₀ with
                    | .OutOfFuel => .error .OutOfFuel
                    | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                    | .Ok sharedState varstore =>
                        match s₀.sharedState.accountMap.find? address with
                          | .none => 
                            match s₀ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₀ varstore =>
                                let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                                .ok (.Ok sharedState₁ varstore, [⟨1⟩])  -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                          | .some yulContract =>
                            let executionEnv₁ := { sharedState.executionEnv with
                                                      calldata := calldata₁,
                                                      code := yulContract.code,
                                                      source := s₀.executionEnv.codeOwner,
                                                      weiValue := value
                                                      depth := s₀.toSharedState.executionEnv.depth + 1
                                                  }
                            let sharedState₁ := { sharedState with
                                                    executionEnv := executionEnv₁,
                                                    accountMap := accountMap₁
                                                }
                            let s₁ : State := .Ok sharedState₁ default
                            
                            match callFromCode fuel₁ [] .none s₁ with
                            | .error e => .error e
                            | .ok (s₂, _) =>                            
                              /- We note here that if:
                                    `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                                  then we are writing beyond the theoretical memory size limit.
                                  The yellow paper is unclear on the semantics of this (at the time of writing).
                                  We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                                  And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                                  In practice, this is essentially impossible to occur due to the
                                    prohibitively large gas cost of allocating this much memory. -/
                              let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₂.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                              match s₂ with
                                | .OutOfFuel => .error .OutOfFuel
                                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                                | .Ok sharedState₂ _ =>
                                  let sharedState₃ := { sharedState₂ with
                                                          memory := memory₃,
                                                          returnData := s₂.toMachineState.H_return
                                                      }
                                  .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .DELEGATECALL =>
        match args with
          | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
              let address := AccountAddress.ofUInt256 address_arg
              let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
              if s₀.toSharedState.executionEnv.depth ≥ 1024
              then
                match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState₀ varstore =>
                    let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                    .ok (.Ok sharedState₁ varstore, [⟨0⟩])  -- Reached depth limit: return 0 to indicate error, with empty return data 
              else
                match s₀ with
                | .OutOfFuel => .error .OutOfFuel
                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                | .Ok sharedState varstore =>
                    match s₀.sharedState.accountMap.find? address with
                      | .none => 
                        match s₀ with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₀ varstore =>
                            let sharedState₁ := {sharedState₀ with H_return := ByteArray.empty }
                            .ok (.Ok sharedState₁ varstore, [⟨1⟩])  -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                      | .some yulContract =>
                        let executionEnv₁ := { sharedState.executionEnv with
                                                  calldata := calldata₁,
                                                  code := yulContract.code,
                                                  depth := s₀.toSharedState.executionEnv.depth + 1
                                              }
                        let sharedState₁ := { sharedState with
                                                executionEnv := executionEnv₁
                                            }
                        let s₁ : State := .Ok sharedState₁ default
                        
                        match callFromCode fuel₁ [] .none s₁ with
                          | .error e => .error e
                          | .ok (s₂, _) =>                        
                          /- We note here that if:
                                `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                              then we are writing beyond the theoretical memory size limit.
                              The yellow paper is unclear on the semantics of this (at the time of writing).
                              We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                              And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                              In practice, this is essentially impossible to occur due to the
                                prohibitively large gas cost of allocating this much memory. -/
                          let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₂.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                          match s₂ with
                            | .OutOfFuel => .error .OutOfFuel
                            | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                            | .Ok sharedState₂ _ =>
                              let sharedState₃ := { sharedState₂ with
                                                      memory := memory₃,
                                                      returnData := s₂.toMachineState.H_return
                                                  }
                              .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | _ => match step prim .none s₀ args with
              | .ok (s, lit) => .ok (s, lit.toList)
              | .error e => .error e

  def evalTail (fuel : Nat) (args : List Expr) : Except Yul.Exception (State × Literal) → Except Yul.Exception (State × List Literal)
    | .ok (s, arg) => 
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => cons' arg (evalArgs fuel' args s)
    | .error e => .error e

  /--
    `evalArgs` evaluates a list of arguments.
  -/
  def evalArgs (fuel : Nat) (args : List Expr) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match args with
        | [] => .ok (s, [])
        | arg :: args =>
          evalTail fuel' args (eval fuel' arg s)

  /--
    `call` executes a call of a user-defined function.
    
    Intended for use when a contract is calling one of its own functions, rather than an external contract.
  -/
  def call (fuel : Nat) (args : List Literal) (yulFunctionNameOption : Option YulFunctionName) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
        match s.sharedState.accountMap.find? s.toSharedState.executionEnv.codeOwner with
        | .none => .error .MissingContract
        | .some yulContract =>
          let fOpt : Option FunctionDefinition :=
            match yulFunctionNameOption with
              | .none => .some (FunctionDefinition.Def [] [] [yulContract.code.dispatcher])
              | .some yulFunctionName =>
                  yulContract.code.functions.lookup yulFunctionName
          match fOpt with
          | .none => .error .MissingContractFunction
          | .some f =>
            let s₁ := 👌 s.initcall f.params args
            match exec fuel' (.Block f.body) s₁ with
              | .error e => .error e
              | .ok s₂ =>
                let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
                .ok (s₃, List.map s₂.lookup! f.rets)

  /--
    `callFromCode` executes a call of a user-defined function, running `executionEnv.code` rather than the code from `s.toSharedState.executionEnv.codeOwner`.
    
    Intended for use when calling an external contract.
  -/
  def callFromCode (fuel : Nat) (args : List Literal) (yulFunctionNameOption : Option YulFunctionName) (s : State) : Except Yul.Exception (State × List Literal) :=
    match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' =>
          let fOpt : Option FunctionDefinition :=
            match yulFunctionNameOption with
              | .none => .some (FunctionDefinition.Def [] [] [s.executionEnv.code.dispatcher])
              | .some yulFunctionName =>
                  s.executionEnv.code.functions.lookup yulFunctionName
          match fOpt with
          | .none => .error .MissingContractFunction
          | .some f =>
            let s₁ := 👌 s.initcall f.params args
            match exec fuel' (.Block f.body) s₁ with
            | .error e => .error e
            | .ok s₂ =>
              let s₃ := s₂.reviveJump.overwrite? s |>.setStore s
              .ok (s₃, List.map s₂.lookup! f.rets)

  -- Safe to call `List.head!` on return values, because the compiler throws an
  -- error when coarity is > 0 in (1) and when coarity is > 1 in all other
  -- cases.

  def evalPrimCall (fuel : ℕ) (prim : PrimOp) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) => head' (primCall fuel s prim args)
    | .error e => .error e

  def evalCall (fuel : Nat) (f : YulFunctionName) : Except Yul.Exception (State × List Literal) → Except Yul.Exception (State × Literal)
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => head' (call fuel' args f s)
    | .error e => .error e

  def execPrimCall (fuel : ℕ) (prim : PrimOp) (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) => multifill' vars (primCall fuel s prim args)
    | .error e => .error e

  def execCall (fuel : Nat) (yulFunctionName : YulFunctionName) (vars : List Identifier) : Except Yul.Exception (State × List Literal) → Except Yul.Exception State
    | .ok (s, args) =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => multifill' vars (call fuel' args yulFunctionName s)
    | .error e => .error e

  /--
    `execSwitchCases` executes each case of a `switch` statement.
  -/
  def execSwitchCases (fuel : Nat) (s : State) : List (Literal × List Stmt) → Except Yul.Exception (List (Literal × (Except Yul.Exception State)))
    | [] => .ok []
    | ((val, stmts) :: cases') =>
      match fuel with
      | 0 => .error .OutOfFuel
      | .succ fuel' => 
        match exec fuel' (.Block stmts) s with
          | .error (.YulHalt s₂ v) =>
            match execSwitchCases fuel' s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .error (.YulHalt s₂ v)) :: s₃)
          | .error e => .error e
          | .ok s₂ =>
            match execSwitchCases fuel' s cases' with
            | .error e => .error e
            | .ok s₃ =>
              .ok ((val, .ok s₂) :: s₃)

  /--
    `eval` evaluates an expression.

    - calls evaluated here are assumed to have coarity 1
  -/
  def eval (fuel : Nat) (expr : Expr) (s : State) : Except Yul.Exception (State × Literal) :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
        match expr with

        -- We hit these two cases (`PrimCall` and `Call`) when evaluating:
        --
        --  1. f()                 (expression statements)
        --  2. g(f())              (calls in function arguments)
        --  3. if f() {...}        (if conditions)
        --  4. for {...} f() ...   (for conditions)
        --  5. switch f() ...      (switch conditions)

        | .Call (Sum.inl prim) args => evalPrimCall fuel' prim (reverse' (evalArgs fuel' args.reverse s))
        | .Call (Sum.inr yulFunctionName) args        =>
          evalCall fuel' yulFunctionName (reverse' (evalArgs fuel' args.reverse s))
        | .Var id             => .ok (s, s[id]!)
        | .Lit val            => .ok (s, val)

  /--
    `exec` executs a single statement.
  -/
  def exec (fuel : Nat) (stmt : Stmt) (s : State) : Except Yul.Exception State :=
    match fuel with
    | 0 => .error .OutOfFuel
    | .succ fuel' =>
      match stmt with
        | .Block [] => .ok s
        | .Block (stmt :: stmts) =>
          let s₁ := exec fuel' stmt s
          match s₁ with
            | .error e => .error e
            | .ok s₁ => exec fuel' (.Block stmts) s₁

        | .Let vars exprOption =>
            match exprOption with
              | .none => .ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars)
              | .some expr =>
                match expr with
                  | .Call (Sum.inl prim) args =>
                    execPrimCall fuel' prim vars (reverse' (evalArgs fuel' args.reverse s))
                  | .Call (Sum.inr yulFunctionName) args =>
                    execCall fuel' yulFunctionName vars (reverse' (evalArgs fuel' args.reverse s))
                  | .Var identifier => .ok (s.insert vars.head! s[identifier]!) -- It should be safe to call head! here if the Yul code is parsed correctly.
                  | .Lit literal => .ok (s.insert vars.head! literal) -- It should be safe to call head! here if the Yul code is parsed correctly.

        | .If cond body =>
          match eval fuel' cond s with
            | .error e => .error e
            | .ok (s, cond) =>
              if cond ≠ ⟨0⟩ then exec fuel' (.Block body) s else .ok s

        -- "Expressions that are also statements (i.e. at the block level) have
        -- to evaluate to zero values."
        --
        -- (https://docs.soliditylang.org/en/latest/yul.html#restrictions-on-the-grammar)
        --
        -- Thus, we cannot have literals or variables on the RHS.
        | .ExprStmtCall expr =>
             match expr with
               | .Call (Sum.inl prim) args => execPrimCall fuel' prim [] (reverse' (evalArgs fuel' args.reverse s))
               | .Call (Sum.inr f) args => execCall fuel' f [] (reverse' (evalArgs fuel' args.reverse s))
               | _ => .error .InvalidExpression -- This case should never occur because we cannot have literals or variables on the RHS, as noted above.

        | .Switch cond cases' default' =>
          match eval fuel' cond s with
            | .error e => .error e
            | .ok (s₁, cond) =>
              match execSwitchCases fuel' s₁ cases' with
              | .error e => .error e  
              | .ok branches =>
                match exec fuel' (.Block default') s₁ with
                | .error e => .error e
                | .ok s₂ =>
                  (List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) (.ok s₂) branches)

        -- A `Break` or `Continue` in the pre or post is a compiler error,
        -- so we assume it can't happen and don't modify the state in these
        -- cases. (https://docs.soliditylang.org/en/v0.8.23/yul.html#loops)
        | .For cond post body => (loop fuel' cond post body s)
        | .Continue => .ok (🔁 s)
        | .Break => .ok (💔 s)
        | .Leave => .ok (🚪 s)

  /--
    `loop` executes a for-loop.
  -/
  def loop (fuel : Nat) (cond : Expr) (post body : List Stmt) (s : State) : Except Yul.Exception State :=
    match fuel with
      | 0 => .error .OutOfFuel
      | 1 => .error .OutOfFuel
      | fuel' + 1 + 1 =>
        match eval fuel' cond (👌s) with
        | .error e => .error e
        | .ok (s₁, x) =>
          if x = ⟨0⟩
            then .ok (s₁✏️⟦s⟧?)
            else
              match exec fuel' (.Block body) s₁ with
              | .error e => .error e
              | .ok s₂ =>
                match s₂ with
                  | .OutOfFuel                      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Break _ _)      => .ok (🧟s₂✏️⟦s⟧?)
                  | .Checkpoint (.Leave _ _)      => .ok (s₂✏️⟦s⟧?)
                  | .Checkpoint (.Continue _ _)
                  | _ =>
                    match exec fuel' (.Block post) (🧟 s₂) with
                    | .error e => .error e
                    | .ok s₃ =>
                      let s₄ := s₃✏️⟦s⟧?
                      match exec fuel' (.For cond post body) s₄ with
                      | .error e => .error e
                      | .ok s₅ =>
                        let s₆ := s₅✏️⟦s⟧?
                        .ok s₆
end

def execTopLevel (fuel : Nat) (stmt : Stmt) (s : State) : State :=
  match exec fuel stmt s with
    | .error .InvalidArguments => default
    | .error .NotEncodableRLP => default
    | .error .InvalidInstruction => default
    | .error .OutOfFuel => default
    | .error .StaticModeViolation => s -- Revert, note that we do not model charging gas in the Yul semantics
    | .error .MissingContract => default
    | .error .MissingContractFunction => default -- We do not model fallback functions
    | .error .InvalidExpression => default
    | .error (.YulHalt s _) => s
    | .ok s => s

notation "🍄" => exec
notation "🌸" => eval

end Yul

end EvmYul
