import Mathlib.Data.BitVec
import Mathlib.Init
import Mathlib.Data.Finmap
import Mathlib.Data.List.Defs
import EvmYul.Data.Stack

import EvmYul.Maps.AccountMap
import EvmYul.Maps.AccountMap

import EvmYul.State.AccountOps
import EvmYul.State.ExecutionEnv
import EvmYul.State.Substate
import EvmYul.State.TransactionOps

import EvmYul.EVM.Exception
import EvmYul.EVM.Gas
import EvmYul.EVM.GasPositive
import EvmYul.EVM.GasConstants
import EvmYul.EVM.State
import EvmYul.EVM.StateOps
import EvmYul.EVM.Exception
import EvmYul.EVM.Instr
import EvmYul.EVM.PrecompiledContracts

import EvmYul.Operations
import EvmYul.Pretty
import EvmYul.SharedStateOps
import EvmYul.Semantics
import EvmYul.Wheels
import EvmYul.EllipticCurves
import EvmYul.UInt256
import EvmYul.MachineState

import Conform.Wheels

open EvmYul.DebuggingAndProfiling

namespace EvmYul

namespace EVM

def argOnNBytesOfInstr : Operation .EVM → ℕ
  -- | .Push .PUSH0 => 0 is handled as default.
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def N (pc : UInt256) (instr : Operation .EVM) := pc + ⟨1⟩ + .ofNat (argOnNBytesOfInstr instr)

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
def decode (arr : ByteArray) (pc : UInt256) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let instr ← arr.get? pc.toNat >>= EvmYul.EVM.parseInstr
  let argWidth := argOnNBytesOfInstr instr
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (EvmYul.uInt256OfByteArray (arr.extract' pc.toNat.succ (pc.toNat.succ + argWidth)), argWidth)
  )

def fetchInstr (I : EvmYul.ExecutionEnv .EVM) (pc : UInt256) :
               Except EVM.ExecutionException (Operation .EVM × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .StackUnderflow) Except.ok

partial def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 :=
  match c.get? i.toNat >>= EvmYul.EVM.parseInstr with
    | none => result
    | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = .JUMPDEST then result.push i else result)

def D_J (c : ByteArray) (i : UInt256) : Array UInt256 :=
  D_J_aux c i #[]

private def BitVec.ofFn {k} (x : Fin k → Bool) : BitVec k :=
  BitVec.ofNat k (natOfBools (Vector.ofFn x))
  where natOfBools (vec : Vector Bool k) : Nat :=
          (·.1) <| vec.toList.foldl (init := (0, 0)) λ (res, i) bit ↦ (res + 2^i * bit.toNat, i + 1)

def byteAt (μ₀ μ₁ : UInt256) : UInt256 :=
  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < ⟨32⟩
                                             then v₁.getLsbD i
                                             else false)
  EvmYul.UInt256.ofNat (BitVec.toNat vᵣ)

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

def call_termination
  (gas recipient t value : UInt256)
  (evmState : State)
:= UInt256.ofNat
    (Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas evmState.accountMap
      evmState.toMachineState evmState.substate)
        < evmState.gasAvailable

def step_termination (gasCost : Nat) (instr : Operation .EVM) (evmState : State) :=
  match instr with
  | .CREATE => UInt256.ofNat (L (evmState.gasAvailable - UInt256.ofNat gasCost).toNat) < evmState.gasAvailable
  | .CREATE2 => UInt256.ofNat (L (evmState.gasAvailable - UInt256.ofNat gasCost).toNat) < evmState.gasAvailable
  | .CALL =>
    match evmState.stack with
    | μ₀ :: μ₁ :: μ₂ :: _ =>
      call_termination μ₀ μ₁ μ₁ μ₂ evmState ∧
        Ccallgas (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁) μ₂ μ₀
          evmState.accountMap evmState.toMachineState evmState.substate < gasCost
    | _ => True
  | .CALLCODE =>
    match evmState.stack with
    | μ₀ :: μ₁ :: μ₂ :: _ =>
      call_termination μ₀ (UInt256.ofNat ↑evmState.executionEnv.codeOwner) μ₁ μ₂ evmState ∧
        Ccallgas (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner μ₂ μ₀
          evmState.accountMap evmState.toMachineState evmState.substate < gasCost
    | _ => True
  | .DELEGATECALL =>
    match evmState.stack with
    | μ₀ :: μ₁ :: _ =>
      call_termination μ₀ (UInt256.ofNat ↑evmState.executionEnv.codeOwner) μ₁ { val := 0 } evmState ∧
        Ccallgas (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner { val := 0 } μ₀
          evmState.accountMap evmState.toMachineState evmState.substate < gasCost
    | _ => True
  | .STATICCALL =>
    match evmState.stack with
    | μ₀ :: μ₁ :: _ =>
      call_termination μ₀ μ₁ μ₁ { val := 0 } evmState ∧
        Ccallgas (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁) { val := 0 } μ₀
          evmState.accountMap evmState.toMachineState evmState.substate < gasCost
    | _ => True
  | _ => True

structure StepResult (gasCost : Nat) (evmState : State) where
  state : State
  gas_le :
    gasCost ≤ evmState.gasAvailable.toNat →
    state.gasAvailable ≤ evmState.gasAvailable
  gas_lt :
    0 < gasCost →
    gasCost ≤ evmState.gasAvailable.toNat →
    state.gasAvailable < evmState.gasAvailable

structure CallResult (gasCost : Nat) (evmState : State) where
  x : UInt256
  state : State
  gas_le :
    gasCost ≤ evmState.gasAvailable.toNat →
    state.gasAvailable ≤ evmState.gasAvailable
  gas_lt :
    0 < gasCost →
    gasCost ≤ evmState.gasAvailable.toNat →
    state.gasAvailable < evmState.gasAvailable

def ExecutionResult.gasAvailable : ExecutionResult State → UInt256
  | .success s _ => s.gasAvailable
  | .revert g _ => g

structure XResult (gasBound : UInt256) where
  result : ExecutionResult State
  gas_le : result.gasAvailable ≤ gasBound

def ExecutionResult.xiGasAvailable :
    ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) →
      UInt256
  | .success (_, _, g, _) _ => g
  | .revert g _ => g

structure XiResult (g : UInt256) where
  result : ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate)
  gas_le : result.xiGasAvailable ≤ g

structure LambdaResult (g : UInt256) where
  address : AccountAddress
  createdAccounts : Batteries.RBSet AccountAddress compare
  accountMap : AccountMap .EVM
  gas : UInt256
  substate : Substate
  success : Bool
  output : ByteArray
  gas_le : gas ≤ g

structure ThetaResult (g : UInt256) where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accountMap : AccountMap .EVM
  gas : UInt256
  substate : Substate
  success : Bool
  output : ByteArray
  gas_le : gas ≤ g

structure CreateSubResult (gasLimit : Nat) where
  address : AccountAddress
  state : State
  gas : UInt256
  success : Bool
  output : ByteArray
  gas_toNat_le : gas.toNat ≤ gasLimit

structure CallSubResult (gasLimit : Nat) where
  createdAccounts : Batteries.RBSet AccountAddress compare
  accountMap : AccountMap .EVM
  gas : UInt256
  substate : Substate
  success : Bool
  output : ByteArray
  gas_le : gas ≤ UInt256.ofNat gasLimit

def ThetaResult.ofPrecompile (g : UInt256) (createdAccounts : Batteries.RBSet AccountAddress compare)
    (r : Bool × AccountMap .EVM × UInt256 × Substate × ByteArray)
    (hgas : r.2.2.1 ≤ g) : ThetaResult g :=
  { createdAccounts := createdAccounts
    accountMap := r.2.1
    gas := r.2.2.1
    substate := r.2.2.2.1
    success := r.1
    output := r.2.2.2.2
    gas_le := hgas
  }

theorem sizeOf_UInt256_le : ∀ (a b : UInt256), a < b → sizeOf a < sizeOf b := by
  intros
  simp [sizeOf, UInt256._sizeOf_1, Fin._sizeOf_1]
  simpa 

lemma UInt256.ofNat_lt_of_lt_toNat {n : Nat} {u : UInt256} (h : n < u.toNat) :
    UInt256.ofNat n < u := by
  unfold LT.lt UInt256.instLT
  simp only [UInt256.ofNat, Id.run]
  change (Fin.ofNat UInt256.size n).val < u.val.val
  simp only [Fin.val_ofNat]
  have h' : n < u.val.val := h
  rw [Nat.mod_eq_of_lt (Nat.lt_trans h' u.val.isLt)]
  exact h'

lemma UInt256.ofNat_le_of_le_toNat {n : Nat} {u : UInt256} (h : n ≤ u.toNat) :
    UInt256.ofNat n ≤ u := by
  unfold LE.le UInt256.instLE
  simp only [UInt256.ofNat, Id.run]
  change (Fin.ofNat UInt256.size n).val ≤ u.val.val
  simp only [Fin.val_ofNat]
  have hn : n < UInt256.size := Nat.lt_of_le_of_lt h u.val.isLt
  rw [Nat.mod_eq_of_lt hn]
  exact h

lemma UInt256.toNat_le_of_le_ofNat {u : UInt256} {n : Nat}
    (h : u ≤ UInt256.ofNat n) (hn : n < UInt256.size) :
    u.toNat ≤ n := by
  unfold LE.le UInt256.instLE at h
  change u.val.val ≤ (Fin.ofNat UInt256.size n).val at h
  simp only [Fin.val_ofNat] at h
  simpa [UInt256.toNat, UInt256.ofNat, Id.run, Nat.mod_eq_of_lt hn] using h

lemma UInt256.lt_of_le_of_ne' {a b : UInt256} (hle : a ≤ b) (hne : a ≠ b) :
      a < b := by
    unfold LE.le UInt256.instLE at hle
    unfold LT.lt UInt256.instLT
    apply lt_of_le_of_ne hle
    intro hv
    apply hne
    cases a
    cases b
    simp at hv
    subst hv
    rfl

lemma UInt256.toNat_sub_ofNat_of_le {a : UInt256} {n : Nat} (h : n ≤ a.toNat) :
    (a - UInt256.ofNat n).toNat = a.toNat - n := by
  have hn : n < UInt256.size := Nat.lt_of_le_of_lt h a.val.isLt
  change (UInt256.sub a (UInt256.ofNat n)).toNat = a.toNat - n
  unfold UInt256.sub UInt256.toNat UInt256.ofNat
  simp only [Id.run]
  rw [Fin.sub_val_of_le]
  · simp [Nat.mod_eq_of_lt hn]
  · change (Fin.ofNat UInt256.size n).val ≤ a.val.val
    simp [Nat.mod_eq_of_lt hn]
    exact h

lemma UInt256.sub_ofNat_lt_of_pos_le {a : UInt256} {n : Nat}
    (hpos : 0 < n) (hle : n ≤ a.toNat) :
    a - UInt256.ofNat n < a := by
  unfold LT.lt UInt256.instLT
  change (a - UInt256.ofNat n).toNat < a.toNat
  rw [UInt256.toNat_sub_ofNat_of_le hle]
  omega

lemma UInt256.sub_ofNat_le {a : UInt256} {n : Nat} (hle : n ≤ a.toNat) :
    a - UInt256.ofNat n ≤ a := by
  unfold LE.le UInt256.instLE
  change (a - UInt256.ofNat n).toNat ≤ a.toNat
  rw [UInt256.toNat_sub_ofNat_of_le hle]
  omega

lemma UInt256.le_trans' {a b c : UInt256} (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  unfold LE.le UInt256.instLE at *
  omega

lemma UInt256.le_lt_trans' {a b c : UInt256} (hab : a ≤ b) (hbc : b < c) : a < c := by
  unfold LE.le UInt256.instLE at hab
  unfold LT.lt UInt256.instLT at *
  omega

lemma UInt256.toNat_le_of_le {a b : UInt256} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  unfold LE.le UInt256.instLE at h
  exact h

lemma UInt256.zero_le (a : UInt256) : ({ val := 0 } : UInt256) ≤ a := by
  change (0 : Fin UInt256.size) ≤ a.val
  exact Nat.zero_le _

lemma UInt256.add_le_of_toNat_add_le {a b c : UInt256}
    (h : a.toNat + b.toNat ≤ c.toNat) : a + b ≤ c := by
  unfold LE.le UInt256.instLE UInt256.toNat at *
  have hsum_lt : a.val.val + b.val.val < UInt256.size := Nat.lt_of_le_of_lt h c.val.isLt
  change (UInt256.add a b).val.val ≤ c.val.val
  unfold UInt256.add
  rw [Fin.val_add]
  simp [Nat.mod_eq_of_lt hsum_lt]
  exact h

lemma UInt256.add_lt_of_toNat_add_lt {a b c : UInt256}
    (h : a.toNat + b.toNat < c.toNat) : a + b < c := by
  unfold LT.lt UInt256.instLT UInt256.toNat at *
  have hsum_lt : a.val.val + b.val.val < UInt256.size := Nat.lt_trans h c.val.isLt
  change (UInt256.add a b).val.val < c.val.val
  unfold UInt256.add
  rw [Fin.val_add]
  simp [Nat.mod_eq_of_lt hsum_lt]
  exact h

lemma UInt256.succ_bne_zero (i : Fin (UInt256.size - 1)) :
    (({ val := i.succ } : UInt256) != ({ val := 0 } : UInt256)) = true := by
  have hne : ({ val := i.succ } : UInt256) ≠ ({ val := 0 } : UInt256) := by
    intro h
    have hv := congrArg UInt256.val h
    have hvn := congrArg Fin.val hv
    simp at hvn
  unfold bne
  cases hbeq : (({ val := i.succ } : UInt256) == ({ val := 0 } : UInt256))
  · rfl
  · exact False.elim (hne (beq_iff_eq.mp hbeq))

lemma Ccallgas_lt_Ccall (t r val g σ μ A) :
    Ccallgas t r val g σ μ A < Ccall t r val g σ μ A := by
  by_cases hval : val = ({ val := 0 } : UInt256)
  · subst val
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [bne, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess]
    split
    · split <;> omega
    · rename_i hneq
      exact False.elim (hneq rfl)
  · have hbne : (val != ({ val := 0 } : UInt256)) = true := by
      simp [bne, hval]
    unfold Ccall Ccallgas Cextra Cxfer Cnew Caccess
    simp [hbne, GasConstants.Gwarmaccess, GasConstants.Gcoldaccountaccess,
      GasConstants.Gcallvalue, GasConstants.Gcallstipend, GasConstants.Gnewaccount]
    split <;> omega

lemma L_lt_of_pos {n c : Nat} (hc : 0 < c) (hle : c ≤ n) : L (n - c) < n := by
  unfold L
  omega

lemma L_le_self (n : Nat) : L n ≤ n := by
  unfold L
  omega

lemma create_refund_gas_le_charged {charged g : UInt256}
    (hg : g.toNat ≤ L charged.toNat) :
    UInt256.ofNat (charged.toNat - L charged.toNat + g.toNat) ≤ charged := by
  apply UInt256.ofNat_le_of_le_toNat
  have hL := L_le_self charged.toNat
  omega

lemma AccountAddress.ofUInt256_ofNat (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat ↑a) = a := by
  apply Fin.ext
  unfold AccountAddress.ofUInt256 UInt256.ofNat
  simp [Id.run]
  have ha256 : a.val < UInt256.size := Nat.lt_trans a.isLt (by decide)
  simp [Nat.mod_eq_of_lt ha256, Nat.mod_eq_of_lt a.isLt]

lemma precompile_ECREC_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_ECREC σ g A I).2.2.1 ≤ g := by
  unfold Ξ_ECREC
  by_cases hgas : g.toNat < 3000
  · simp [hgas, UInt256.zero_le]
  · simp [hgas, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_SHA256_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_SHA256 σ g A I).2.2.1 ≤ g := by
  unfold Ξ_SHA256
  by_cases hgas : g.toNat < 60 + 12 * ((I.calldata.size + 31) / 32)
  · simp [hgas, UInt256.zero_le]
  · cases ffi.SHA256 I.calldata <;>
      simp [hgas, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_RIP160_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_RIP160 σ g A I).2.2.1 ≤ g := by
  unfold Ξ_RIP160
  by_cases hgas : g.toNat < 600 + 120 * ((I.calldata.size + 31) / 32)
  · simp [hgas, UInt256.zero_le]
  · cases RIP160 I.calldata <;>
      simp [hgas, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_ID_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_ID σ g A I).2.2.1 ≤ g := by
  unfold Ξ_ID
  by_cases hgas : g.toNat < 15 + 3 * ((I.calldata.size + 31) / 32)
  · simp [hgas, UInt256.zero_le]
  · simp [hgas, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_EXPMOD_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_EXPMOD σ g A I).2.2.1 ≤ g := by
  unfold Ξ_EXPMOD
  by_cases hgas : g.toNat < Ξ_EXPMOD_gasRequired I
  · simp [hgas, UInt256.zero_le]
  · simp [hgas, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]

lemma precompile_BN_ADD_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_BN_ADD σ g A I).2.2.1 ≤ g := by
  unfold Ξ_BN_ADD
  by_cases hgas : g.toNat < 150
  · simp [hgas, UInt256.zero_le]
  · cases hres : BN_ADD (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
      (I.calldata.readBytes 64 32) (I.calldata.readBytes 96 32) with
    | ok o =>
      simp [hgas, hres, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
      simpa [hgas, hres] using UInt256.zero_le g

lemma precompile_BN_MUL_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_BN_MUL σ g A I).2.2.1 ≤ g := by
  unfold Ξ_BN_MUL
  by_cases hgas : g.toNat < 6000
  · simp [hgas, UInt256.zero_le]
  · cases hres : BN_MUL (I.calldata.readBytes 0 32) (I.calldata.readBytes 32 32)
      (I.calldata.readBytes 64 32) with
    | ok o =>
      simp [hgas, hres, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
      simpa [hgas, hres] using UInt256.zero_le g

lemma precompile_SNARKV_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_SNARKV σ g A I).2.2.1 ≤ g := by
  unfold Ξ_SNARKV
  by_cases hgas : g.toNat < 34000 * (I.calldata.size / 192) + 45000
  · simp [hgas, UInt256.zero_le]
  · cases hres : SNARKV I.calldata with
    | ok o =>
      simp [hgas, hres, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
      simpa [hgas, hres] using UInt256.zero_le g

lemma precompile_BLAKE2_F_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_BLAKE2_F σ g A I).2.2.1 ≤ g := by
  unfold Ξ_BLAKE2_F
  by_cases hgas : g.toNat < fromByteArrayBigEndian (I.calldata.extract 0 4)
  · simpa [hgas] using UInt256.zero_le g
  · cases hres : ffi.BLAKE2 I.calldata with
    | ok o =>
      simp [hgas, hres, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
      simpa [hgas, hres] using UInt256.zero_le g

lemma precompile_PointEval_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : (Ξ_PointEval σ g A I).2.2.1 ≤ g := by
  unfold Ξ_PointEval
  by_cases hgas : g.toNat < 50000
  · simp [hgas, UInt256.zero_le]
  · cases hres : PointEval I.calldata with
    | ok o =>
      simp [hgas, hres, UInt256.sub_ofNat_le (Nat.le_of_not_gt hgas)]
    | error e =>
      simpa [hgas, hres] using UInt256.zero_le g

lemma call_termination_of_Ccall_le {gas recipient t value : UInt256} {evmState : State}
    (h :
      Ccall (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
          evmState.toSharedState.1.accountMap evmState.toMachineState evmState.toSharedState.1.substate ≤
        evmState.gasAvailable.toNat) :
    call_termination gas recipient t value evmState := by
  unfold call_termination
  apply UInt256.ofNat_lt_of_lt_toNat
  simpa using Nat.lt_of_lt_of_le
    (Ccallgas_lt_Ccall (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient)
      value gas evmState.toSharedState.1.accountMap evmState.toMachineState evmState.toSharedState.1.substate)
    h

lemma create_step_termination_of_C_le {gasCost : Nat} {evmState : State}
    (hpos : 0 < gasCost) (hle : gasCost ≤ evmState.gasAvailable.toNat) :
    UInt256.ofNat (L (evmState.gasAvailable - UInt256.ofNat gasCost).toNat) <
      evmState.gasAvailable := by
  apply UInt256.ofNat_lt_of_lt_toNat
  rw [UInt256.toNat_sub_ofNat_of_le hle]
  exact L_lt_of_pos hpos hle

lemma C'_CREATE_pos (evmState : State) :
    0 < C' evmState Operation.CREATE := by
  simp [C', GasConstants.Gcreate]

lemma C'_CREATE2_pos (evmState : State) :
    0 < C' evmState Operation.CREATE2 := by
  simp [C', GasConstants.Gcreate]

lemma generic_step_gas_lt_of_charged {gasCost : Nat} {instr : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {evmState evmState' : State}
    (hop : instr ∉ ([Operation.CREATE, Operation.CREATE2, Operation.CALL, Operation.CALLCODE,
      Operation.DELEGATECALL, Operation.STATICCALL] : List (Operation .EVM)))
    (hpos : 0 < gasCost) (hle : gasCost ≤ evmState.gasAvailable.toNat)
    (h :
      (EvmYul.step (τ := OperationType.EVM) instr arg)
          ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost } : State) =
        .ok evmState') :
    evmState'.gasAvailable < evmState.gasAvailable := by
  have hpreserve := EvmYul.evm_step_preserves_gas_of_not_call_create hop h
  rw [hpreserve]
  exact UInt256.sub_ofNat_lt_of_pos_le hpos hle

def generic_step_result_of_charged (gasCost : Nat) (instr : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (evmState : State)
    (hop : instr ∉ ([Operation.CREATE, Operation.CREATE2, Operation.CALL, Operation.CALLCODE,
      Operation.DELEGATECALL, Operation.STATICCALL] : List (Operation .EVM))) :
    Except EVM.ExecutionException (StepResult gasCost evmState) :=
  match h :
      (EvmYul.step (τ := OperationType.EVM) instr arg)
        ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost } : State) with
  | .error e => .error e
  | .ok evmState' =>
      .ok
        { state := evmState'
          gas_le := by
            intro hle
            by_cases hpos : 0 < gasCost
            · have hlt := generic_step_gas_lt_of_charged hop hpos hle h
              unfold LT.lt UInt256.instLT at hlt
              unfold LE.le UInt256.instLE
              exact Nat.le_of_lt hlt
            · have hzero : gasCost = 0 := Nat.eq_zero_of_not_pos hpos
              subst gasCost
              have hpreserve := EvmYul.evm_step_preserves_gas_of_not_call_create hop h
              rw [hpreserve]
              change evmState.gasAvailable - UInt256.ofNat 0 ≤ evmState.gasAvailable
              exact UInt256.sub_ofNat_le (Nat.zero_le _)
          gas_lt := by
            intro hpos hle
            exact generic_step_gas_lt_of_charged hop hpos hle h
        }

def generic_step_result_of_charged_from_exec (gasCost : Nat) (instr : Operation .EVM)
    (arg : Option (UInt256 × Nat)) (evmStateBase evmStateExec : State)
    (hop : instr ∉ ([Operation.CREATE, Operation.CREATE2, Operation.CALL, Operation.CALLCODE,
      Operation.DELEGATECALL, Operation.STATICCALL] : List (Operation .EVM))) :
    Except EVM.ExecutionException (StepResult gasCost evmStateBase) :=
  match h :
      (EvmYul.step (τ := OperationType.EVM) instr arg)
        ({ evmStateExec with
            gasAvailable := evmStateBase.gasAvailable - UInt256.ofNat gasCost
        } : State) with
  | .error e => .error e
  | .ok evmState' =>
      .ok
        { state := evmState'
          gas_le := by
            intro hle
            by_cases hpos : 0 < gasCost
            · have hpreserve := EvmYul.evm_step_preserves_gas_of_not_call_create hop h
              rw [hpreserve]
              exact UInt256.sub_ofNat_le hle
            · have hzero : gasCost = 0 := Nat.eq_zero_of_not_pos hpos
              subst gasCost
              have hpreserve := EvmYul.evm_step_preserves_gas_of_not_call_create hop h
              rw [hpreserve]
              change evmStateBase.gasAvailable - UInt256.ofNat 0 ≤ evmStateBase.gasAvailable
              exact UInt256.sub_ofNat_le (Nat.zero_le _)
          gas_lt := by
            intro hpos hle
            have hpreserve := EvmYul.evm_step_preserves_gas_of_not_call_create hop h
            rw [hpreserve]
            exact UInt256.sub_ofNat_lt_of_pos_le hpos hle
        }

def X_W (w : Operation .EVM) (s : Stack UInt256) : Bool :=
  w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
  (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)

def X_belongs (o : Option UInt256) (l : Array UInt256) : Bool :=
  match o with
    | none => false
    | some n => l.contains n

def X_notIn (o : Option UInt256) (l : Array UInt256) : Bool := not (X_belongs o l)

def X_Z (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) :=
  if δ w = none then
    .error .InvalidInstruction
  else if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow
  else
    let cost₁ := memoryExpansionCost evmState w
    if evmState.gasAvailable.toNat < cost₁ then
      .error .OutOfGass
    else
      let gasAvailable := evmState.gasAvailable - .ofNat cost₁
      let evmState := { evmState with gasAvailable := gasAvailable}
      let cost₂ := C' evmState w
      if evmState.gasAvailable.toNat < cost₂ then
        .error .OutOfGass
      else
        let invalidJump := X_notIn evmState.stack[0]? validJumps
        if w = .JUMP ∧ invalidJump then
          .error .BadJumpDestination
        else if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
          .error .BadJumpDestination
        else if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
          .error .InvalidMemoryAccess
        else if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
          .error .StackOverflow
        else if (¬ evmState.executionEnv.perm) ∧ X_W w evmState.stack then
          .error .StaticModeViolation
        else if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
          .error .OutOfGass
        else if w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩ then
          .error .OutOfGass
        else
          .ok (evmState, cost₂)

theorem X_Z_step_termination {validJumps : Array UInt256} {w : Operation .EVM}
    {evmState evmState' : State} {cost : ℕ}
    (h : X_Z validJumps w evmState = .ok (evmState', cost)) :
    step_termination cost w evmState' := by
  unfold X_Z at h
  by_cases hδ : δ w = none
  · simp [hδ] at h
  simp [hδ] at h
  by_cases hstack : evmState.stack.length < (δ w).getD 0
  · simp [hstack] at h
  simp [hstack] at h
  by_cases hcost₁ : evmState.gasAvailable.toNat < memoryExpansionCost evmState w
  · simp [hcost₁] at h
  simp [hcost₁] at h
  set evmState₁ : State := ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w) } : State) with hev₁
  by_cases hcost₂ : (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat < C' evmState₁ w
  · simp [hcost₂] at h
  simp [hcost₂] at h
  by_cases hjump : w = Operation.JUMP ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjump] at h
  simp [hjump] at h
  by_cases hjumpi : w = Operation.JUMPI ∧ evmState.stack[1]? ≠ some { val := 0 } ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjumpi] at h
  simp [hjumpi] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        evmState.returnData.size <
          (evmState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat + (evmState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
  · simp [hreturndata.1, hreturndata.2] at h
  simp [hreturndata] at h
  by_cases hoverflow : 1024 < List.length evmState.stack - (δ w).getD 0 + (α w).getD 0
  · simp [hoverflow] at h
  simp [hoverflow] at h
  by_cases hstatic : evmState.executionEnv.perm = false ∧ X_W w evmState.stack = true
  · simp [hstatic] at h
  simp [hstatic] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat ≤
          GasConstants.Gcallstipend
  · have hsstoreCost :
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.SSTORE)).toNat ≤
          GasConstants.Gcallstipend := by
        simpa [hsstore.1] using hsstore.2
    simp [hsstore.1, hsstoreCost] at h
  simp [hsstore] at h
  by_cases hcreate : w.isCreate = true ∧ { val := 49152 } < evmState.stack[2]?.getD { val := 0 }
  · simp [hcreate] at h
  simp [hcreate] at h
  rcases h with ⟨hstate, hcost⟩
  subst evmState'
  subst cost
  subst evmState₁
  cases w <;> rename_i a <;> cases a <;> simp [step_termination] at *
  case neg.System.CREATE =>
    exact create_step_termination_of_C_le
      (gasCost := C' ({ evmState with gasAvailable :=
        (evmState.gasAvailable - UInt256.ofNat
          (memoryExpansionCost evmState Operation.CREATE)) } : State) Operation.CREATE)
      (evmState := { evmState with gasAvailable :=
        (evmState.gasAvailable - UInt256.ofNat
          (memoryExpansionCost evmState Operation.CREATE)) })
      (C'_CREATE_pos _)
      (by simpa using hcost₂)
  case neg.System.CREATE2 =>
    exact create_step_termination_of_C_le
      (gasCost := C' ({ evmState with gasAvailable :=
        (evmState.gasAvailable - UInt256.ofNat
          (memoryExpansionCost evmState Operation.CREATE2)) } : State) Operation.CREATE2)
      (evmState := { evmState with gasAvailable :=
        (evmState.gasAvailable - UInt256.ofNat
          (memoryExpansionCost evmState Operation.CREATE2)) })
      (C'_CREATE2_pos _)
      (by simpa using hcost₂)
  case neg.System.CALL =>
    cases hstk : evmState.stack with
    | nil => simp
    | cons μ₀ stack =>
      cases stack with
      | nil => simp
      | cons μ₁ stack =>
        cases stack with
        | nil => simp
        | cons μ₂ stack =>
          constructor
          · apply call_termination_of_Ccall_le
            simpa [C', hstk] using hcost₂
          · simpa [C', hstk] using
              Ccallgas_lt_Ccall (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁)
                μ₂ μ₀ evmState.toSharedState.1.accountMap
                { gasAvailable :=
                    evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.CALL)
                  activeWords := evmState.activeWords
                  memory := evmState.memory
                  returnData := evmState.returnData
                  H_return := evmState.H_return }
                evmState.toSharedState.1.substate
  case neg.System.CALLCODE =>
    cases hstk : evmState.stack with
    | nil => simp
    | cons μ₀ stack =>
      cases stack with
      | nil => simp
      | cons μ₁ stack =>
        cases stack with
        | nil => simp
        | cons μ₂ stack =>
          constructor
          · apply call_termination_of_Ccall_le
            simpa [C', hstk, AccountAddress.ofUInt256_ofNat] using hcost₂
          · simpa [C', hstk, AccountAddress.ofUInt256_ofNat] using
              Ccallgas_lt_Ccall (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner
                μ₂ μ₀ evmState.toSharedState.1.accountMap
                { gasAvailable :=
                    evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.CALLCODE)
                  activeWords := evmState.activeWords
                  memory := evmState.memory
                  returnData := evmState.returnData
                  H_return := evmState.H_return }
                evmState.toSharedState.1.substate
  case neg.System.DELEGATECALL =>
    cases hstk : evmState.stack with
    | nil => simp
    | cons μ₀ stack =>
      cases stack with
      | nil => simp
      | cons μ₁ stack =>
        constructor
        · apply call_termination_of_Ccall_le
          simpa [C', hstk, AccountAddress.ofUInt256_ofNat] using hcost₂
        · simpa [C', hstk, AccountAddress.ofUInt256_ofNat] using
            Ccallgas_lt_Ccall (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner
              ({ val := 0 } : UInt256) μ₀ evmState.toSharedState.1.accountMap
              { gasAvailable :=
                  evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.DELEGATECALL)
                activeWords := evmState.activeWords
                memory := evmState.memory
                returnData := evmState.returnData
                H_return := evmState.H_return }
              evmState.toSharedState.1.substate
  case neg.System.STATICCALL =>
    cases hstk : evmState.stack with
    | nil => simp
    | cons μ₀ stack =>
      cases stack with
      | nil => simp
      | cons μ₁ stack =>
        constructor
        · apply call_termination_of_Ccall_le
          simpa [C', hstk] using hcost₂
        · simpa [C', hstk] using
            Ccallgas_lt_Ccall (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁)
              ({ val := 0 } : UInt256) μ₀ evmState.toSharedState.1.accountMap
              { gasAvailable :=
                  evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.STATICCALL)
                activeWords := evmState.activeWords
                memory := evmState.memory
                returnData := evmState.returnData
                H_return := evmState.H_return }
              evmState.toSharedState.1.substate

theorem X_Z_cost_le {validJumps : Array UInt256} {w : Operation .EVM}
    {evmState evmState' : State} {cost : ℕ}
    (h : X_Z validJumps w evmState = .ok (evmState', cost)) :
    cost ≤ evmState'.gasAvailable.toNat := by
  unfold X_Z at h
  by_cases hδ : δ w = none
  · simp [hδ] at h
  simp [hδ] at h
  by_cases hstack : evmState.stack.length < (δ w).getD 0
  · simp [hstack] at h
  simp [hstack] at h
  by_cases hcost₁ : evmState.gasAvailable.toNat < memoryExpansionCost evmState w
  · simp [hcost₁] at h
  simp [hcost₁] at h
  set evmState₁ : State := ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w) } : State) with hev₁
  by_cases hcost₂ : (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat < C' evmState₁ w
  · simp [hcost₂] at h
  simp [hcost₂] at h
  by_cases hjump : w = Operation.JUMP ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjump] at h
  simp [hjump] at h
  by_cases hjumpi : w = Operation.JUMPI ∧ evmState.stack[1]? ≠ some { val := 0 } ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjumpi] at h
  simp [hjumpi] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        evmState.returnData.size <
          (evmState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat + (evmState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
  · simp [hreturndata.1, hreturndata.2] at h
  simp [hreturndata] at h
  by_cases hoverflow : 1024 < List.length evmState.stack - (δ w).getD 0 + (α w).getD 0
  · simp [hoverflow] at h
  simp [hoverflow] at h
  by_cases hstatic : evmState.executionEnv.perm = false ∧ X_W w evmState.stack = true
  · simp [hstatic] at h
  simp [hstatic] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat ≤
          GasConstants.Gcallstipend
  · have hsstoreCost :
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.SSTORE)).toNat ≤
          GasConstants.Gcallstipend := by
        simpa [hsstore.1] using hsstore.2
    simp [hsstore.1, hsstoreCost] at h
  simp [hsstore] at h
  by_cases hcreate : w.isCreate = true ∧ { val := 49152 } < evmState.stack[2]?.getD { val := 0 }
  · simp [hcreate] at h
  simp [hcreate] at h
  rcases h with ⟨hstate, hcost⟩
  subst evmState'
  subst cost
  subst evmState₁
  exact Nat.le_of_not_gt hcost₂

theorem X_Z_cost_pos_of_continues {validJumps : Array UInt256} {w : Operation .EVM}
    {evmState evmState' : State} {cost : ℕ}
    (h : X_Z validJumps w evmState = .ok (evmState', cost))
    (hcont : ContinuesAfterXStep w) :
    0 < cost := by
  unfold X_Z at h
  by_cases hδ : δ w = none
  · simp [hδ] at h
  simp [hδ] at h
  by_cases hstack : evmState.stack.length < (δ w).getD 0
  · simp [hstack] at h
  simp [hstack] at h
  by_cases hcost₁ : evmState.gasAvailable.toNat < memoryExpansionCost evmState w
  · simp [hcost₁] at h
  simp [hcost₁] at h
  set evmState₁ : State := ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w) } : State) with hev₁
  by_cases hcost₂ : (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat < C' evmState₁ w
  · simp [hcost₂] at h
  simp [hcost₂] at h
  by_cases hjump : w = Operation.JUMP ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjump] at h
  simp [hjump] at h
  by_cases hjumpi : w = Operation.JUMPI ∧ evmState.stack[1]? ≠ some { val := 0 } ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjumpi] at h
  simp [hjumpi] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        evmState.returnData.size <
          (evmState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat + (evmState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
  · simp [hreturndata.1, hreturndata.2] at h
  simp [hreturndata] at h
  by_cases hoverflow : 1024 < List.length evmState.stack - (δ w).getD 0 + (α w).getD 0
  · simp [hoverflow] at h
  simp [hoverflow] at h
  by_cases hstatic : evmState.executionEnv.perm = false ∧ X_W w evmState.stack = true
  · simp [hstatic] at h
  simp [hstatic] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat ≤
          GasConstants.Gcallstipend
  · have hsstoreCost :
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.SSTORE)).toNat ≤
          GasConstants.Gcallstipend := by
        simpa [hsstore.1] using hsstore.2
    simp [hsstore.1, hsstoreCost] at h
  simp [hsstore] at h
  by_cases hcreate : w.isCreate = true ∧ { val := 49152 } < evmState.stack[2]?.getD { val := 0 }
  · simp [hcreate] at h
  simp [hcreate] at h
  rcases h with ⟨hstate, hcost⟩
  subst evmState'
  subst cost
  subst evmState₁
  exact C'_pos_of_continuesAfterXStep _ hcont

theorem X_Z_state_gas_le {validJumps : Array UInt256} {w : Operation .EVM}
    {evmState evmState' : State} {cost : ℕ}
    (h : X_Z validJumps w evmState = .ok (evmState', cost)) :
    evmState'.gasAvailable ≤ evmState.gasAvailable := by
  unfold X_Z at h
  by_cases hδ : δ w = none
  · simp [hδ] at h
  simp [hδ] at h
  by_cases hstack : evmState.stack.length < (δ w).getD 0
  · simp [hstack] at h
  simp [hstack] at h
  by_cases hcost₁ : evmState.gasAvailable.toNat < memoryExpansionCost evmState w
  · simp [hcost₁] at h
  simp [hcost₁] at h
  set evmState₁ : State := ({ evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w) } : State) with hev₁
  by_cases hcost₂ : (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat < C' evmState₁ w
  · simp [hcost₂] at h
  simp [hcost₂] at h
  by_cases hjump : w = Operation.JUMP ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjump] at h
  simp [hjump] at h
  by_cases hjumpi : w = Operation.JUMPI ∧ evmState.stack[1]? ≠ some { val := 0 } ∧ X_notIn evmState.stack[0]? validJumps = true
  · simp [hjumpi] at h
  simp [hjumpi] at h
  by_cases hreturndata :
      w = Operation.RETURNDATACOPY ∧
        evmState.returnData.size <
          (evmState.stack[1]?.getD (⟨0⟩ : UInt256)).toNat + (evmState.stack[2]?.getD (⟨0⟩ : UInt256)).toNat
  · simp [hreturndata.1, hreturndata.2] at h
  simp [hreturndata] at h
  by_cases hoverflow : 1024 < List.length evmState.stack - (δ w).getD 0 + (α w).getD 0
  · simp [hoverflow] at h
  simp [hoverflow] at h
  by_cases hstatic : evmState.executionEnv.perm = false ∧ X_W w evmState.stack = true
  · simp [hstatic] at h
  simp [hstatic] at h
  by_cases hsstore :
      w = Operation.SSTORE ∧
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState w)).toNat ≤
          GasConstants.Gcallstipend
  · have hsstoreCost :
        (evmState.gasAvailable - UInt256.ofNat (memoryExpansionCost evmState Operation.SSTORE)).toNat ≤
          GasConstants.Gcallstipend := by
        simpa [hsstore.1] using hsstore.2
    simp [hsstore.1, hsstoreCost] at h
  simp [hsstore] at h
  by_cases hcreate : w.isCreate = true ∧ { val := 49152 } < evmState.stack[2]?.getD { val := 0 }
  · simp [hcreate] at h
  simp [hcreate] at h
  rcases h with ⟨hstate, hcost⟩
  subst evmState'
  subst cost
  subst evmState₁
  exact UInt256.sub_ofNat_le (Nat.le_of_not_gt hcost₁)

mutual

def call
  (gasCost : Nat)
  (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (evmState : State)
  (hterm : call_termination gas recipient t value evmState)
  (hcallgas_lt :
    Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
      evmState.accountMap evmState.toMachineState evmState.substate < gasCost)
    :
  Except EVM.ExecutionException (CallResult gasCost evmState)
:= do
      let _htermUsed := hterm
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := evmState.executionEnv.codeOwner
      let σ := evmState.accountMap
      let Iₑ := evmState.executionEnv.depth
      let callgas := Ccallgas t recipient value gas σ evmState.toMachineState evmState.substate
      let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let i := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
      let A' := evmState.addAccessedAccount t |>.substate
      let callSubResult : CallSubResult callgas ← do
        if value ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
          let resultOfΘ ←
            ΘWithGas
              blobVersionedHashes
              (createdAccounts := evmState.createdAccounts)
              (genesisBlockHeader := evmState.genesisBlockHeader)
              (blocks := evmState.blocks)
              (σ  := σ)                                     -- σ in  Θ(σ, ..)
              (σ₀ := evmState.σ₀)
              (A  := A')                                    -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := evmState.executionEnv.sender)          -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute .EVM σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat evmState.executionEnv.gasPrice) -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := evmState.executionEnv.header)
              (w  := permission)                            -- I_w in Θ(.., I_W)
          pure
            { createdAccounts := resultOfΘ.createdAccounts
              accountMap := resultOfΘ.accountMap
              gas := resultOfΘ.gas
              substate := resultOfΘ.substate
              success := resultOfΘ.success
              output := resultOfΘ.output
              gas_le := resultOfΘ.gas_le
            : CallSubResult callgas }
        else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
          .ok
            { createdAccounts := evmState.createdAccounts
              accountMap := evmState.toState.accountMap
              gas := .ofNat callgas
              substate := A'
              success := false
              output := .empty
              gas_le := le_rfl
            : CallSubResult callgas }
      let cA := callSubResult.createdAccounts
      let σ' := callSubResult.accountMap
      let g' := callSubResult.gas
      let A' := callSubResult.substate
      let z := callSubResult.success
      let o := callSubResult.output
      have hg'_le_ofNat : g' ≤ UInt256.ofNat callgas := callSubResult.gas_le
      have hcallgas_lt_local : callgas < gasCost := by
        simpa [callgas, σ] using hcallgas_lt
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (.ofNat o.size)

      let μ'ₘ := writeBytes o 0 evmState.toMachineState outOffset.toNat n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      let μ'_g := μ'ₘ.gasAvailable + g' -- Ccall is subtracted in X as part of C

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.find? evmState.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
      let μ'incomplete : MachineState :=
        { μ'ₘ with
            returnData   := μ'ₒ
            gasAvailable := μ'_g
            activeWords :=
              let m : ℕ:= MachineState.M evmState.toMachineState.activeWords.toNat inOffset.toNat inSize.toNat
              .ofNat <| MachineState.M m outOffset.toNat outSize.toNat

        }

      let result : State := { evmState with accountMap := σ', substate := A', createdAccounts := cA }
      let result := {
        result with toMachineState := μ'incomplete
      }
      .ok
        { x := x
          state := result
          gas_le := by
            intro hle
            have hg'_toNat_le : g'.toNat ≤ callgas :=
              Nat.le_trans (UInt256.toNat_le_of_le hg'_le_ofNat) (UInt256.toNat_ofNat_le callgas)
            simpa [writeBytes] using
              UInt256.add_le_of_toNat_add_le (a := evmState.gasAvailable) (b := g') (by
                rw [UInt256.toNat_sub_ofNat_of_le hle]
                omega)
          gas_lt := by
            intro hpos hle
            have hg'_toNat_le : g'.toNat ≤ callgas :=
              Nat.le_trans (UInt256.toNat_le_of_le hg'_le_ofNat) (UInt256.toNat_ofNat_le callgas)
            simpa [writeBytes] using
              UInt256.add_lt_of_toNat_add_lt (a := evmState.gasAvailable) (b := g') (by
                rw [UInt256.toNat_sub_ofNat_of_le hle]
                omega)
        }
      termination_by (evmState.gasAvailable, 0)
      decreasing_by 
        apply Prod.Lex.left 
        simp [call_termination] at hterm
        apply sizeOf_UInt256_le
        assumption

def step (gasCost : ℕ) (instr : Operation .EVM) (arg : Option (UInt256 × Nat) := .none) (evmState : State)
  (hterm : step_termination gasCost instr evmState)
  : Except EVM.ExecutionException (StepResult gasCost evmState)
:=
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    -- let (instr, arg) ←
    --   match instr with
    --     | .none => fetchInstr evmState.toState.executionEnv evmState.pc
    --     | .some (instr, arg) => pure (instr, arg)
    let evmStateBase := evmState
    let evmState := { evmState with execLength := evmState.execLength + 1 }
    match instr with
      | .CREATE =>
        let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
        match evmState.stack.pop3 with
          | some ⟨stack, μ₀, μ₁, μ₂⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

            let createResult : CreateSubResult (L evmState.gasAvailable.toNat)
              :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then
                { address := default
                  state := evmState
                  gas := .ofNat (L evmState.gasAvailable.toNat)
                  success := False
                  output := .empty
                  gas_toNat_le := by
                    exact UInt256.toNat_ofNat_le _ }
              else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  LambdaWithGas
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok Λ =>
                    { address := Λ.address
                      state := { evmState with
                        accountMap := Λ.accountMap
                        substate := Λ.substate
                        createdAccounts := Λ.createdAccounts
                      }
                      gas := Λ.gas
                      success := Λ.success
                      output := Λ.output
                      gas_toNat_le := by
                        have hLlt : L evmState.gasAvailable.toNat < UInt256.size :=
                          Nat.lt_of_le_of_lt (L_le_self _) evmState.gasAvailable.val.isLt
                        exact UInt256.toNat_le_of_le_ofNat Λ.gas_le hLlt
                    }
                  | _ =>
                    { address := 0
                      state := {evmState with accountMap := ∅}
                      gas := ⟨0⟩
                      success := False
                      output := .empty
                      gas_toNat_le := Nat.zero_le _ }
              else
                { address := 0
                  state := evmState
                  gas := .ofNat (L evmState.gasAvailable.toNat)
                  success := False
                  output := .empty
                  gas_toNat_le := by
                    exact UInt256.toNat_ofNat_le _ }
            let a := createResult.address
            let evmState' := createResult.state
            let g' := createResult.gas
            let z := createResult.success
            let o := createResult.output
            have hg'_le : g'.toNat ≤ L evmState.gasAvailable.toNat := createResult.gas_toNat_le
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L (evmState.gasAvailable.toNat) then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                  activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                  returnData := newReturnData
                  gasAvailable :=
                    .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok
              { state := evmState'.replaceStackAndIncrPC (stack.push x)
                gas_le := by
                  intro hle
                  have hfinal_le_charged :
                      UInt256.ofNat (evmState.gasAvailable.toNat - L evmState.gasAvailable.toNat + g'.toNat) ≤
                        evmState.gasAvailable :=
                    create_refund_gas_le_charged hg'_le
                  have hcharged_le := UInt256.sub_ofNat_le hle
                  exact
                    (by
                      simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                        UInt256.le_trans' hfinal_le_charged hcharged_le)
                gas_lt := by
                  intro hpos hle
                  have hfinal_le_charged :
                      UInt256.ofNat (evmState.gasAvailable.toNat - L evmState.gasAvailable.toNat + g'.toNat) ≤
                        evmState.gasAvailable :=
                    create_refund_gas_le_charged hg'_le
                  have hcharged_lt := UInt256.sub_ofNat_lt_of_pos_le hpos hle
                  exact
                    (by
                      simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                        UInt256.le_lt_trans' hfinal_le_charged hcharged_lt)
              }
          | _ =>
          .error .StackUnderflow
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        let evmState := {evmState with gasAvailable := evmState.gasAvailable - UInt256.ofNat gasCost}
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := EvmYul.UInt256.toByteArray μ₃
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.find? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
            let createResult : CreateSubResult (L evmState.gasAvailable.toNat) :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then
                { address := default
                  state := evmState
                  gas := .ofNat (L evmState.gasAvailable.toNat)
                  success := False
                  output := .empty
                  gas_toNat_le := by
                    exact UInt256.toNat_ofNat_le _ }
              else
              if μ₀ ≤ (σ.find? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  LambdaWithGas
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok Λ =>
                    { address := Λ.address
                      state := ({ evmState with
                        accountMap := Λ.accountMap
                        substate := Λ.substate
                        createdAccounts := Λ.createdAccounts
                      } : State)
                      gas := Λ.gas
                      success := Λ.success
                      output := Λ.output
                      gas_toNat_le := by
                        have hLlt : L evmState.gasAvailable.toNat < UInt256.size :=
                          Nat.lt_of_le_of_lt (L_le_self _) evmState.gasAvailable.val.isLt
                        exact UInt256.toNat_le_of_le_ofNat Λ.gas_le hLlt
                    }
                  | _ =>
                    { address := 0
                      state := {evmState with accountMap := ∅}
                      gas := ⟨0⟩
                      success := False
                      output := .empty
                      gas_toNat_le := Nat.zero_le _ }
              else
                { address := 0
                  state := evmState
                  gas := .ofNat (L evmState.gasAvailable.toNat)
                  success := False
                  output := .empty
                  gas_toNat_le := by
                    exact UInt256.toNat_ofNat_le _ }
            let a := createResult.address
            let evmState' := createResult.state
            let g' := createResult.gas
            let z := createResult.success
            let o := createResult.output
            have hg'_le : g'.toNat ≤ L evmState.gasAvailable.toNat := createResult.gas_toNat_le
            let x : UInt256 :=
              let balance := σ.find? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L evmState.gasAvailable.toNat then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                returnData := newReturnData
                gasAvailable := .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok
              { state := evmState'.replaceStackAndIncrPC (stack.push x)
                gas_le := by
                  intro hle
                  have hfinal_le_charged :
                      UInt256.ofNat (evmState.gasAvailable.toNat - L evmState.gasAvailable.toNat + g'.toNat) ≤
                        evmState.gasAvailable :=
                    create_refund_gas_le_charged hg'_le
                  have hcharged_le := UInt256.sub_ofNat_le hle
                  exact
                    (by
                      simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                        UInt256.le_trans' hfinal_le_charged hcharged_le)
                gas_lt := by
                  intro hpos hle
                  have hfinal_le_charged :
                      UInt256.ofNat (evmState.gasAvailable.toNat - L evmState.gasAvailable.toNat + g'.toNat) ≤
                        evmState.gasAvailable :=
                    create_refund_gas_le_charged hg'_le
                  have hcharged_lt := UInt256.sub_ofNat_lt_of_pos_le hpos hle
                  exact
                    (by
                      simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                        UInt256.le_lt_trans' hfinal_le_charged hcharged_lt)
              }
          | _ =>
          .error .StackUnderflow
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        -- let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        match hstack : evmState.stack with
        | μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: (stack : Stack UInt256) =>
          let hcallterm : call_termination μ₀ μ₁ μ₁ μ₂ evmState := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.1
          let hcallgas_lt :
              Ccallgas (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁) μ₂ μ₀
                evmState.accountMap evmState.toMachineState evmState.substate < gasCost := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.2
          let callResult ←
            call gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState hcallterm hcallgas_lt
          let μ'ₛ := stack.push callResult.x -- μ′s[0] ≡ x
          let evmState' := callResult.state.replaceStackAndIncrPC μ'ₛ
          .ok
            { state := evmState'
              gas_le := by
                intro hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_le hle
              gas_lt := by
                intro hpos hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_lt hpos hle
            }
        | _ => .error .StackUnderflow
      | .CALLCODE =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        match hstack : evmState.stack with
        | μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: (stack : Stack UInt256) =>
          let hcallterm : call_termination μ₀ (UInt256.ofNat ↑evmState.executionEnv.codeOwner) μ₁ μ₂ evmState := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.1
          let hcallgas_lt :
              Ccallgas (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner μ₂ μ₀
                evmState.accountMap evmState.toMachineState evmState.substate < gasCost := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.2
          let callResult ←
            call gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
              hcallterm
              (by simpa [AccountAddress.ofUInt256_ofNat] using hcallgas_lt)
          let μ'ₛ := stack.push callResult.x -- μ′s[0] ≡ x
          let evmState' := callResult.state.replaceStackAndIncrPC μ'ₛ
          .ok
            { state := evmState'
              gas_le := by
                intro hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_le hle
              gas_lt := by
                intro hpos hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_lt hpos hle
            }
        | _ => .error .StackUnderflow
      | .DELEGATECALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        match hstack : evmState.stack with
        | μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: (stack : Stack UInt256) =>
          let hcallterm : call_termination μ₀ (UInt256.ofNat ↑evmState.executionEnv.codeOwner) μ₁ { val := 0 } evmState := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.1
          let hcallgas_lt :
              Ccallgas (AccountAddress.ofUInt256 μ₁) evmState.executionEnv.codeOwner { val := 0 } μ₀
                evmState.accountMap evmState.toMachineState evmState.substate < gasCost := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.2
          let callResult ←
            call gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
              hcallterm
              (by simpa [AccountAddress.ofUInt256_ofNat] using hcallgas_lt)
          let μ'ₛ := stack.push callResult.x -- μ′s[0] ≡ x
          let evmState' := callResult.state.replaceStackAndIncrPC μ'ₛ
          .ok
            { state := evmState'
              gas_le := by
                intro hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_le hle
              gas_lt := by
                intro hpos hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_lt hpos hle
            }
        | _ => .error .StackUnderflow
      | .STATICCALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize

        match hstack : evmState.stack with
        | μ₀ :: μ₁ :: μ₂ :: μ₃ :: μ₄ :: μ₅ :: μ₆ :: (stack : Stack UInt256) =>
          let hcallterm : call_termination μ₀ μ₁ μ₁ { val := 0 } evmState := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.1
          let hcallgas_lt :
              Ccallgas (AccountAddress.ofUInt256 μ₁) (AccountAddress.ofUInt256 μ₁) { val := 0 } μ₀
                evmState.accountMap evmState.toMachineState evmState.substate < gasCost := by
            simp [step_termination] at hterm
            simp [evmState] at *
            rw [hstack] at hterm
            simp [*] at hterm
            exact hterm.2
          let callResult ←
            call gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState hcallterm hcallgas_lt
          let μ'ₛ := stack.push callResult.x -- μ′s[0] ≡ x
          let evmState' := callResult.state.replaceStackAndIncrPC μ'ₛ
          .ok
            { state := evmState'
              gas_le := by
                intro hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_le hle
              gas_lt := by
                intro hpos hle
                simpa [EVM.State.replaceStackAndIncrPC, EVM.State.incrPC] using
                  callResult.gas_lt hpos hle
            }
        | _ => .error .StackUnderflow
      | .StopArith op =>
        generic_step_result_of_charged_from_exec gasCost (.StopArith op) arg evmStateBase evmState (by simp)
      | .CompBit op =>
        generic_step_result_of_charged_from_exec gasCost (.CompBit op) arg evmStateBase evmState (by simp)
      | .Keccak op =>
        generic_step_result_of_charged_from_exec gasCost (.Keccak op) arg evmStateBase evmState (by simp)
      | .Env op =>
        generic_step_result_of_charged_from_exec gasCost (.Env op) arg evmStateBase evmState (by simp)
      | .Block op =>
        generic_step_result_of_charged_from_exec gasCost (.Block op) arg evmStateBase evmState (by simp)
      | .StackMemFlow op =>
        generic_step_result_of_charged_from_exec gasCost (.StackMemFlow op) arg evmStateBase evmState (by simp)
      | .Push op =>
        generic_step_result_of_charged_from_exec gasCost (.Push op) arg evmStateBase evmState (by simp)
      | .Dup op =>
        generic_step_result_of_charged_from_exec gasCost (.Dup op) arg evmStateBase evmState (by simp)
      | .Exchange op =>
        generic_step_result_of_charged_from_exec gasCost (.Exchange op) arg evmStateBase evmState (by simp)
      | .Log op =>
        generic_step_result_of_charged_from_exec gasCost (.Log op) arg evmStateBase evmState (by simp)
      | .System .RETURN =>
        generic_step_result_of_charged_from_exec gasCost Operation.RETURN arg evmStateBase evmState (by simp)
      | .System .REVERT =>
        generic_step_result_of_charged_from_exec gasCost Operation.REVERT arg evmStateBase evmState (by simp)
      | .System .INVALID =>
        generic_step_result_of_charged_from_exec gasCost Operation.INVALID arg evmStateBase evmState (by simp)
      | .System .SELFDESTRUCT =>
        generic_step_result_of_charged_from_exec gasCost (.System .SELFDESTRUCT) arg evmStateBase evmState (by simp)
      termination_by (evmState.gasAvailable, 1)
      decreasing_by
        · 
          apply Prod.Lex.left
          apply sizeOf_UInt256_le
          simp [step_termination] at hterm; assumption
        · 
          apply Prod.Lex.left
          apply sizeOf_UInt256_le
          simp [step_termination] at hterm; assumption
        · 
          apply Prod.Lex.right
          simp
        · 
          apply Prod.Lex.right
          simp
        · 
          apply Prod.Lex.right
          simp
        · 
          apply Prod.Lex.right
          simp

/--
  Iterative progression of `step`
-/
def XWithGasBound (validJumps : Array UInt256) (gasBound : UInt256) (evmState : State)
  (hgasBound : evmState.gasAvailable ≤ gasBound)
  : Except EVM.ExecutionException (XResult gasBound)
:= do
      let I_b := evmState.toState.executionEnv.code
      let (w, args) := decode I_b evmState.pc |>.getD (.STOP, .none)
      let H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          some <| μ.H_return
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none
      match hz : X_Z validJumps w evmState with
        | .error e =>
          .error e
        | some (evmState', cost₂) =>
          have hzg_le := X_Z_state_gas_le hz
          let hstepterm : step_termination cost₂ w evmState' := by
            exact X_Z_step_termination hz
          let stepResult ← step cost₂ w args evmState' hstepterm
          let evmState'' := stepResult.state
          have hcostle : cost₂ ≤ evmState'.gasAvailable.toNat := X_Z_cost_le hz
          have hstep_le : evmState''.gasAvailable ≤ evmState'.gasAvailable := stepResult.gas_le hcostle
          -- Maybe we should restructure in a way such that it is more meaningful to compute
          -- gas independently, but the model has not been set up thusly and it seems
          -- that neither really was the YP.
          -- Similarly, we cannot reach a situation in which the stack elements are not available
          -- on the stack because this is guarded above. As such, `C` can be pure here.
          match hH : H evmState''.toMachineState w with -- The YP does this in a weird way.
            | none =>
              have hcont : ContinuesAfterXStep w := by
                unfold ContinuesAfterXStep
                constructor
                · intro hδ
                  unfold X_Z at hz
                  simp [hδ] at hz
                · intro hw
                  simp at hw
                  rcases hw with hw | hw | hw | hw
                  · subst w
                    simp [H] at hH
                  · subst w
                    simp [H] at hH
                  · subst w
                    simp [H] at hH
                  · subst w
                    simp [H] at hH
              have hcost_pos : 0 < cost₂ := X_Z_cost_pos_of_continues hz hcont
              have hstep_lt : evmState''.gasAvailable < evmState'.gasAvailable :=
                stepResult.gas_lt hcost_pos hcostle
              have hdecr :
                  Prod.Lex (fun a b : UInt256 => sizeOf a < sizeOf b) (fun a b : Nat => a < b)
                    (evmState''.gasAvailable, 2) (evmState.gasAvailable, 2) := by
                by_cases hz_eq : evmState'.gasAvailable = evmState.gasAvailable
                · apply Prod.Lex.left
                  apply sizeOf_UInt256_le
                  simpa [hz_eq] using hstep_lt
                · have h_lt : evmState'.gasAvailable < evmState.gasAvailable := by
                    apply UInt256.lt_of_le_of_ne' hzg_le hz_eq
                  apply Prod.Lex.left
                  apply sizeOf_UInt256_le
                  exact UInt256.le_lt_trans' hstep_le h_lt
              XWithGasBound validJumps gasBound evmState''
                (UInt256.le_trans' (UInt256.le_trans' hstep_le hzg_le) hgasBound)
            | some o =>
              if w == .REVERT then
                /-
                  The Yellow Paper says we don't call the "iterator function" "O" for `REVERT`,
                  but we actually have to call the semantics of `REVERT` to pass the test
                  EthereumTests/BlockchainTests/GeneralStateTests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json
                  And the EEL spec does so too.
                -/
                .ok
                  { result := .revert evmState''.gasAvailable o
                    gas_le := by
                      exact UInt256.le_trans' (UInt256.le_trans' hstep_le hzg_le) hgasBound
                  }
              else
                .ok
                  { result := .success evmState'' o
                    gas_le := by
                      exact UInt256.le_trans' (UInt256.le_trans' hstep_le hzg_le) hgasBound
                  }
                termination_by (evmState.gasAvailable, 2)
                decreasing_by
                  · by_cases hz_eq : evmState'.gasAvailable = evmState.gasAvailable
                    · rw [hz_eq]
                      apply Prod.Lex.right
                      simp
                    · apply Prod.Lex.left
                      apply sizeOf_UInt256_le
                      exact UInt256.lt_of_le_of_ne' hzg_le hz_eq
                  · assumption

/--
  The code execution function
-/
def ΞWithGas -- Type `Ξ` using `\GX` or `\Xi`
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  Except
    EVM.ExecutionException
    (XiResult g)
:= do
      let defState : EVM.State := default
      let freshEvmState : EVM.State :=
        { defState with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := createdAccounts
            gasAvailable := g
            blocks := blocks
            genesisBlockHeader := genesisBlockHeader
        }
      let result ← XWithGasBound (D_J I.code ⟨0⟩) g freshEvmState (by simp [freshEvmState])
      match result with
        | ⟨.success evmState' o, hgas⟩ =>
          let finalGas := evmState'.gasAvailable
          .ok
            { result := ExecutionResult.success
                (evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate) o
              gas_le := by
                simpa [ExecutionResult.xiGasAvailable, ExecutionResult.gasAvailable, finalGas,
                  freshEvmState] using hgas
            }
        | ⟨.revert g' o, hgas⟩ =>
          .ok
            { result := ExecutionResult.revert g' o
              gas_le := by
                simpa [ExecutionResult.xiGasAvailable, ExecutionResult.gasAvailable,
                  freshEvmState] using hgas
            }
        termination_by (g, 3)

def LambdaWithGas
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare) -- needed for EIP-6780
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)          -- available gas
  (p : UInt256)          -- gas price
  (v : UInt256)          -- endowment
  (i : ByteArray)        -- the initialisation EVM code
  (e : UInt256)          -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader)      -- "I_H has no special treatment and is determined from the blockchain"
  (w : Bool)             -- permission to make modifications to the state
  :
  Except EVM.ExecutionException
    (LambdaResult g)
:=
  do
  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let n : UInt256 := (σ.find? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  let lₐ ← L_A s n ζ i
  let a : AccountAddress := -- (94) (95)
    (ffi.KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let existentAccount := σ.findD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (i, createdAccounts) :=
    if
      existentAccount.nonce ≠ ⟨0⟩
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, createdAccounts)
    else (i, createdAccounts.insert a)

  let newAccount : Account .EVM :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.find? s with
      | none =>  σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv .EVM :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , calldata := default
    , code      := i
    , gasPrice  := p.toNat
    , header    := H
    , depth     := e.toNat
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    }
  match ΞWithGas createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar exEnv with
    | .error e =>
      if e == .OutOfFuel then throw .OutOfFuel
      .ok
        { address := a
          createdAccounts := createdAccounts
          accountMap := σ
          gas := ⟨0⟩
          substate := AStar
          success := false
          output := .empty
          gas_le := by
            change (0 : Fin UInt256.size) ≤ g.val
            exact Nat.zero_le _
        }
    | .ok ⟨.revert g' o, hgas⟩ =>
      .ok
        { address := a
          createdAccounts := createdAccounts
          accountMap := σ
          gas := g'
          substate := AStar
          success := false
          output := o
          gas_le := hgas
        }
    | .ok ⟨.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData, hgas⟩ =>
      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.find? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

      let σ' : AccountMap .EVM := -- (115)
        if F then σ else
          let newAccount' := σStarStar.findD a default
          σStarStar.insert a {newAccount' with code := returnedData}

      -- (114)
      let g' := if F then 0 else gStarStar.toNat - c

      -- (116)
      let A' := if F then AStar else AStarStar
      -- (117)
      let z := not F
      .ok
        { address := a
          createdAccounts := createdAccounts'
          accountMap := σ'
          gas := .ofNat g'
          substate := A'
          success := z
          output := .empty
          gas_le := by
            have hg'le : g' ≤ gStarStar.toNat := by
              unfold g'
              split <;> omega
            exact le_trans (UInt256.ofNat_le_of_le_toNat hg'le) hgas
        } -- (93)
      termination_by (g, 4)
 where
  L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  := -- (96)
    let s := s.toByteArray
    let n := BE n.toNat
    match ζ with
      | none   => RLP <| .𝕃 [.𝔹 s, .𝔹 n]
      | some ζ => .some <| BE 255 ++ s ++ ζ ++ ffi.KEC i

/--
Message cal
`σ`  - evm state
`A`  - accrued substate
`s`  - sender
`o`  - transaction originator
`r`  - recipient
`c`  - the account whose code is to be called, usually the same as `r`
`g`  - available gas
`p`  - effective gas price
`v`  - value
`v'` - value in the execution context
`d`  - input data of the call
`e`  - depth of the message-call / contract-creation stack
`w`  - permissions to make modifications to the stack

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
def ΘWithGas
      (blobVersionedHashes : List ByteArray)
      (createdAccounts : Batteries.RBSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader)
      (blocks : ProcessedBlocks)
      (σ  : AccountMap .EVM)
      (σ₀  : AccountMap .EVM)
      (A  : Substate)
      (s  : AccountAddress)
      (o  : AccountAddress)
      (r  : AccountAddress)
      (c  : ToExecute .EVM)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Nat)
      (H : BlockHeader)
      (w  : Bool)
        :
      Except EVM.ExecutionException (ThetaResult g)
:=
  do

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.find? r with
      | none =>
        if v != UInt256.ofNat 0 then
          σ.insert r { (default : Account .EVM) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.find? s with
      | none => σ'₁
      | some acc =>
        σ'₁.insert s { acc with balance := acc.balance - v}

  let I : ExecutionEnv .EVM :=
    {
      codeOwner := r        -- Equation (132)
      sender    := o        -- Equation (133)
      gasPrice  := p.toNat  -- Equation (134)
      calldata := d        -- Equation (135)
      source    := s        -- Equation (136)
      weiValue  := v'       -- Equation (137)
      depth     := e        -- Equation (138)
      perm      := w        -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match c with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := H
      blobVersionedHashes := blobVersionedHashes
    }

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let θ ←
    match c with
      | ToExecute.Precompiled p =>
        match p with
          | 1  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_ECREC σ₁ g A I) (precompile_ECREC_gas_le σ₁ g A I)
          | 2  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_SHA256 σ₁ g A I) (precompile_SHA256_gas_le σ₁ g A I)
          | 3  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_RIP160 σ₁ g A I) (precompile_RIP160_gas_le σ₁ g A I)
          | 4  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_ID σ₁ g A I) (precompile_ID_gas_le σ₁ g A I)
          | 5  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_EXPMOD σ₁ g A I) (precompile_EXPMOD_gas_le σ₁ g A I)
          | 6  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_BN_ADD σ₁ g A I) (precompile_BN_ADD_gas_le σ₁ g A I)
          | 7  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_BN_MUL σ₁ g A I) (precompile_BN_MUL_gas_le σ₁ g A I)
          | 8  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_SNARKV σ₁ g A I) (precompile_SNARKV_gas_le σ₁ g A I)
          | 9  => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_BLAKE2_F σ₁ g A I) (precompile_BLAKE2_F_gas_le σ₁ g A I)
          | 10 => .ok <| ThetaResult.ofPrecompile g ∅ (Ξ_PointEval σ₁ g A I) (precompile_PointEval_gas_le σ₁ g A I)
          | _ => .error .InvalidInstruction
      | ToExecute.Code _ =>
        match ΞWithGas createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I with
          | .error e =>
            if e == .OutOfFuel then throw .OutOfFuel
            pure
              { createdAccounts := createdAccounts
                accountMap := σ
                gas := ⟨0⟩
                substate := A
                success := false
                output := .empty
                gas_le := by
                  change (0 : Fin UInt256.size) ≤ g.val
                  exact Nat.zero_le _
              }
          | .ok ⟨.revert g' o, hgas⟩ =>
            pure
              { createdAccounts := createdAccounts
                accountMap := σ
                gas := g'
                substate := A
                success := false
                output := o
                gas_le := hgas
              }
          | .ok ⟨.success (a, b, c, d) o, hgas⟩ =>
            pure
              { createdAccounts := a
                accountMap := b
                gas := c
                substate := d
                success := true
                output := o
                gas_le := hgas
              }

  let createdAccounts := θ.createdAccounts
  let z := θ.success
  let σ'' := θ.accountMap
  let g' := θ.gas
  let A'' := θ.substate
  let out := θ.output

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (119)
  .ok
    { createdAccounts := createdAccounts
      accountMap := σ'
      gas := g'
      substate := A'
      success := z
      output := out
      gas_le := by
        simpa [g'] using θ.gas_le
    }
  termination_by (g, 4)

end

def XWithGas (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (XResult evmState.gasAvailable)
:=
  XWithGasBound validJumps evmState.gasAvailable evmState (by rfl)

def X (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
:= do
  let result ← XWithGas validJumps evmState
  pure result.result

def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  Except
    EVM.ExecutionException
    (ExecutionResult (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
:= do
  let result ← ΞWithGas createdAccounts genesisBlockHeader blocks σ σ₀ g A I
  pure result.result

def Lambda
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (A : Substate)
  (s : AccountAddress)
  (o : AccountAddress)
  (g : UInt256)
  (p : UInt256)
  (v : UInt256)
  (i : ByteArray)
  (e : UInt256)
  (ζ : Option ByteArray)
  (H : BlockHeader)
  (w : Bool)
  :
  Except EVM.ExecutionException
    (AccountAddress × Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)
:= do
  let result ←
    LambdaWithGas blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o g p v i e ζ H w
  pure
    ( result.address
    , result.createdAccounts
    , result.accountMap
    , result.gas
    , result.substate
    , result.success
    , result.output
    )

def Θ
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Batteries.RBSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ  : AccountMap .EVM)
  (σ₀  : AccountMap .EVM)
  (A  : Substate)
  (s  : AccountAddress)
  (o  : AccountAddress)
  (r  : AccountAddress)
  (c  : ToExecute .EVM)
  (g  : UInt256)
  (p  : UInt256)
  (v  : UInt256)
  (v' : UInt256)
  (d  : ByteArray)
  (e  : Nat)
  (H : BlockHeader)
  (w  : Bool)
  :
  Except EVM.ExecutionException
    (Batteries.RBSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray)
:= do
  let result ←
    ΘWithGas blobVersionedHashes createdAccounts genesisBlockHeader blocks σ σ₀ A s o r c g p v v' d e H w
  pure
    ( result.createdAccounts
    , result.accountMap
    , result.gas
    , result.substate
    , result.success
    , result.output
    )

open Batteries (RBMap RBSet)


-- Type Υ using \Upsilon or \GU
def Υ
  (σ : AccountMap .EVM)
  (H_f : ℕ)
  (H : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except EVM.Exception (AccountMap .EVM × Substate × Bool × UInt256)
:= do
  let g₀ : ℕ := EVM.intrinsicGas T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.find? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Batteries.RBSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Batteries.RBSet.ofList AStar_K Substate.storageKeysCmp}
  let createdAccounts : Batteries.RBSet AccountAddress compare := .empty
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          Lambda
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            g
            p
            T.base.value
            T.base.data
            ⟨0⟩
            none
            H
            true
        with
          | .ok (_, _, σ_P, g', A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          Θ
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            t
            (toExecute .EVM σ₀ t)
            g
            p
            T.base.value
            T.base.value
            T.base.data
            0
            H
            true
        with
          | .ok (_, σ_P, g', A, z, _) => pure (σ_P, g', A, z)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  let gStar := g' + min ((T.base.gasLimit - g') / ⟨5⟩) A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance .EVM S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != UInt256.ofNat 0 then
      σStar.increaseBalance .EVM H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.1.foldl Batteries.RBMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Batteries.RBMap.erase σ' -- (88)
  let σ' := σ'.map λ (addr, acc) ↦ (addr, { acc with tstorage := .empty})
  .ok (σ', A, z, T.base.gasLimit - gStar)
end EVM

end EvmYul
