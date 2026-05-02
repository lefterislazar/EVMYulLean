import EvmYul.EVM.Gas
import EvmYul.EVM.Instr

namespace EvmYul

namespace EVM

section Gas

open GasConstants InstructionGasGroups

def ContinuesAfterXStep (w : Operation .EVM) : Prop :=
  δ w ≠ none ∧ w ∉ [.STOP, .RETURN, .REVERT, .SELFDESTRUCT]

lemma Caccess_pos (a A) : 0 < Caccess a A := by
  unfold Caccess
  split <;> simp [Gwarmaccess, Gcoldaccountaccess]

lemma Cextra_pos (t r val σ A) : 0 < Cextra t r val σ A := by
  unfold Cextra
  have h := Caccess_pos t A
  omega

lemma Ccall_pos (t r val g σ μ A) : 0 < Ccall t r val g σ μ A := by
  unfold Ccall
  have h := Cextra_pos t r val σ A
  omega

lemma Csload_pos (μₛ A I) : 0 < Csload μₛ A I := by
  unfold Csload
  split <;> simp [Gwarmaccess, Gcoldsload]

lemma Csstore_storeComponent_pos (v v₀ v' : UInt256) :
    0 < (if v = v' || v₀ ≠ v then Gwarmaccess else
      if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else Gsreset) := by
  by_cases h₁ : v = v' ∨ v₀ ≠ v
  · simp [h₁, Gwarmaccess]
  · by_cases h₂ : (v ≠ v' ∧ v₀ = v) ∧ v₀ = ⟨0⟩
    · simp [h₂]
      split <;> simp [Gsset, Gsreset]
    · simp [h₁, h₂, Gsreset]

lemma Csstore_pos (s : State) : 0 < Csstore s := by
  unfold Csstore
  exact Nat.lt_of_lt_of_le (Csstore_storeComponent_pos _ _ _) (Nat.le_add_left _ _)

lemma Cselfdestruct_pos (s : State) : 0 < Cselfdestruct s := by
  unfold Cselfdestruct
  repeat split <;> simp [Gselfdestruct, Gcoldaccountaccess, Gnewaccount]

set_option maxHeartbeats 800000 in
lemma C'_pos_of_continuesAfterXStep (s : State) {w : Operation .EVM}
    (h : ContinuesAfterXStep w) : 0 < C' s w := by
  cases w <;> rename_i a <;> cases a <;>
    simp [ContinuesAfterXStep, δ, C', Wzero, Wbase, Wverylow, Wlow, Wmid, Whigh,
      Wcopy, Wextaccount, Wverylow.pushInstrsWithoutZero, Wverylow.dupInstrs,
      Wverylow.swapInstrs, Caccess_pos, Ccall_pos, Csload_pos, Csstore_pos,
      Ctstore, Ctload, Gjumpdest, Gbase, Gverylow, Glow, Gmid, Ghigh, Gexp,
      Gexpbyte, Gcopy, Glog, Glogdata, Glogtopic, Gcreate, Gkeccak256,
      Gkeccak256word, Gblockhash, HASH_OPCODE_GAS] at h ⊢ <;>
    repeat split
  all_goals
    try unfold GasConstants.Gwarmaccess at h ⊢
    norm_num [GasConstants.Gexp, GasConstants.Gexpbyte, GasConstants.Gwarmaccess,
      Gverylow, Glow, Gmid, Ghigh] at h ⊢

end Gas

end EVM

end EvmYul
