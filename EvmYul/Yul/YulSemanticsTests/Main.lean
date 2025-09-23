import EvmYul.Yul.Interpreter
import EvmYul.Yul.YulNotation

namespace EvmYul

namespace Yul

open Ast SizeLemmas

def callerAddressUInt256 : UInt256 := ⟨1⟩
def storageAddressUInt256 : UInt256 := ⟨2⟩
def callerAddress := AccountAddress.ofUInt256 callerAddressUInt256
def storageAddress := AccountAddress.ofUInt256 storageAddressUInt256

def stateEg₁ : Yul.State :=
  let storageCode : YulContract := 
  
  
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    switch shr(224, calldataload(0))
                    case 0x2e64cec1 { external_fun_retrieve() }
                    case 0x6057361d { external_fun_store() }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "abi_decode"
          <f
          function abi_decode(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "external_fun_retrieve"
          <f
          function external_fun_retrieve()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                abi_decode(4, calldatasize())
                let ret := fun_retrieve()
                let memPos := mload(64)
                let _1 := abi_encode_uint256(memPos, ret)
                return(memPos, sub(_1, memPos))
            }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "external_fun_store"
          <f
          function external_fun_store()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_store(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "fun_retrieve"
          <f
          function fun_retrieve() -> var
            {
                var :=  sload( 0x00)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_store"
          <f
          function fun_store(var_num)
            {
                update_storage_value_offset_uint256_to_uint256(0x00, var_num)
            }
        
           >


}
  
  
  let storageAccount : Account .Yul :=
    { code := storageCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
  let callerCode : YulContract := 
  
  {
dispatcher := 
      <s {
                mstore(64, 0x80)
                if iszero(lt(calldatasize(), 4))
                {
                    if eq(0x5ec1cee6, shr(224, calldataload(0)))
                    {
                        external_fun_testStoreAndRetrieveExternal()
                    }
                }
                revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            } >,
functions := (∅ : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition))

            |>.insert
          "revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb"
          <f
          function revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b"
          <f
          function revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
            { revert(0, 0) }
            
           >

          |>.insert
          "validator_revert_uint256"
          <f
          function validator_revert_uint256(value)
            { if 0 { revert(0, 0) } }
            
           >

          |>.insert
          "abi_decode_uint256"
          <f
          function abi_decode_uint256(offset, end) -> value
            {
                value := calldataload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_tuple_uint256"
          <f
          function abi_decode_tuple_uint256(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_uint256(headStart, dataEnd)
            }
            
           >

          |>.insert
          "external_fun_testStoreAndRetrieveExternal"
          <f
          function external_fun_testStoreAndRetrieveExternal()
            {
                if callvalue()
                {
                    revert_error_ca66f745a3ce8ff40e2ccaf1ad45db7774001b90d25810abd9040049be7bf4bb()
                }
                let _1 := abi_decode_tuple_uint256(4, calldatasize())
                fun_testStoreAndRetrieveExternal(_1)
                return(0, 0)
            }
            
           >

          |>.insert
          "revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74"
          <f
          function revert_error_42b3090547df1d2001c96683413b8cf91c1b902ef5e3cb8d9f6f304cf7446f74()
            { revert(0, 0) }
            
           >

          |>.insert
          "revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20"
          <f
          function revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
            { revert(0, 0) }
            
           >

          |>.insert
          "panic_error_0x41"
          <f
          function panic_error_0x41()
            {
                mstore(0, shl(224, 0x4e487b71))
                mstore(4, 0x41)
                revert(0, 0x24)
            }
            
           >

          |>.insert
          "finalize_allocation"
          <f
          function finalize_allocation(memPtr, size)
            {
                let newFreePtr := add(memPtr, and(add(size, 31), not(31)))
                if or(gt(newFreePtr, 0xffffffffffffffff), lt(newFreePtr, memPtr)) { panic_error_0x41() }
                mstore(64, newFreePtr)
            }
            
           >

          |>.insert
          "abi_decode_fromMemory"
          <f
          function abi_decode_fromMemory(headStart, dataEnd)
            {
                if slt(sub(dataEnd, headStart), 0)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
            }
            
           >

          |>.insert
          "abi_encode_uint256_to_uint256"
          <f
          function abi_encode_uint256_to_uint256(value, pos)
            { mstore(pos, value) }
            
           >

          |>.insert
          "abi_encode_uint256"
          <f
          function abi_encode_uint256(headStart, value0) -> tail
            {
                tail := add(headStart, 32)
                abi_encode_uint256_to_uint256(value0, headStart)
            }
            
           >

          |>.insert
          "revert_forward"
          <f
          function revert_forward()
            {
                let pos := mload(64)
                let _1 := returndatasize()
                returndatacopy(pos, 0, _1)
                let _2 := returndatasize()
                revert(pos, _2)
            }
            
           >

          |>.insert
          "abi_decode_t_uint256_fromMemory"
          <f
          function abi_decode_t_uint256_fromMemory(offset, end) -> value
            {
                value := mload(offset)
                validator_revert_uint256(value)
            }
            
           >

          |>.insert
          "abi_decode_uint256_fromMemory"
          <f
          function abi_decode_uint256_fromMemory(headStart, dataEnd) -> value0
            {
                if slt(sub(dataEnd, headStart), 32)
                {
                    revert_error_dbdddcbe895c83990c08b3492a0e83918d802a52331272ac6fdb6a7c4aea3b1b()
                }
                value0 := abi_decode_t_uint256_fromMemory(headStart, dataEnd)
            }
            
           >

          |>.insert
          "update_byte_slice_shift"
          <f
          function update_byte_slice_shift(value, toInsert) -> result
            {
                toInsert := toInsert
                result := toInsert
            }
            
           >

          |>.insert
          "update_storage_value_offset_uint256_to_uint256"
          <f
          function update_storage_value_offset_uint256_to_uint256(slot, value)
            {
                let _1 := sload(slot)
                let _2 := update_byte_slice_shift(_1, value)
                sstore(slot, _2)
            }
            
           >

          |>.insert
          "fun_testStoreAndRetrieveExternal"
          <f
          function fun_testStoreAndRetrieveExternal(var_v)
            {
                let _1 := 1
                if iszero(_1)
                {
                    revert_error_0cc013b6b3b6beabea4e3a74a6d380f0df81852ca99887912475e1f66b2a2c20()
                }
                let _2 :=  mload(64)
                mstore(_2,  shl(224, 0x6057361d))
                let _3 := abi_encode_uint256(add(_2, 4), var_v)
                let _4 := gas()
                let _5 := call(_4,  2,  0, _2, sub(_3, _2), _2, 0)
                if iszero(_5) { revert_forward() }
                if _5
                {
                    let _6 := 0
                    if 0 { _6 := returndatasize() }
                    finalize_allocation(_2, _6)
                    abi_decode_fromMemory(_2, add(_2, _6))
                }
                let _7 :=  mload(64)
                mstore(_7,  shl(224, 0x2e64cec1))
                let _8 := add(_7,  4)
                let _9 := gas()
                let _10 := call(_9,  2,  0,  _7, sub( _8,  _7), _7, 32)
                if iszero(_10) { revert_forward() }
                let expr
                if _10
                {
                    let _11 := 32
                    let _12 := returndatasize()
                    if gt(32, _12) { _11 := returndatasize() }
                    finalize_allocation(_7, _11)
                    expr := abi_decode_uint256_fromMemory(_7, add(_7, _11))
                }
                update_storage_value_offset_uint256_to_uint256( 0,  expr)
            }
        
           >


}
  
  
  let callerAccount : Account .Yul :=
    { code := callerCode
    , balance := ⟨1000⟩
    , nonce := ⟨0⟩ 
    , storage := ∅
    , tstorage := ∅
    }
  let accountMap : AccountMap .Yul := Batteries.RBMap.insert ∅ storageAddress storageAccount
                                      |>.insert callerAddress callerAccount
  let sharedState : SharedState .Yul :=
    { accountMap := accountMap
    , σ₀ := ∅
    , totalGasUsedInBlock := 0
    , transactionReceipts := #[]
    , substate := Inhabited.default
    , executionEnv := 
        { calldata := ByteArray.mk #[]
        , code := Inhabited.default
        , codeOwner := callerAddress
        , source := Inhabited.default
        , weiValue := ⟨0⟩
        , sender := Inhabited.default
        , gasPrice := 0
        , header := (Inhabited.default : BlockHeader)
        , depth := 0
        , perm := true
        , blobVersionedHashes := []
        }
    , blocks := ∅
    , genesisBlockHeader := Inhabited.default
    , createdAccounts := ∅
    , gasAvailable := ⟨0⟩
    , activeWords := ⟨0⟩
    , memory := ByteArray.mk #[]
    , returnData := ByteArray.mk #[]
    , H_return := ByteArray.mk #[]
    }
  Yul.State.Ok sharedState ∅
    
def test₁ :=
  let expr : Expr := .Call (Sum.inr "fun_testStoreAndRetrieveExternal") [.Lit ⟨42⟩]
  match (exec 99 (.ExprStmtCall expr) stateEg₁) with
  | .error e => repr e
  | .ok s => s!"{s.toSharedState.accountMap.toList.map (fun (a : AccountAddress × Account .Yul) => repr a.1 ++ " " ++ repr a.2.storage.toList)}"

end Yul

end EvmYul

open EvmYul.Yul

-- Run this test via `lake exe yulSemanticsTests`.
-- `#eval` cannot run the test because it uses the foreign function interface for `ByteArray.zeroes`.
def main : IO Unit := do
  IO.println s!"test₁: {test₁}"
  -- IO.println s!"Test 3: {stateEg₁.toSharedState.accountMap.toList.map (fun a => repr a.1 ++ " " ++ repr a.2.storage.toList)}"
