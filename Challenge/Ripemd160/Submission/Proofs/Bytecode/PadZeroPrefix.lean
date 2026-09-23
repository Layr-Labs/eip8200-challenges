import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadZeroPrefix
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- The persistent first-word invariant makes its first 28 bytes zero. -/
theorem prefix_zero (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32)
    (i : Nat) (hi : i < 28) : memory[i]?.getD 0 = 0 := by
  have hp : (2 : Nat) ^ 32 ≤ 2 ^ ((32 - (i + 1)) * 8) :=
    Nat.pow_le_pow_right (by decide) (by omega)
  have hz : Precompile.bytesToNatPadded memory 0 (i + 1) = 0 := by
    rw [← Bytes.readWord_shift_toNat memory 0 (i + 1) (by omega),
      Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt (hlow.trans_le hp)]
  have hs := Bytes.bytesToNatPadded_succ memory 0 i
  rw [hz, Nat.zero_add] at hs
  have hb : (YulSemantics.EVM.byteFrom memory.toList i).toNat = 0 := by omega
  have he : YulSemantics.EVM.byteFrom memory.toList i = (0 : UInt8) :=
    UInt8.toNat_inj.mp hb
  change memory.data[i]?.getD 0 = 0
  simpa only [YulSemantics.EVM.byteFrom, List.getD_eq_getElem?_getD,
    YulEvmCompiler.ByteArray.toList_eq_data, Array.getElem?_toList] using he

def zeroBytes : ByteArray := ByteArray.mk (Array.replicate 1084 (0 : UInt8))

@[simp] theorem zeroBytes_size : zeroBytes.size = 1084 := rfl

@[simp] theorem zeroBytes_getD (i : Nat) : zeroBytes[i]?.getD 0 = 0 := by
  change (Array.replicate 1084 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 1084
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

/-- Clearing the remaining suffix produces exactly the original full table clear. -/
theorem write_suffix_eq (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat < 2 ^ 32) :
    MachineState.writeBytes memory zeroBytes 28 = StaggerTableSparse.zeroMemory memory := by
  apply ByteArray.ext_getElem
  · simp [MachineState.writeBytes_size]
  · intro i hiA hiB
    rw [← Memory.getD0_eq_getElem _ _ hiA, ← Memory.getD0_eq_getElem _ _ hiB,
      MachineState.writeBytes_getElem?_getD, StaggerTableSparse.zeroMemory_getD]
    simp only [zeroBytes_size, zeroBytes_getD]
    by_cases hi : i < 28
    · rw [if_neg (by omega), if_pos (by omega), prefix_zero memory hlow i hi]
    · by_cases hend : i < 1112
      · rw [if_pos (by omega), if_pos hend]
      · rw [if_neg (by omega), if_neg hend]

theorem readPadded_end (input : ByteArray) :
    MachineState.readPadded input input.size 1084 = zeroBytes := by
  simp [MachineState.readPadded, zeroBytes]

#print axioms prefix_zero
#print axioms write_suffix_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadZeroPrefix
