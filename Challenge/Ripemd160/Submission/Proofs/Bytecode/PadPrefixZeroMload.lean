import Challenge.Ripemd160.Submission.Proofs.Bytecode.PadPrefixMemoryKernel
import Challenge.EvmProof.Memory
import YulEvmCompiler.Decode
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace AstraPadPrefixKernel
open EvmSemantics Challenge.EvmProof

theorem readWord_zero_of_bytes (memory : ByteArray) (address : Nat)
    (h : ∀ k, k < 32 → memory[address+k]?.getD 0 = 0) :
    MachineState.readWord memory address = UInt256.ofNat 0 := by
  have heq : MachineState.readPadded memory address 32 =
      MachineState.readPadded ByteArray.empty address 32 := by
    apply Memory.readPadded_congr
    intro k hk
    simpa using h k hk
  rw [MachineState.readWord, heq]
  simp only [MachineState.readPadded, ByteArray.size_empty, Nat.min_zero,
    Nat.sub_zero, Nat.zero_min, Nat.zero_add, ByteArray.extract_same,
    ByteArray.empty_append]
  simp only [Data.Bytes.bytesToBigEndianNat,
    YulEvmCompiler.ByteArray.toList_eq_data, Array.toList_replicate]
  decide

theorem zero_pair_readWord (memory : ByteArray) (words : Nat → UInt256)
    (j : Nat) (hj : 0 < j ∧ j < 61)
    (hleft : words j = UInt256.ofNat 0)
    (hright : words (j-1) = UInt256.ofNat 0) :
    MachineState.readWord (storeDescending memory words 0 61) (18*j) =
      UInt256.ofNat 0 := by
  apply readWord_zero_of_bytes
  intro k hk
  exact zero_pair_byte memory words j k hj hk hleft hright

#print axioms zero_pair_readWord
end AstraPadPrefixKernel
