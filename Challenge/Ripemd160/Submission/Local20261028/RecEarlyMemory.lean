import Challenge.EvmProof.Memory
import YulEvmCompiler.BytesLemmas

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

/-!
# Erasing a speculative serialized answer on a scanner miss

The miss continuation clears the one speculative word before entering the
ordinary padding prefix.  The states do not coincide at PC 246: the cleared
word and its high-water mark are absorbed by the *nonempty* calldata copy.
-/
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeFallback

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

/-- The entire speculative allocation, after the cleanup store. -/
def zero32 : ByteArray := ByteArray.mk (Array.replicate 32 0)

private theorem bytes_ext (a b : ByteArray) (hs : a.size = b.size)
    (hg : ∀ i : Nat, a[i]?.getD (0 : UInt8) = b[i]?.getD 0) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · exact hs
  · intro i ha hb
    have h := hg i
    rw [getElem?_pos _ i ha, getElem?_pos _ i hb] at h
    exact h

@[simp] theorem zero32_size : zero32.size = 32 := by rfl

@[simp] theorem zero32_getD (i : Nat) : zero32[i]?.getD 0 = 0 := by
  change (Array.replicate 32 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 32
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

/-- MSTORE(0,0) overwrites, rather than merely obscuring, all speculative bytes. -/
theorem clear_word (m : ByteArray) (hm : m.size = 32) :
    MachineState.writeBytes m (Data.Bytes.natToBytesPadded 0 32) 0 = zero32 := by
  have hz : Data.Bytes.natToBytesPadded 0 32 = zero32 := by
    apply bytes_ext
    · exact YulEvmCompiler.BytesLemmas.natToBytesPadded_size 0 32
    · intro i
      by_cases hi : i < 32
      · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
        simp
      · rw [Memory.getElem?_getD_eq_zero_of_size_le _ _ (by
          rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
        simp
  rw [hz]
  apply bytes_ext
  · simp [MachineState.writeBytes_size, hm]
  · intro i
    rw [MachineState.writeBytes_getElem?_getD]
    by_cases hi : i < 32
    · simp [hi]
    · have hm' : ¬ i < m.size := by omega
      simp [hi, getElem?_neg, hm']

/-- A nonempty write beyond the cleared word grows both memories to the same
size; zero padding makes their untouched bytes identical.  The nonempty
hypothesis matters because `writeBytes` treats an empty write as a no-op. -/
theorem writeBytes_absorb_zero32 (bytes : ByteArray) (start : Nat)
    (hstart : 32 ≤ start) (hne : 0 < bytes.size) :
    MachineState.writeBytes zero32 bytes start =
      MachineState.writeBytes ByteArray.empty bytes start := by
  apply bytes_ext
  · simp only [MachineState.writeBytes_size, zero32_size, ByteArray.size_empty,
      if_neg (by omega : bytes.size ≠ 0)]
    omega
  · intro i
    simp [MachineState.writeBytes_getElem?_getD]

/-- In particular, the generic calldata copy absorbs the cleared answer. -/
theorem calldata_absorb_zero32 (input : ByteArray) (hpos : 0 < input.size) :
    MachineState.writeBytes zero32 (MachineState.readPadded input 0 input.size) 1056 =
      MachineState.writeBytes ByteArray.empty
        (MachineState.readPadded input 0 input.size) 1056 := by
  apply writeBytes_absorb_zero32 _ _ (by decide)
  simpa only [Memory.readPadded_size] using hpos


#print axioms calldata_absorb_zero32
end Challenge.Ripemd160.Submission.Proofs.Bytecode.EarlySerializeFallback
