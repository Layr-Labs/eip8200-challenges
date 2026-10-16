import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTablePad

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-!
# The pad-only table as one code copy

The pad-only low block used to clear `[28, 1112)` by copying calldata past its end and then store
`0x80` at 522 (one word) and at 54 (a packed `PUSH19` word putting `0x80` at 67 and 85). It now
copies a 1084-byte image from the code to memory 28 instead: zero except `0x80` at image offsets
39, 57 and 525 (memory 67, 85 and 553). After the three length stores the memory is exactly the
old `padRealChain` image, so every consumer of that image is unchanged.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PadImageStore

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory

/-- The pad-only table image: zero except `0x80` at offsets 39, 57 and 525. -/
def padImage : ByteArray :=
  ByteArray.mk ((((Array.replicate 1084 (0 : UInt8)).set! 39 128).set! 57 128).set! 525 128)

@[simp] theorem padImage_size : padImage.size = 1084 := by decide

theorem padImage_getD (i : Nat) :
    padImage[i]?.getD 0 = if i = 39 ∨ i = 57 ∨ i = 525 then 128 else 0 := by
  by_cases hi : i < 1084
  · have h : ∀ j : Fin 1084, padImage[j.val]?.getD 0 =
        (if j.val = 39 ∨ j.val = 57 ∨ j.val = 525 then 128 else 0 : UInt8) := by decide
    exact h ⟨i, hi⟩
  · rw [if_neg (by omega), getElem?_neg padImage i (by rw [padImage_size]; omega)]
    rfl

private theorem word128_getD (j : Nat) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 128).toNat 32)[j]?.getD 0 =
      if j = 31 then 128 else 0 := by
  by_cases hj : j < 32
  · rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hj]
    have h : ∀ k : Fin 32,
        UInt8.ofNat ((UInt256.ofNat 128).toNat / 256 ^ (32 - 1 - k.val) % 256) =
          if k.val = 31 then 128 else 0 := by decide
    exact h ⟨j, hj⟩
  · rw [if_neg (by omega), getElem?_neg _ j
      (by rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_size]; omega)]
    rfl

private theorem zeros_getD (i : Nat) :
    (ByteArray.mk (Array.replicate 1084 (0 : UInt8)))[i]?.getD 0 = 0 := by
  change (Array.replicate 1084 (0 : UInt8))[i]?.getD 0 = 0
  by_cases hi : i < 1084
  · rw [getElem?_pos _ _ (by simpa using hi)]
    simp
  · rw [getElem?_neg _ _ (by simpa using hi)]
    rfl

private theorem zeros_size : (ByteArray.mk (Array.replicate 1084 (0 : UInt8))).size = 1084 := rfl

/-- The copied image followed by the three length stores is the old pad-only low-block image. -/
theorem image_chain (memory : ByteArray) (n : UInt256) :
    writeWord (writeWord (writeWord (MachineState.writeBytes memory padImage 28)
        162 (StaggerTablePad.lowDirty n)) 666 (StaggerTablePad.lowDirty n))
        144 (StaggerTablePad.lowDirty n) =
      StaggerTablePad.padRealChain memory n := by
  apply ByteArray.ext_getElem
  · simp only [StaggerTablePad.padRealChain, StaggerTablePad.lowChainOver,
      StaggerTableSparse.zeroSuffix, writeWord, MachineState.writeBytes_size,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, padImage_size, zeros_size]
    simp only [show (32 : Nat) = 0 ↔ False by decide, show (1084 : Nat) = 0 ↔ False by decide,
      if_false]
    omega
  · intro i hiA hiB
    rw [← Memory.getD0_eq_getElem _ _ hiA, ← Memory.getD0_eq_getElem _ _ hiB]
    simp only [StaggerTablePad.padRealChain, StaggerTablePad.lowChainOver,
      StaggerTableSparse.zeroSuffix, writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size, padImage_size, zeros_size,
      padImage_getD, zeros_getD, word128_getD]
    split_ifs <;> first | rfl | omega

#print axioms padImage_getD
#print axioms image_chain

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PadImageStore
