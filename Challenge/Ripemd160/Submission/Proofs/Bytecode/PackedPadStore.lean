import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableSparse

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPadStore

open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory StaggerTableSparse

private theorem byte128 (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat 128).toNat 32)[i]?.getD 0 =
      if i = 31 then 128 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat ((UInt256.ofNat 128).toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 31 then 128 else 0 := by decide
  exact h ⟨i, hi⟩

private theorem bytePacked (i : Nat) (hi : i < 32) :
    (Data.Bytes.natToBytesPadded (UInt256.ofNat (128 * (1 + 2 ^ 144))).toNat 32)[i]?.getD 0 =
      if i = 13 ∨ i = 31 then 128 else 0 := by
  rw [YulEvmCompiler.BytesLemmas.natToBytesPadded_getElem?_getD _ _ _ hi]
  have h : ∀ j : Fin 32,
      UInt8.ofNat ((UInt256.ofNat (128 * (1 + 2 ^ 144))).toNat / 256 ^ (32 - 1 - j.val) % 256) =
        if j.val = 13 ∨ j.val = 31 then 128 else 0 := by decide
  exact h ⟨i, hi⟩

/-- The packed store omits only the already-zero bytes at addresses 36 through 53. -/
theorem pack_two_128 (memory : ByteArray)
    (hzero : ∀ i, 36 ≤ i → i < 54 → memory[i]?.getD 0 = 0) :
    writeWord (writeWord memory 54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128) =
      writeWord memory 54 (UInt256.ofNat (128 * (1 + 2 ^ 144))) := by
  apply ByteArray.ext_getElem
  · simp only [writeWord_size]
    omega
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj]
    simp only [writeWord, MachineState.writeBytes_getElem?_getD,
      YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
    by_cases h36 : 36 ≤ i ∧ i < 36 + 32
    · by_cases h54 : 54 ≤ i ∧ i < 54 + 32
      · rw [if_pos h36, if_pos h54, byte128 _ (by omega), bytePacked _ (by omega)]
        split_ifs <;> first | rfl | omega
      · rw [if_pos h36, if_neg h54, byte128 _ (by omega), if_neg (by omega)]
        exact (hzero i h36.1 (by omega)).symm
    · by_cases h54 : 54 ≤ i ∧ i < 54 + 32
      · rw [if_neg h36, if_pos h54, byte128 _ (by omega), bytePacked _ (by omega)]
        split_ifs <;> first | rfl | omega
      · simp only [if_neg h36, if_neg h54]

/-- The same merge over an ARBITRARY base: all the merge needs is that bytes `[36,54)` of
the base are zero.  The pad block's real base is `writeBytes memory zeroBytes 28`, which
clears `[28,1112)` and so satisfies this just as `zeroMemory` does. -/
theorem after_length_stores_gen (base : ByteArray) (low : UInt256)
    (hz : ∀ i, 36 ≤ i → i < 54 → base[i]?.getD 0 = 0) :
    let preMemory := writeWord (writeWord (writeWord (writeWord
      base 162 low) 666 low) 144 low) 522 (UInt256.ofNat 128)
    writeWord (writeWord preMemory 54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128) =
      writeWord preMemory 54 (UInt256.ofNat (128 * (1 + 2 ^ 144))) := by
  dsimp only
  apply pack_two_128
  intro i hlo hhi
  simp only [writeWord, MachineState.writeBytes_getElem?_getD,
    YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  exact hz i hlo hhi

/-- Arbitrary length values are allowed: their writes cannot touch the omitted prefix. -/
theorem after_length_stores (memory : ByteArray) (low : UInt256) :
    let preMemory := writeWord (writeWord (writeWord (writeWord
      (zeroMemory memory) 162 low) 666 low) 144 low) 522 (UInt256.ofNat 128)
    writeWord (writeWord preMemory 54 (UInt256.ofNat 128)) 36 (UInt256.ofNat 128) =
      writeWord preMemory 54 (UInt256.ofNat (128 * (1 + 2 ^ 144))) :=
  after_length_stores_gen (zeroMemory memory) low
    (fun i hlo hhi => by rw [zeroMemory_getD, if_pos (by omega)])

#print axioms pack_two_128
#print axioms after_length_stores

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PackedPadStore
