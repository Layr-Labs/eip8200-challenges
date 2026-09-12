import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairTableScratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerTableMemory
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory StaggerTableMemory

def scratchMemory (memory : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord memory 60 high) 28 low

@[simp] theorem scratch_read_low (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (scratchMemory memory low high) 28 = low :=
  read_writeWord _ _ _

@[simp] theorem scratch_read_high (memory : ByteArray) (low high : UInt256) :
    MachineState.readWord (scratchMemory memory low high) 60 = high := by
  rw [scratchMemory, read_writeWord_disjoint _ _ _ _ (Or.inr (by decide)), read_writeWord]

def poolWord (memory : ByteArray) (i : Nat) : UInt256 :=
  Word.mask32 (MachineState.readWord memory (4 * i))

theorem poolWord_eq (memory : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    poolWord (scratchMemory memory low high) i =
      Word.mask32 (UInt256.shiftRight (if i < 8 then low else high)
        (UInt256.ofNat (32 * (7 - i % 8)))) := by
  by_cases hlow : i < 8
  · rw [if_pos hlow, Nat.mod_eq_of_lt hlow]
    have h := PairTableScratch.mask32_window (scratchMemory memory low high) 28 i (by decide) hlow
    rw [scratch_read_low] at h
    have ha : 28 + 4 * i - 28 = 4 * i := by omega
    simpa only [poolWord, ha] using h
  · rw [if_neg hlow]
    have hmod : i % 8 = i - 8 := by omega
    rw [hmod]
    have h := PairTableScratch.mask32_window (scratchMemory memory low high) 60 (i - 8) (by decide) (by omega)
    rw [scratch_read_high] at h
    have ha : 60 + 4 * (i - 8) - 28 = 4 * i := by omega
    simpa only [poolWord, ha] using h

private theorem chunk_eq_mask (value : UInt256) (j : Nat) (hj : j < 8) :
    PairedScheduleData.chunk value j =
      Word.mask32 (UInt256.shiftRight (PairedScheduleData.reversedWord value)
        (UInt256.ofNat (32 * (7 - j)))) := by
  by_cases h0 : j = 0
  · subst j
    simp only [PairedScheduleData.chunk, if_pos rfl, Nat.sub_zero]
    exact (DenseScheduleMemory.DensePacked.mask32_shr224 _).symm
  · by_cases h7 : j = 7
    · subst j
      simp only [PairedScheduleData.chunk, if_neg h0, if_pos rfl,
        Nat.sub_self, Nat.mul_zero]
      change Word.mask32 (PairedScheduleData.reversedWord value) = Word.mask32 (UInt256.shiftRight (PairedScheduleData.reversedWord value) (UInt256.ofNat 0))
      congr 1
      exact PairedScheduleData.shr_zero _ |>.symm
    · simp only [PairedScheduleData.chunk, if_neg h0, if_neg h7,
        DenseScheduleMemory.DensePacked.shr]

/-- All sixteen sources are clean 32-bit chunks before any table overwrite. -/
theorem poolWord_eq_extracted (memory : ByteArray) (p i : Nat) (hi : i < 16) :
    poolWord (scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory p))
        (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))) i =
      PairedScheduleData.extractedWord memory p i := by
  rw [poolWord_eq _ _ _ _ hi, PairedScheduleData.extractedWord,
    chunk_eq_mask _ _ (Nat.mod_lt _ (by decide))]
  by_cases h : i < 8
  · rw [if_pos h, Nat.div_eq_of_lt h]
    simp only [Nat.mul_zero, Nat.add_zero]
  · rw [if_neg h]
    have hd : i / 8 = 1 := by omega
    rw [hd]

theorem erase_scratch (memory : ByteArray) (words : Nat → UInt256)
    (low high : UInt256) :
    storeDescending (scratchMemory memory low high) words 0 61 =
      storeDescending memory words 0 61 := by
  apply ByteArray.ext_getElem
  · rw [storeDescending_size _ _ _ _ (by omega),
      storeDescending_size _ _ _ _ (by omega)]
    simp only [scratchMemory, writeWord_size]
    omega
  · intro address hA hB
    rw [← Memory.getD0_eq_getElem _ _ hA, ← Memory.getD0_eq_getElem _ _ hB]
    by_cases hin : address < 632
    · exact getD_storeDescending_inside _ _ _ _ _ _ (by omega) (by omega) (by simpa using hin)
    · rw [getD_table_outside _ _ _ (by omega), getD_table_outside _ _ _ (by omega)]
      simp only [scratchMemory, writeWord, MachineState.writeBytes_getElem?_getD,
        YulEvmCompiler.BytesLemmas.natToBytesPadded_size]
      rw [if_neg (by omega), if_neg (by omega)]


#print axioms poolWord_eq_extracted
#print axioms erase_scratch
end Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch
