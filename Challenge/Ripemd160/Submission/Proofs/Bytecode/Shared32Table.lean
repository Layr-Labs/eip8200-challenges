import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Table

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Scratch

def highScalar (k : Nat) : Nat := if k = 8 then 128 else if k = 14 then 256 else 0

def words (memory : ByteArray) (k : Nat) : UInt256 :=
  if k < 8 then StaggerScratch.dirtyWord memory 1120 k else UInt256.ofNat (highScalar k)

def scalars (memory : ByteArray) (k : Nat) : UInt32 :=
  UInt32.ofNat (if k < 8 then (PairedScheduleData.extractedWord memory 1120 k).toNat
    else highScalar k)

theorem words_split (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat = (scalars memory k).toNat +
        (words memory k).toNat / 2 ^ 32 * 2 ^ 32 ∧
      (words memory k).toNat / 2 ^ 32 < 2 ^ 64 ∧
      (k ≠ 2 → (words memory k).toNat / 2 ^ 32 < 2 ^ 32) ∧
      (¬ (k = 1 ∨ k = 2) → (words memory k).toNat / 2 ^ 32 = 0) := by
  by_cases hl : k < 8
  · have hs := StaggerScratch.dirtyWord_split memory 1120 k
    have hb := PairedScheduleData.extractedWord_bound memory 1120 k
    simpa only [words, scalars, if_pos hl, UInt32.toNat_ofNat',
      show UInt32.size = 2 ^ 32 by rfl, Nat.mod_eq_of_lt hb] using hs
  · interval_cases k <;> norm_num [words, scalars, highScalar, Word.word_toNat_ofNat]

theorem words_clean (memory : ByteArray) (k : Nat) (hk0 : 3 ≤ k) (hk1 : k < 16) :
    (words memory k).toNat < 2 ^ 32 := by
  by_cases hl : k < 8
  · have hd : ¬(k = 1 ∨ k = 2) := by omega
    rw [words, if_pos hl, StaggerScratch.dirtyWord, if_neg hd]
    exact PairedScheduleData.extractedWord_bound memory 1120 k
  · interval_cases k <;> norm_num [words, highScalar, Word.word_toNat_ofNat]

/-! ## The JD6 table image for the 32-byte route -/

/-- The endian scratch word the loader builds. -/
def lowW (memory : ByteArray) : UInt256 :=
  PairedScheduleData.reversedWord (MachineState.readWord memory 1120)

/-- The schedule fields as the fan presents them, which is what the writer stores. -/
def WJ (memory : ByteArray) : Nat → UInt256 :=
  Shared32Scratch.wordsJ memory (lowW memory) highWord

theorem fanWord_eq_poolWord (memory : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    Shared32Scratch.fanWord low high i
      = StaggerScratch.poolWord (StaggerScratch.scratchMemory memory low high) i :=
  (StaggerScratch.poolWord_eq memory low high i hi).symm

theorem fanWord_high_irrelevant (low high high' : UInt256) (i : Nat) (hi : i < 8) :
    Shared32Scratch.fanWord low high i = Shared32Scratch.fanWord low high' i := by
  rw [Shared32Scratch.fanWord, Shared32Scratch.fanWord, if_pos hi, if_pos hi]

theorem fanWord_eq_scalars (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (Shared32Scratch.fanWord (lowW memory) highWord k).toNat = (scalars memory k).toNat := by
  by_cases hl : k < 8
  · rw [fanWord_high_irrelevant (lowW memory) highWord
        (PairedScheduleData.reversedWord (MachineState.readWord memory (1120 + 32))) k hl,
      fanWord_eq_poolWord memory _ _ k hk, lowW,
      StaggerScratch.poolWord_eq_extracted memory 1120 k hk, scalars, if_pos hl,
      UInt32.toNat_ofNat']
    exact (Nat.mod_eq_of_lt (PairedScheduleData.extractedWord_bound memory 1120 k)).symm
  · rw [fanWord_eq_poolWord memory (lowW memory) highWord k hk]
    have h := Shared32Scratch.pool_upper memory (lowW memory) k (by omega) hk
    rw [StaggerScratch.poolWordD, if_neg (by omega)] at h
    rw [h, scalars, if_neg hl, highScalar]
    interval_cases k <;> norm_num [Word.word_toNat_ofNat]

/-- **The writer bridge for this route.**  No bound on any source word. -/
theorem writer_memoryJ (memory : ByteArray) (hgap : PairStoreGap.GapClear memory) :
    Pair13WriterRaw.writerMemory
      (Shared32Scratch.fanMemory memory (lowW memory) highWord) (WJ memory)
      = Pair13Memory.resultMemoryJ memory (WJ memory) := by
  rw [Pair13Memory.writerMemory_eq_resultMemoryJ _ (WJ memory)
      (Shared32Scratch.fanMemory_gapClear _ _ _ hgap),
    Pair13Memory.resultMemoryJ, Pair13Memory.resultMemoryJ,
    Shared32Scratch.erase_fan memory (Pair13Memory.tableJ (WJ memory)) _ _]

/-- The per-slot junk the table image carries. -/
def GJ (memory : ByteArray) (j : Nat) : Nat :=
  ((Pair13Memory.tableJ (WJ memory) j).toNat % 2 ^ 144) / 2 ^ 32

private theorem elided_ge3 (j : Nat) (hj : j ∈ PairStoreGap.lowerPairSlots) :
    3 ≤ StaggerTableLayout.slots[j]! := by
  simp only [PairStoreGap.lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem dualW_eq_dualOf (words : Nat → UInt256) (k : Nat) :
    Pair13WriterRaw.dualW words k = Shared32Scratch.dualOf words k := rfl

theorem tableJ_low32 (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) (j : Nat) (hj : j < 61) :
    (Pair13Memory.tableJ (WJ memory) j).toNat % 2 ^ 144
      = (scalars memory StaggerTableLayout.slots[j]!).toNat + GJ memory j * 2 ^ 32 := by
  have hk := StaggerTableLayout.slots_lt j hj
  have hmain : (Pair13Memory.tableJ (WJ memory) j).toNat % 2 ^ 144 % 2 ^ 32
      = (scalars memory StaggerTableLayout.slots[j]!).toNat := by
    rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 32 ≤ 144)), Pair13Memory.tableJ]
    simp only [WJ]
    by_cases he : j ∈ PairStoreGap.lowerPairSlots
    · rw [if_pos he, dualW_eq_dualOf,
        Shared32Scratch.dualOf_hi_low32 memory (lowW memory) highWord hlow _
          (elided_ge3 j he) hk,
        fanWord_eq_scalars memory _ hk]
    · rw [if_neg he, dualW_eq_dualOf,
        Shared32Scratch.dualOf_low32 memory (lowW memory) highWord _ hk,
        fanWord_eq_scalars memory _ hk]
  rw [GJ]
  omega

#print axioms fanWord_eq_scalars
#print axioms writer_memoryJ
#print axioms tableJ_low32

theorem copiedMemory_low (input : ByteArray) :
    (MachineState.readWord (copiedMemory input) 0).toNat % 2 ^ 144 < 2 ^ 32 := by
  refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
  unfold copiedMemory
  rw [Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by decide))]
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem copiedMemory_poolClear (input : ByteArray) :
    PairStoreGap.PoolClear (copiedMemory input) :=
  Shared32Scratch.copiedMemory_poolClear input

theorem copied_writer_memoryJ (input : ByteArray) :
    Pair13WriterRaw.writerMemory
      (Shared32Scratch.fanMemory (copiedMemory input) (lowW (copiedMemory input)) highWord)
      (WJ (copiedMemory input))
      = Pair13Memory.resultMemoryJ (copiedMemory input) (WJ (copiedMemory input)) :=
  writer_memoryJ _ (copiedMemory_gapClear input)

/-- **The table this route leaves is Ready**, with the junk budget `JunkBound` now asks for. -/
theorem table_readyJ (memory : ByteArray)
    (hlow : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32)
    (hpc : PairStoreGap.PoolClear memory) :
    StaggerMessage.Ready (Pair13Memory.resultMemoryJ memory (WJ memory)) (scalars memory) := by
  have hfan : PairStoreGap.PoolClear
      (Shared32Scratch.fanMemory memory (lowW memory) highWord) :=
    Shared32Scratch.fan_poolClear memory _ _ hpc
  rw [Pair13Memory.resultMemoryJ]
  refine JD8Table.ready_slot memory (Pair13Memory.tableJ (WJ memory)) (scalars memory)
    (GJ memory) (fun j hj => tableJ_low32 memory hlow j hj) (fun j hj => ?_) (fun j hj hnd => ?_)
  · have hk := StaggerTableLayout.slots_lt j hj
    rw [GJ, Pair13Memory.tableJ]
    simp only [WJ]
    by_cases he : j ∈ PairStoreGap.lowerPairSlots
    · rw [if_pos he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_hi_bound memory (lowW memory) highWord _
    · rw [if_neg he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_lo_bound memory (lowW memory) highWord hlow hfan _ hk
  · have hk := StaggerTableLayout.slots_lt j hj
    have hc : StaggerTableLayout.slots[j]! = 0 ∨ StaggerTableLayout.slots[j]! = 4 ∨
        StaggerTableLayout.slots[j]! = 5 ∨ StaggerTableLayout.slots[j]! = 6 ∨
        StaggerTableLayout.slots[j]! = 7 ∨ StaggerTableLayout.slots[j]! = 8 ∨
        StaggerTableLayout.slots[j]! = 9 ∨ StaggerTableLayout.slots[j]! = 11 := by
      simp only [StaggerAlgorithm.JDirty] at hnd
      omega
    rw [GJ, Pair13Memory.tableJ]
    simp only [WJ]
    by_cases he : j ∈ PairStoreGap.lowerPairSlots
    · rw [if_pos he, dualW_eq_dualOf]
      have h3 := elided_ge3 j he
      exact Shared32Scratch.dualOf_hi_zero memory (lowW memory) highWord _ (by omega)
    · rw [if_neg he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_lo_zero memory (lowW memory) highWord hlow _ hk hc

#print axioms tableJ_low32
#print axioms table_readyJ
#print axioms copied_writer_memoryJ
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
