import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.JD8Table
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable ColdHighPaddingMemory

/-- The table the normal loader leaves under this artifact: the SLOT-indexed image, because
an elided slot and its pair carry the same schedule word with different junk. -/
def tableMemory (input : ByteArray) (i : Nat) : ByteArray :=
  Pair13Memory.resultMemoryJ (finalMemory input i)
    (Shared32Scratch.wordsJ (finalMemory input i)
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i)))
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i + 32))))

theorem extracted_words (input : ByteArray) (hfit : CalldataFits input) (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i)
    (k : Nat) (hk : k<16) :
    PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i) k = Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord (finalMemory input i) (DriverTrace.messageOffsetWord i) k = _
  rw [finalMemory_blockAt input hfit i hi hh k hk,blockWords_eq_readLE32 input i k hk]

private theorem dualW_eq_dualOf (words : Nat → UInt256) (k : Nat) :
    Pair13WriterRaw.dualW words k = Shared32Scratch.dualOf words k := rfl

private theorem elided_ge3 (j : Nat) (hj : j ∈ PairStoreGap.lowerPairSlots) :
    3 ≤ StaggerTableLayout.slots[j]! := by
  simp only [PairStoreGap.lowerPairSlots, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

theorem ready (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size)
    (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i) :
    StaggerMessage.Ready (tableMemory input i) (blockWords input i) := by
  have hlow : (MachineState.readWord (finalMemory input i) 0).toNat % 2 ^ 144 < 2 ^ 32 := by
    rw [finalMemory_lowClear input hfit hpositive i (by omega)]
    decide
  have hpc := finalMemory_poolClear input hfit hpositive i (by omega)
  have hfan := Shared32Scratch.fan_poolClear (finalMemory input i)
    (PairedScheduleData.reversedWord
      (MachineState.readWord (finalMemory input i) (messagePointer i)))
    (PairedScheduleData.reversedWord
      (MachineState.readWord (finalMemory input i) (messagePointer i + 32))) hpc
  have hblk : ∀ k, k < 16 →
      (Shared32Scratch.fanWord
        (PairedScheduleData.reversedWord
          (MachineState.readWord (finalMemory input i) (messagePointer i)))
        (PairedScheduleData.reversedWord
          (MachineState.readWord (finalMemory input i) (messagePointer i + 32))) k).toNat
        = (blockWords input i k).toNat := by
    intro k hk
    rw [Shared32Scratch.fanWord,
      (StaggerScratch.poolWord_eq (finalMemory input i) _ _ k hk).symm,
      StaggerScratch.poolWord_eq_extracted (finalMemory input i) (messagePointer i) k hk,
      extracted_words input hfit i hi hh k hk, Word.ofUInt32_toNat]
  rw [tableMemory, Pair13Memory.resultMemoryJ]
  refine JD8Table.ready_slot (finalMemory input i) (Pair13Memory.tableJ _)
    (blockWords input i)
    (fun j => ((Pair13Memory.tableJ (Shared32Scratch.wordsJ (finalMemory input i)
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i)))
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i + 32)))) j).toNat
      % 2 ^ 144) / 2 ^ 32) (fun j hj => ?_) (fun j hj => ?_) (fun j hj hnd => ?_)
  · have hk := StaggerTableLayout.slots_lt j hj
    have hmain : (Pair13Memory.tableJ (Shared32Scratch.wordsJ (finalMemory input i)
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i)))
      (PairedScheduleData.reversedWord
        (MachineState.readWord (finalMemory input i) (messagePointer i + 32)))) j).toNat
        % 2 ^ 144 % 2 ^ 32 = (blockWords input i StaggerTableLayout.slots[j]!).toNat := by
      rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega : 32 ≤ 144)), Pair13Memory.tableJ]
      by_cases he : j ∈ PairStoreGap.lowerPairSlots
      · rw [if_pos he, dualW_eq_dualOf,
          Shared32Scratch.dualOf_hi_low32 (finalMemory input i) _ _ hlow _ (elided_ge3 j he) hk,
          hblk _ hk]
      · rw [if_neg he, dualW_eq_dualOf,
          Shared32Scratch.dualOf_low32 (finalMemory input i) _ _ _ hk, hblk _ hk]
    omega
  · have hk := StaggerTableLayout.slots_lt j hj
    rw [Pair13Memory.tableJ]
    by_cases he : j ∈ PairStoreGap.lowerPairSlots
    · rw [if_pos he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_hi_bound (finalMemory input i) _ _ _
    · rw [if_neg he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_lo_bound (finalMemory input i) _ _ hlow hfan _ hk
  · have hk := StaggerTableLayout.slots_lt j hj
    have hc : StaggerTableLayout.slots[j]! = 0 ∨ StaggerTableLayout.slots[j]! = 4 ∨
        StaggerTableLayout.slots[j]! = 5 ∨ StaggerTableLayout.slots[j]! = 6 ∨
        StaggerTableLayout.slots[j]! = 7 ∨ StaggerTableLayout.slots[j]! = 8 ∨
        StaggerTableLayout.slots[j]! = 9 ∨ StaggerTableLayout.slots[j]! = 11 := by
      simp only [StaggerAlgorithm.JDirty] at hnd
      omega
    rw [Pair13Memory.tableJ]
    by_cases he : j ∈ PairStoreGap.lowerPairSlots
    · rw [if_pos he, dualW_eq_dualOf]
      have h3 := elided_ge3 j he
      exact Shared32Scratch.dualOf_hi_zero (finalMemory input i) _ _ _ (by omega)
    · rw [if_neg he, dualW_eq_dualOf]
      exact Shared32Scratch.dualOf_lo_zero (finalMemory input i) _ _ hlow _ hk hc

#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
