import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolInvariant
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Scratch
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerMessage

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open Shared32Scratch

def highScalar (k : Nat) : Nat := if k = 8 then 128 else if k = 14 then 256 else 0

def words (memory : ByteArray) (k : Nat) : UInt256 :=
  if k < 8 then StaggerScratch.dirtyWord memory 1056 k else UInt256.ofNat (highScalar k)

def scalars (memory : ByteArray) (k : Nat) : UInt32 :=
  UInt32.ofNat (if k < 8 then (PairedScheduleData.extractedWord memory 1056 k).toNat
    else highScalar k)

theorem words_split (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat = (scalars memory k).toNat +
        (words memory k).toNat / 2 ^ 32 * 2 ^ 32 ∧
      (words memory k).toNat / 2 ^ 32 < 2 ^ 64 ∧
      (k ≠ 2 → (words memory k).toNat / 2 ^ 32 < 2 ^ 32) ∧
      (¬ (k = 1 ∨ k = 2) → (words memory k).toNat / 2 ^ 32 = 0) := by
  by_cases hl : k < 8
  · have hs := StaggerScratch.dirtyWord_split memory 1056 k
    have hb := PairedScheduleData.extractedWord_bound memory 1056 k
    simpa only [words, scalars, if_pos hl, UInt32.toNat_ofNat',
      show UInt32.size = 2 ^ 32 by rfl, Nat.mod_eq_of_lt hb] using hs
  · interval_cases k <;> norm_num [words, scalars, highScalar, Word.word_toNat_ofNat]

theorem words_clean (memory : ByteArray) (k : Nat) (hk0 : 3 ≤ k) (hk1 : k < 16) :
    (words memory k).toNat < 2 ^ 32 := by
  by_cases hl : k < 8
  · have hd : ¬(k = 1 ∨ k = 2) := by omega
    rw [words, if_pos hl, StaggerScratch.dirtyWord, if_neg hd]
    exact PairedScheduleData.extractedWord_bound memory 1056 k
  · interval_cases k <;> norm_num [words, highScalar, Word.word_toNat_ofNat]

/-- The words the S51 pool actually loads.  For `3 ≤ k` this is EXACTLY `words memory k`;
for `k < 3` it may carry the previous block's slot-0 dual lane above bit 144. -/
def wordsRaw (memory : ByteArray) (k : Nat) : UInt256 :=
  StaggerScratch.poolWordD
    (StaggerScratch.scratchMemory memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord) k

theorem pool_wordsRaw (memory : ByteArray) (k : Nat) :
    StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord) k =
      wordsRaw memory k := rfl

theorem wordsRaw_eq_high (memory : ByteArray) (k : Nat) (hk0 : 3 ≤ k) (hk1 : k < 16) :
    wordsRaw memory k = words memory k := by
  by_cases hl : k < 8
  · rw [wordsRaw, words, if_pos hl, pool_lower_high_irrelevant memory 1056 k highWord hl]
    exact StaggerScratch.poolWordD_eq_dirty_high memory 1056 k hk1 (by omega)
  · rw [wordsRaw, words, if_neg hl]
    exact pool_upper memory _ k (by omega) hk1

theorem wordsRaw_clean (memory : ByteArray) (k : Nat) (hk0 : 3 ≤ k) (hk1 : k < 16) :
    (wordsRaw memory k).toNat < 2 ^ 32 := by
  rw [wordsRaw_eq_high memory k hk0 hk1]
  exact words_clean memory k hk0 hk1

theorem wordsRaw_mod (memory : ByteArray) (k : Nat) (hk : k < 16)
    (hzero : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    (wordsRaw memory k).toNat % 2 ^ 144 = (words memory k).toNat % 2 ^ 144 := by
  by_cases hl : k < 8
  · rw [wordsRaw, words, if_pos hl]
    exact pool_lower memory 1056 k highWord hl hzero
  · rw [wordsRaw_eq_high memory k (by omega) hk]

theorem table_ready (memory : ByteArray) :
    StaggerMessage.Ready (StaggerTableLayout.resultMemory memory (words memory))
      (scalars memory) := by
  exact StaggerMessage.ready_junk memory (words memory) (scalars memory)
    (fun k => (words memory k).toNat / 2 ^ 32)
    (fun k hk => (words_split memory k hk).1)
    (fun k hk => (words_split memory k hk).2.1)
    (fun k hk h2 => Nat.lt_trans ((words_split memory k hk).2.2.1 h2) (by decide))
    (fun k hk h2 _ => (words_split memory k hk).2.2.1 h2)
    (fun k hk hd => by
      have hd' : ¬ (k = 1 ∨ k = 2) := fun h =>
        hd (h.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (Or.inl h2)))
      have hz := (words_split memory k hk).2.2.2 hd'
      exact ⟨by rw [hz]; decide, fun _ => hz⟩)

theorem writer_memory (memory : ByteArray) (hgap : PairStoreGap.GapClear memory)
    (hzero : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    Pair13WriterRaw.writerMemory
      (fanMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord)
      (wordsRaw memory) = StaggerTableLayout.resultMemory0 memory (words memory) := by
  rw [Pair13Memory.writerMemory_eq_resultMemoryD _ _
      (fun i h1 h2 => wordsRaw_clean memory i h1 h2) (fanMemory_gapClear _ _ _ hgap),
    Pair13Memory.resultMemoryD_congr_mod _ (wordsRaw memory) (words memory)
      (by simp only [Pair13WriterRaw.dualW,
        wordsRaw_eq_high memory 6 (by decide) (by decide)])
      (fun j _ hj => by
        simp only [StaggerTableLayout.tableWords]
        exact wordsRaw_mod memory _ (StaggerTableLayout.slots_lt j hj) hzero),
    Pair13Memory.resultMemoryD_eq _ _ (words_clean memory 6 (by decide) (by decide))]
  exact congrArg
    (fun m => PairedScheduleMemory.writeWord m 0
      (StaggerTableLayout.dualLane (words memory 6)))
    (erase_fan memory (StaggerTableLayout.tableWords (words memory)) _ _)

theorem copiedMemory_low (input : ByteArray) :
    (MachineState.readWord (copiedMemory input) 0).toNat % 2 ^ 144 < 2 ^ 32 := by
  refine Nat.lt_of_le_of_lt (Nat.mod_le _ _) ?_
  unfold copiedMemory
  rw [Memory.readWord_writeBytes_disjoint _ _ _ _ (Or.inl (by decide))]
  unfold MachineState.readWord
  rw [← Bytes.bytesNat_toList, Bytes.readPadded_toList]
  simp only [YulEvmCompiler.ByteArray.toList_eq_data]
  decide

theorem copied_writer_memory (input : ByteArray) :
    Pair13WriterRaw.writerMemory
      (fanMemory (copiedMemory input)
        (PairedScheduleData.reversedWord (MachineState.readWord (copiedMemory input) 1056)) highWord)
      (wordsRaw (copiedMemory input)) =
      StaggerTableLayout.resultMemory0 (copiedMemory input) (words (copiedMemory input)) :=
  writer_memory _ (copiedMemory_gapClear input) (copiedMemory_low input)

def tableMemory (memory : ByteArray) : ByteArray :=
  PoolShape.resultMemory false memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord

theorem tableMemory_ready (memory : ByteArray) (hc : PoolShape.Clear memory)
    (scalar : Nat → UInt32)
    (hr : StaggerMessage.Ready (StaggerTableLayout.resultMemory0 memory (words memory)) scalar) :
    StaggerMessage.Ready (tableMemory memory) scalar := by
  apply PoolInvariant.ready _ _ _ hc
  rw [PoolReference.reference_eq_writer _ _ _ (PoolInvariant.clear_low memory hc)]
  change StaggerMessage.Ready (Pair13WriterRaw.writerMemory
    (fanMemory memory (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord)
    (wordsRaw memory)) scalar
  rw [writer_memory memory (PoolInvariant.clear_gap memory hc) (PoolInvariant.clear_low memory hc)]
  exact hr

#print axioms table_ready
#print axioms wordsRaw_eq_high
#print axioms wordsRaw_mod
#print axioms copied_writer_memory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
