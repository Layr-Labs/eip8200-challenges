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

theorem pool_words (memory : ByteArray) (k : Nat) (hk : k < 16)
    (hzero : (MachineState.readWord memory 0).toNat < 2 ^ 32) :
    StaggerScratch.poolWordD
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1120)) highWord) k =
      words memory k := by
  by_cases hl : k < 8
  · rw [words, if_pos hl]
    exact pool_lower memory 1120 k highWord hl hzero
  · rw [words, if_neg hl]
    exact pool_upper memory _ k (by omega) hk

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

theorem writer_memory (memory : ByteArray) (hgap : PairStoreGap.GapClear memory) :
    Pair13WriterRaw.writerMemory
      (fanMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1120)) highWord)
      (words memory) = StaggerTableLayout.resultMemory memory (words memory) := by
  rw [Pair13Memory.writerMemory_eq_resultMemory _ _ (words_clean memory)
    (fanMemory_gapClear _ _ _ hgap)]
  exact erase_fan memory _ _ _

theorem copied_writer_memory (input : ByteArray) :
    Pair13WriterRaw.writerMemory
      (fanMemory (copiedMemory input)
        (PairedScheduleData.reversedWord (MachineState.readWord (copiedMemory input) 1120)) highWord)
      (words (copiedMemory input)) =
      StaggerTableLayout.resultMemory (copiedMemory input) (words (copiedMemory input)) :=
  writer_memory _ (copiedMemory_gapClear input)

#print axioms table_ready
#print axioms pool_words
#print axioms copied_writer_memory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
