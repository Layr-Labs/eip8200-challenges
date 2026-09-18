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
  if k < 8 then PairedScheduleData.extractedWord memory 1056 k
  else UInt256.ofNat (highScalar k)

def scalars (memory : ByteArray) (k : Nat) : UInt32 :=
  UInt32.ofNat (if k < 8 then (PairedScheduleData.extractedWord memory 1056 k).toNat
    else highScalar k)

theorem words_lt (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat < 2 ^ 32 := by
  by_cases hl : k < 8
  · rw [words, if_pos hl]
    exact PairedScheduleData.extractedWord_bound memory 1056 k
  · rw [words, if_neg hl]
    interval_cases k <;> norm_num [highScalar, Word.word_toNat_ofNat]

theorem words_div (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat / 2 ^ 32 = 0 :=
  Nat.div_eq_of_lt (words_lt memory k hk)

theorem words_eq_scalars (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat = (scalars memory k).toNat := by
  by_cases hl : k < 8
  · rw [words, scalars, if_pos hl, UInt32.toNat_ofNat', if_pos hl,
      Nat.mod_eq_of_lt (PairedScheduleData.extractedWord_bound memory 1056 k)]
  · rw [words, scalars, if_neg hl]
    interval_cases k <;> norm_num [highScalar, Word.word_toNat_ofNat]

theorem words_split (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (words memory k).toNat = (scalars memory k).toNat +
        (words memory k).toNat / 2 ^ 32 * 2 ^ 32 ∧
      (words memory k).toNat / 2 ^ 32 < 2 ^ 64 ∧
      (k ≠ 2 → (words memory k).toNat / 2 ^ 32 < 2 ^ 32) ∧
      (¬ (k = 1 ∨ k = 2) → (words memory k).toNat / 2 ^ 32 = 0) := by
  have hz := words_div memory k hk
  refine ⟨by rw [hz, words_eq_scalars memory k hk]; omega, by rw [hz]; norm_num,
    fun _ => by rw [hz]; norm_num, fun _ => hz⟩

theorem words_clean (memory : ByteArray) (k : Nat) (_hk0 : 3 ≤ k) (hk1 : k < 16) :
    (words memory k).toNat < 2 ^ 32 := words_lt memory k hk1

/-- The words the S51 pool actually loads.  For `3 ≤ k` this is EXACTLY `words memory k`;
for `k < 3` it may carry the previous block's slot-0 dual lane above bit 144. -/
def wordsRaw (memory : ByteArray) (k : Nat) : UInt256 :=
  StaggerScratch.poolWord
    (StaggerScratch.scratchMemory memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord) k

theorem pool_wordsRaw (memory : ByteArray) (k : Nat) :
    StaggerScratch.poolWord
      (StaggerScratch.scratchMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord) k =
      wordsRaw memory k := rfl

theorem wordsRaw_eq_words (memory : ByteArray) (k : Nat) (hk1 : k < 16) :
    wordsRaw memory k = words memory k := by
  rw [wordsRaw, StaggerScratch.poolWord_eq _ _ _ _ hk1, words]
  by_cases hl : k < 8
  · rw [if_pos hl, if_pos hl,
      ← StaggerScratch.poolWord_eq_extracted memory 1056 k hk1,
      StaggerScratch.poolWord_eq _ _ _ _ hk1, if_pos hl]
  · rw [if_neg hl, if_neg hl, highWord, highScalar]
    interval_cases k <;> rfl

theorem wordsRaw_eq_high (memory : ByteArray) (k : Nat) (_hk0 : 3 ≤ k) (hk1 : k < 16) :
    wordsRaw memory k = words memory k := wordsRaw_eq_words memory k hk1

theorem wordsRaw_lt (memory : ByteArray) (k : Nat) (hk : k < 16) :
    (wordsRaw memory k).toNat < 2 ^ 112 := by
  rw [wordsRaw_eq_words memory k hk]
  exact Nat.lt_trans (words_lt memory k hk) (by norm_num)

theorem wordsRaw_mod (memory : ByteArray) (k : Nat) (hk : k < 16)
    (_hzero : (MachineState.readWord memory 0).toNat % 2 ^ 144 < 2 ^ 32) :
    (wordsRaw memory k).toNat % 2 ^ 144 = (words memory k).toNat % 2 ^ 144 := by
  rw [wordsRaw_eq_words memory k hk]

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
    (q : Nat) (hq : q < 50 ∨ 54 ≤ q) :
    (Pair13WriterRaw.writerMemory
      (fanMemory memory
        (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord)
      (wordsRaw memory))[q]?.getD 0
      = (StaggerTableLayout.resultMemory0 memory (words memory))[q]?.getD 0 := by
  rw [Pair13Memory.writerMemory_getD_resultMemoryD _ _
      (fun i h1 => wordsRaw_lt memory i h1) (fanMemory_gapClear _ _ _ hgap) q hq,
    Pair13Memory.resultMemoryD_congr_mod _ (wordsRaw memory) (words memory)
      (by simp only [Pair13WriterRaw.dualW]
          rw [wordsRaw_eq_words memory 6 (by decide)])
      (fun j _ hj => by
        simp only [StaggerTableLayout.tableWords]
        exact congrArg (fun w : UInt256 => w.toNat % 2 ^ 144)
          (wordsRaw_eq_words memory _ (StaggerTableLayout.slots_lt j hj))),
    Pair13Memory.resultMemoryD_eq _ _ (words_clean memory 6 (by decide) (by decide))]
  exact congrArg
    (fun m => (PairedScheduleMemory.writeWord m 0
      (StaggerTableLayout.dualLane (words memory 6)))[q]?.getD 0)
    (erase_fan memory (StaggerTableLayout.tableWords (words memory)) _ _)

def tableMemory (memory : ByteArray) : ByteArray :=
  PoolShapeV2.resultMemoryV2 memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord

theorem tableMemory_ready (memory : ByteArray) (hc : PoolShape.Clear memory)
    (hc2 : PoolShapeV2.ClearV2 memory) (scalar : Nat → UInt32)
    (hr : StaggerMessage.Ready (StaggerTableLayout.resultMemory0 memory (words memory)) scalar) :
    StaggerMessage.Ready (tableMemory memory) scalar := by
  apply PoolInvariant.ready memory memory _ _ hc2 hc
  rw [PoolReference.reference_eq_writer _ _ _ (PoolInvariant.clear_low memory hc)]
  change StaggerMessage.Ready (Pair13WriterRaw.writerMemory
    (fanMemory memory (PairedScheduleData.reversedWord (MachineState.readWord memory 1056)) highWord)
    (wordsRaw memory)) scalar
  refine PoolInvariant.ready_of_gap _ _ _
    (fun q hq => writer_memory memory (PoolInvariant.clear_gap memory hc) q hq) ?_ hr
  rw [writer_memory memory (PoolInvariant.clear_gap memory hc) 54 (by omega)]
  exact Pair13Memory.resultMemory0_byte54 memory _
    (fun k hk => Nat.lt_trans (words_lt memory k hk) (by norm_num))

#print axioms table_ready
#print axioms wordsRaw_eq_high
#print axioms wordsRaw_mod
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Shared32Table
