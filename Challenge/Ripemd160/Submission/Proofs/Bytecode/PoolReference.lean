import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShape
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Pair13Memory

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

theorem writer_congr (m : ByteArray) (f g : Nat → UInt256)
    (h : ∀ i, i < 16 → f i = g i) :
    PoolRawWriter.writerMemory m f = PoolRawWriter.writerMemory m g := by
  unfold PoolRawWriter.writerMemory
  congr 1
  rw [PoolShape.rawWrites_eq, PoolShape.rawWrites_eq]
  apply List.map_congr_left
  intro x hx
  have hx' : ∀ x ∈ PoolShape.writes, x.2 < 16 := by decide
  rw [h x.2 (hx' x hx)]

theorem writer_dual (m : ByteArray) (words : Nat → UInt256)
    (hc : ∀ i, 3 ≤ i → i < 16 → (words i).toNat < 2^32) :
    PoolRawWriter.writerMemory m (Pair13WriterRaw.dualW words) =
      Pair13WriterRaw.writerMemory m words := by
  exact Pair13WriterRaw.raw_eq_writer m words hc

theorem reference_eq_writer (m : ByteArray) (lo hi : UInt256)
    (hlow : (MachineState.readWord m 0).toNat % 2^144 < 2^32) :
    PoolShape.resultMemory true m lo hi =
      Pair13WriterRaw.writerMemory (Shared32Scratch.fanMemory m lo hi)
        (StaggerScratch.poolWordD (StaggerScratch.scratchMemory m lo hi)) := by
  unfold PoolShape.resultMemory PoolShape.poolValue
  rw [if_pos rfl]
  rw [writer_congr _ _ (Pair13WriterRaw.dualW
    (StaggerScratch.poolWordD (StaggerScratch.scratchMemory m lo hi)))
    (fun i hi16 => Shared32Scratch.fan_poolWord m lo hi hlow i hi16)]
  apply writer_dual
  intro i hi3 hi16
  rw [StaggerScratch.poolWordD, if_neg (by omega), StaggerScratch.poolWord_eq _ _ _ _ hi16]
  exact Shared32Scratch.fanWord_lt lo hi i

def dataMemory (m : ByteArray) (p : Nat) : ByteArray :=
  PoolShape.resultMemory false m
    (PairedScheduleData.reversedWord (MachineState.readWord m p))
    (PairedScheduleData.reversedWord (MachineState.readWord m (p+32)))

theorem reference_data_eq (memory : ByteArray) (p : Nat)
    (hlow : (MachineState.readWord memory 0).toNat % 2^144 < 2^32)
    (hgap : PairStoreGap.GapClear memory) :
    PoolShape.resultMemory true memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory p))
      (PairedScheduleData.reversedWord (MachineState.readWord memory (p+32))) =
      StaggerTableLayout.resultMemory0 memory (StaggerScratch.dirtyWord memory p) := by
  rw [reference_eq_writer _ _ _ hlow]
  let words := StaggerScratch.dirtyWord memory p
  let wordsR := StaggerScratch.poolWordD (StaggerScratch.scratchMemory memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32))))
  let scratch := Shared32Scratch.fanMemory memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))
  have hclean : ∀ i, 3 ≤ i → i < 16 → (words i).toNat < 2 ^ 32 := by
    intro i hi _
    have hnot : ¬ (i = 1 ∨ i = 2) := by omega
    simp only [words, StaggerScratch.dirtyWord, if_neg hnot]
    exact PairedScheduleData.extractedWord_bound memory p i
  have hscratchgap : PairStoreGap.GapClear scratch :=
    Shared32Scratch.fanMemory_gapClear memory _ _ hgap
  have hcleanR : ∀ i, 3 ≤ i → i < 16 → (wordsR i).toNat < 2 ^ 32 := by
    intro i hi hi16
    have hnot : ¬ (i = 1 ∨ i = 2) := by omega
    show (StaggerScratch.poolWordD (StaggerScratch.scratchMemory memory _ _) i).toNat < _
    rw [StaggerScratch.poolWordD_eq_dirty_high memory p i hi16 (by omega),
      StaggerScratch.dirtyWord, if_neg hnot]
    exact PairedScheduleData.extractedWord_bound memory p i
  have hm : Pair13WriterRaw.writerMemory scratch wordsR
      = StaggerTableLayout.resultMemory0 scratch words := by
    rw [Pair13Memory.writerMemory_eq_resultMemoryD scratch wordsR hcleanR hscratchgap,
      Pair13Memory.resultMemoryD_congr_mod _ wordsR words
        (by simp only [Pair13WriterRaw.dualW]
            rw [show wordsR 6 = words 6 from
              StaggerScratch.poolWordD_eq_dirty_high memory p 6 (by decide) (by decide)])
        (fun j _ hj => by
          simp only [StaggerTableLayout.tableWords]
          exact StaggerScratch.poolWordD_eq_dirty memory p _
            (StaggerTableLayout.slots_lt j hj) hlow),
      Pair13Memory.resultMemoryD_eq _ _ (hclean 6 (by decide) (by decide))]
  have herase : StaggerTableLayout.resultMemory0 scratch words = StaggerTableLayout.resultMemory0 memory words :=
    congrArg
      (fun m => PairedScheduleMemory.writeWord m 0
        (StaggerTableLayout.dualLane (words 6)))
      (Shared32Scratch.erase_fan memory (StaggerTableLayout.tableWords words) _ _)
  exact hm.trans herase


#print axioms reference_data_eq
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
