import Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolShapeV2
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
    (hc : ∀ i, i < 16 → (words i).toNat < 2^112) :
    PoolRawWriter.writerMemory m (Pair13WriterRaw.dualW words) =
      Pair13WriterRaw.writerMemory m words := by
  exact Pair13WriterRaw.raw_eq_writer m words hc

theorem reference_eq_writer (m : ByteArray) (lo hi : UInt256)
    (hlow : (MachineState.readWord m 0).toNat % 2^144 < 2^32) :
    PoolShape.resultMemory true m lo hi =
      Pair13WriterRaw.writerMemory (Shared32Scratch.fanMemory m lo hi)
        (StaggerScratch.poolWord (StaggerScratch.scratchMemory m lo hi)) := by
  unfold PoolShape.resultMemory PoolShape.poolValue
  rw [if_pos rfl]
  rw [writer_congr _ _ (Pair13WriterRaw.dualW
    (StaggerScratch.poolWord (StaggerScratch.scratchMemory m lo hi)))
    (fun i hi16 => Shared32Scratch.fan_poolWord m lo hi hlow i hi16)]
  apply writer_dual
  intro i hi16
  rw [StaggerScratch.poolWord_eq _ _ _ _ hi16]
  exact Nat.lt_trans (Shared32Scratch.fanWord_lt lo hi i) (by norm_num)

def dataMemory (m : ByteArray) (p : Nat) : ByteArray :=
  PoolShapeV2.resultMemoryV2 m
    (PairedScheduleData.reversedWord (MachineState.readWord m p))
    (PairedScheduleData.reversedWord (MachineState.readWord m (p+32)))

/-- The composed pool masks words 0..3, so its word function is `poolWord`, which is
`extractedWord` exactly -- every one of the sixteen is a clean 32-bit scalar.  The image is
byte-equal to the clean table everywhere except the four bytes [50,54) that the dropped store
at 36 leaves behind. -/
theorem reference_data_getD (memory : ByteArray) (p : Nat)
    (hlow : (MachineState.readWord memory 0).toNat % 2^144 < 2^32)
    (hgap : PairStoreGap.GapClear memory) (q : Nat) (hq : q < 50 ∨ 54 ≤ q) :
    (PoolShape.resultMemory true memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory p))
      (PairedScheduleData.reversedWord (MachineState.readWord memory (p+32))))[q]?.getD 0 =
      (StaggerTableLayout.resultMemory0 memory
        (PairedScheduleData.extractedWord memory p))[q]?.getD 0 := by
  rw [reference_eq_writer _ _ _ hlow]
  let words := PairedScheduleData.extractedWord memory p
  let wordsR := StaggerScratch.poolWord (StaggerScratch.scratchMemory memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32))))
  let scratch := Shared32Scratch.fanMemory memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord memory (p + 32)))
  have hclean : ∀ i, 3 ≤ i → i < 16 → (words i).toNat < 2 ^ 32 := fun i _ _ =>
    PairedScheduleData.extractedWord_bound memory p i
  have hscratchgap : PairStoreGap.GapClear scratch :=
    Shared32Scratch.fanMemory_gapClear memory _ _ hgap
  have hcleanR : ∀ i, i < 16 → (wordsR i).toNat < 2 ^ 112 := by
    intro i hi16
    show (StaggerScratch.poolWord (StaggerScratch.scratchMemory memory _ _) i).toNat < _
    rw [StaggerScratch.poolWord_eq_extracted memory p i hi16]
    exact Nat.lt_trans (PairedScheduleData.extractedWord_bound memory p i) (by norm_num)
  have hm : (Pair13WriterRaw.writerMemory scratch wordsR)[q]?.getD 0
      = (StaggerTableLayout.resultMemory0 scratch words)[q]?.getD 0 := by
    rw [Pair13Memory.writerMemory_getD_resultMemoryD scratch wordsR hcleanR hscratchgap q hq,
      Pair13Memory.resultMemoryD_congr_mod _ wordsR words
        (by simp only [Pair13WriterRaw.dualW]
            rw [show wordsR 6 = words 6 from
              StaggerScratch.poolWord_eq_extracted memory p 6 (by decide)])
        (fun j _ hj => by
          simp only [StaggerTableLayout.tableWords]
          exact congrArg (fun w : UInt256 => w.toNat % 2 ^ 144)
            (StaggerScratch.poolWord_eq_extracted memory p _
              (StaggerTableLayout.slots_lt j hj))),
      Pair13Memory.resultMemoryD_eq _ _ (hclean 6 (by decide) (by decide))]
  have herase : StaggerTableLayout.resultMemory0 scratch words = StaggerTableLayout.resultMemory0 memory words :=
    congrArg
      (fun m => PairedScheduleMemory.writeWord m 0
        (StaggerTableLayout.dualLane (words 6)))
      (Shared32Scratch.erase_fan memory (StaggerTableLayout.tableWords words) _ _)
  exact hm.trans (congrArg (fun m => m[q]?.getD 0) herase)


#print axioms reference_data_getD
end Challenge.Ripemd160.Submission.Proofs.Bytecode.PoolReference
