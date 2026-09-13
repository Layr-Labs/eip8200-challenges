import Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelCore
import Challenge.Ripemd160.Submission.Proofs.Bytecode.FastEmptyBlock
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PairedBlockModel

set_option warningAsError true
set_option maxRecDepth 20000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPreserve

open EvmSemantics
open EvmSemantics.EVM
open Challenge.EvmProof
open Challenge.Ripemd160.Submission.Proofs.Bytecode
open PairedScheduleMemory
open SentinelCore

/-- `FastEmptyBlock.emptyMemory` rewrites only the five hash words at
0x220..0x2bf, all at or above byte 544, so cell 16 is untouched. -/
theorem sentinel_emptyMemory (memory : ByteArray) (h : SentinelOK memory) :
    SentinelOK (FastEmptyBlock.emptyMemory memory) := by
  show SentinelOK (writeWord (writeWord (writeWord (writeWord (writeWord
    memory 0x220 _) 0x240 _) 0x260 _) 0x280 _) 0x2a0 _)
  exact sentinel_writeWord_disjoint _ _ _ (by norm_num)
    (sentinel_writeWord_disjoint _ _ _ (by norm_num)
      (sentinel_writeWord_disjoint _ _ _ (by norm_num)
        (sentinel_writeWord_disjoint _ _ _ (by norm_num)
          (sentinel_writeWord_disjoint _ _ _ (by norm_num) h))))

/-- The compression tail rewrites only the five hash words at 544..703. -/
theorem sentinel_tailResultMemory (memory : ByteArray) (q : PairedTailTrace.Frame)
    (h : SentinelOK memory) : SentinelOK (PairedTailTrace.resultMemory memory q) := by
  show SentinelOK (writeWord (writeWord (writeWord (writeWord (writeWord
    memory 672 _) 640 _) 608 _) 576 _) 544 _)
  exact sentinel_writeWord_disjoint _ _ _ (by norm_num)
    (sentinel_writeWord_disjoint _ _ _ (by norm_num)
      (sentinel_writeWord_disjoint _ _ _ (by norm_num)
        (sentinel_writeWord_disjoint _ _ _ (by norm_num)
          (sentinel_writeWord_disjoint _ _ _ (by norm_num) h))))

/-- The paired compression branch establishes the invariant with no incoming
hypothesis: its memory is the tail applied to `normalizedMemory`. -/
theorem sentinel_pairedResultState (s : State) (input : ByteArray) (i : Nat) :
    SentinelOK (PairedBlockModel.resultState s input i).memory :=
  sentinel_tailResultMemory _ _ (sentinel_normalizedMemory _ _)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPreserve
