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

/-- `FastEmptyBlock.emptyMemory` rewrites only the five hash words at 0x20..0xa0,
every one of which ends at or below 192.  Cell 16 is untouched, so the pair is
preserved from the incoming state. -/
theorem sentinel_emptyMemory (memory : ByteArray) (h : SentinelOK memory) :
    SentinelOK (FastEmptyBlock.emptyMemory memory) := by
  show SentinelOK (writeWord (writeWord (writeWord (writeWord (writeWord
    memory 0x20 _) 0x40 _) 0x60 _) 0x80 _) 0xa0 _)
  exact sentinel_writeWord_disjoint _ _ _ (by norm_num)
    (sentinel_writeWord_disjoint _ _ _ (by norm_num)
      (sentinel_writeWord_disjoint _ _ _ (by norm_num)
        (sentinel_writeWord_disjoint _ _ _ (by norm_num)
          (sentinel_writeWord_disjoint _ _ _ (by norm_num) h))))

/-- The startup tail rewrites only the five hash words at 32..160, so it too is
disjoint from cell 16. -/
theorem sentinel_tailResultMemory (memory : ByteArray) (q : PairedTailTrace.Frame)
    (h : SentinelOK memory) : SentinelOK (PairedTailTrace.resultMemory memory q) := by
  show SentinelOK (writeWord (writeWord (writeWord (writeWord (writeWord
    memory 160 _) 128 _) 96 _) 64 _) 32 _)
  exact sentinel_writeWord_disjoint _ _ _ (by norm_num)
    (sentinel_writeWord_disjoint _ _ _ (by norm_num)
      (sentinel_writeWord_disjoint _ _ _ (by norm_num)
        (sentinel_writeWord_disjoint _ _ _ (by norm_num)
          (sentinel_writeWord_disjoint _ _ _ (by norm_num) h))))

/-- The paired compression branch establishes the pair with NO incoming
hypothesis: its memory is the tail applied to `normalizedMemory`, and
`normalizedMemory` supplies both halves on its own. -/
theorem sentinel_pairedResultState (s : State) (input : ByteArray) (i : Nat) :
    SentinelOK (PairedBlockModel.resultState s input i).memory :=
  sentinel_tailResultMemory _ _ (sentinel_normalizedMemory _ _)

end Challenge.Ripemd160.Submission.Proofs.Bytecode.SentinelPreserve
