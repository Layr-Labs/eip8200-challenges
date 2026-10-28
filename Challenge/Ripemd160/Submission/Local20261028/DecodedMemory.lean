import Challenge.Ripemd160.Submission.Local20261028.GeneralMessageReady
import Challenge.Ripemd160.Submission.Proofs.Bytecode.StaggerScratch

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.DecodedMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PairedScheduleMemory GeneralMessageReady GeneralMessageLayout
open RipemdMemoryBridge20261028

def scratch (m : ByteArray) (low high : UInt256) : ByteArray :=
  writeWord (writeWord m 162 high) 252 low

theorem mask32_toNat_mod (w : UInt256) : (Word.mask32 w).toNat = w.toNat % 2^32 := by
  rw [Word.mask32_toNat, show 0xffffffff = 2^32-1 by decide, Nat.and_two_pow_sub_one_eq_mod]

theorem entry_eq_pool (m : ByteArray) (low high : UInt256) (i : Nat) (hi : i < 16) :
    (entryWords (scratch m low high) i).toNat =
      (StaggerScratch.poolWord (StaggerScratch.scratchMemory m low high) i).toNat := by
  rw [entryWords_toNat, StaggerScratch.poolWord, mask32_toNat_mod, low_value]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  by_cases hl : i < 8
  · simp only [wordAddress, if_pos hl, scratch, StaggerScratch.scratchMemory, write_getD]
    rw [if_pos (by omega), if_pos (by omega)]
    congr 1
    omega
  · simp only [wordAddress, if_neg hl, scratch, StaggerScratch.scratchMemory, write_getD]
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega)]
    congr 1
    omega

theorem entry_eq_extracted (m : ByteArray) (p i : Nat) (hi : i < 16) :
    (entryWords (scratch m
      (PairedScheduleData.reversedWord (MachineState.readWord m p))
      (PairedScheduleData.reversedWord (MachineState.readWord m (p+32)))) i).toNat =
      (PairedScheduleData.extractedWord m p i).toNat := by
  rw [entry_eq_pool _ _ _ _ hi, StaggerScratch.poolWord_eq_extracted _ _ _ hi]

theorem entry_eq_expected (m : ByteArray) (p i : Nat) (hi : i < 16)
    (hbound : p+64 < 2^256) :
    (entryWords (scratch m
      (PairedScheduleData.reversedWord (MachineState.readWord m p))
      (PairedScheduleData.reversedWord (MachineState.readWord m (p+32)))) i).toNat =
      (ScheduleCorrect.expectedWord m (UInt256.ofNat p) i).toNat := by
  rw [entry_eq_extracted _ _ _ hi, PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hi hbound]

#print axioms entry_eq_expected
#print axioms entry_eq_pool
#print axioms entry_eq_extracted
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.DecodedMemory
