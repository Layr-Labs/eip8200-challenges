import Challenge.Ripemd160.Submission.Local20261028.GeneralMessageReady
import Challenge.Ripemd160.Submission.Local20261028.FirstMemory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstMessageReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RipemdMemoryBridge20261028 RipemdSubmissionTables20261028
open GeneralMessageLayout
open PairedLaneUInt256Bridge Paired144Core

open GeneralMessageReady
theorem low_read (s : State) (continuation : UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstMemory.initial (FirstMemory.value s.memory))
    (slot : Nat) (hslot : slot < 61) :
    (CoreModel.load (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory (18*slot)).toNat % 2^32 =
      (entryWords s.memory StaggerTableLayout.slots[slot]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [low_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [FirstMemory.actual_bytes s continuation rho hz, FirstMemory.low_sources ⟨slot,hslot⟩ ⟨j,hj⟩]
  exact (hz _).symm

theorem high_read (s : State) (continuation : UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstMemory.initial (FirstMemory.value s.memory))
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat / 2^144 % 2^32 =
      (entryWords s.memory Crypto.Ripemd160.rP[i+3]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [high_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [FirstMemory.actual_bytes s continuation rho hz, FirstMemory.high_sources ⟨i,hi⟩ ⟨j,hj⟩]
  exact (hz _).symm

theorem raw_slack (s : State) (continuation : UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstMemory.initial (FirstMemory.value s.memory))
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨hl,hu,hzero⟩ := FirstMemory.barrier_sources ⟨i,hi⟩
  change 14 ≤ barriers[i]! at hl
  change barriers[i]! ≤ 26 at hu
  apply zero_byte_slack _ barriers[i]! hl hu
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [PoolByte.read _ _ _ (by omega), FirstMemory.actual_bytes s continuation rho hz, hzero]
  rfl

/-- The actual specialized-table output satisfies the inherited compressor's
    semantic contract, including the repaired terminal round. -/
theorem ready (s : State) (continuation : UInt256) (rho : List UInt256)
    (hz : Matches s.memory FirstMemory.initial (FirstMemory.value s.memory)) :
    CoreMessage.Ready (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory (entryWords s.memory) := by
  constructor
  · intro i hi
    obtain ⟨_,hslot,hleft,_⟩ := StaggerTableLayout.layout_valid ⟨i,hi⟩
    have hlo := low_read s continuation rho hz StaggerTableLayout.pairIndices[i]! hslot
    rw [hleft] at hlo
    have hhi := high_read s continuation rho hz i hi
    have hs := raw_slack s continuation rho hz i hi
    apply Or.inr
    by_cases ht : i=76
    · subst i
      simp only [CoreModel.message, if_pos rfl, ite_true]
      have hm := RipemdSubmissionTerminalRepair20261028.masked_small
        (CoreModel.load (FirstTable.result7 s (FirstMemory.frame continuation) rho).memory (18*StaggerTableLayout.pairIndices[76]!))
      refine ⟨Or.inr hm, ⟨?_,?_,?_⟩⟩
      · rw [mask_low]; exact hlo
      · rw [mask_high]; exact hhi
      · omega
    · simp only [CoreModel.message, if_neg ht, ite_false]
      exact ⟨Or.inl ht, ⟨hlo,hhi,hs⟩⟩
  · intro j hj
    apply UInt32.toNat_inj.mp
    exact low_read s continuation rho hz j hj

#print axioms low_read
#print axioms high_read
#print axioms raw_slack
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.FirstMessageReady
