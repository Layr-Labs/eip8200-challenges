import Challenge.Ripemd160.Submission.Local20261028.GeneralMemoryExecution
import Challenge.Ripemd160.Submission.Local20261028.CoreMessage
import Challenge.Ripemd160.Submission.Local20261028.TerminalMessageMask

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.GeneralMessageReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open RipemdMemoryBridge20261028 RipemdSubmissionTables20261028
open GeneralMessageLayout
open PairedLaneUInt256Bridge Paired144Core

def entryWords (m : ByteArray) (k : Nat) : UInt32 :=
  UInt32.ofNat (Precompile.bytesToNatPadded m (wordAddress k) 4)

theorem entryWords_toNat (m : ByteArray) (k : Nat) :
    (entryWords m k).toNat = Precompile.bytesToNatPadded m (wordAddress k) 4 := by
  have h := Bytes.bytesToNatPadded_lt_pow m (wordAddress k) 4
  simp only [entryWords, UInt32.toNat_ofNat']
  exact Nat.mod_eq_of_lt h

theorem low_value (m : ByteArray) (a : Nat) :
    (MachineState.readWord m a).toNat % 2^32 = Precompile.bytesToNatPadded m (a+28) 4 := by
  simpa using StaggerTableMemory.readWord_mod_pow m a 4 (by decide)

theorem high_value (m : ByteArray) (a : Nat) :
    (MachineState.readWord m a).toNat / 2^144 % 2^32 = Precompile.bytesToNatPadded m (a+10) 4 := by
  have h := Bytes.readWord_shift_toNat m a 14 (by decide)
  rw [Nat.shiftRight_eq_div_pow, show (32-14)*8=144 from rfl] at h
  rw [h, show (14:Nat)=10+4 from rfl, Bytes.bytesToNatPadded_add]
  have hb := Bytes.bytesToNatPadded_lt_pow m (a+10) 4
  norm_num only [Nat.reducePow] at hb ⊢
  omega

theorem low_read (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (slot : Nat) (hslot : slot < 61) :
    (CoreModel.load (GeneralTable.result8 s x rho).memory (18*slot)).toNat % 2^32 =
      (entryWords s.memory StaggerTableLayout.slots[slot]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [low_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [actual_bytes s x rho hz, low_sources ⟨slot,hslot⟩ ⟨j,hj⟩]
  exact (initial_matches s.memory hz _).symm

theorem high_read (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (GeneralTable.result8 s x rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat / 2^144 % 2^32 =
      (entryWords s.memory Crypto.Ripemd160.rP[i+3]!).toNat := by
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [high_value, entryWords_toNat]
  apply StaggerTableMemory.bytesToNatPadded_congrOffset
  intro j hj
  rw [actual_bytes s x rho hz, high_sources ⟨i,hi⟩ ⟨j,hj⟩]
  exact (initial_matches s.memory hz _).symm

theorem zero_byte_slack (w : UInt256) (k : Nat) (hk : 14 ≤ k) (hk' : k ≤ 26)
    (hz : PoolByte.byte w k = 0) : w.toNat % 2^144 + 2^40 ≤ 2^144 := by
  have h := congrArg UInt8.toNat hz
  rw [PoolByte.byte_toNat] at h
  change w.toNat / 2^(8*(31-k)) % 256 = 0 at h
  interval_cases k <;> norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow] at h ⊢ <;> omega

theorem raw_slack (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0)
    (i : Nat) (hi : i < 77) :
    (CoreModel.load (GeneralTable.result8 s x rho).memory
      (18*StaggerTableLayout.pairIndices[i]!)).toNat % 2^144 + 2^40 ≤ 2^144 := by
  obtain ⟨hl,hu,hzero⟩ := barrier_sources ⟨i,hi⟩
  change 14 ≤ barriers[i]! at hl
  change barriers[i]! ≤ 26 at hu
  apply zero_byte_slack _ barriers[i]! hl hu
  simp only [CoreModel.load, Nat.mul_div_cancel_left _ (by decide : 0 < 18)]
  rw [PoolByte.read _ _ _ (by omega), actual_bytes s x rho hz, hzero, valuation_zero]

theorem mask_low (w : UInt256) :
    (UInt256.land Paired144WordRound.pairWord w).toNat % 2^32 = w.toNat % 2^32 := by
  have h := congrArg BitVec.toNat (RipemdSubmissionTerminalRepair20261028.masked_low w)
  simpa only [low, BitVec.extractLsb'_toNat, Nat.shiftRight_zero, bits_toNat] using h

theorem mask_high (w : UInt256) :
    (UInt256.land Paired144WordRound.pairWord w).toNat / 2^144 % 2^32 = w.toNat / 2^144 % 2^32 := by
  have h := congrArg BitVec.toNat (RipemdSubmissionTerminalRepair20261028.masked_high w)
  simpa only [high, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, bits_toNat] using h

/-- The actual general-table output satisfies the inherited compressor's
    semantic contract, including the repaired terminal round. -/
theorem ready (s : State) (x : Nat → UInt256) (rho : List UInt256)
    (hz : ∀ a ∈ RipemdTableOrder20261027.clearAddresses, s.memory[a]?.getD 0 = 0) :
    CoreMessage.Ready (GeneralTable.result8 s x rho).memory (entryWords s.memory) := by
  constructor
  · intro i hi
    obtain ⟨_,hslot,hleft,_⟩ := StaggerTableLayout.layout_valid ⟨i,hi⟩
    have hlo := low_read s x rho hz StaggerTableLayout.pairIndices[i]! hslot
    rw [hleft] at hlo
    have hhi := high_read s x rho hz i hi
    have hs := raw_slack s x rho hz i hi
    apply Or.inr
    by_cases ht : i=76
    · subst i
      simp only [CoreModel.message, if_pos rfl, ite_true]
      have hm := RipemdSubmissionTerminalRepair20261028.masked_small
        (CoreModel.load (GeneralTable.result8 s x rho).memory (18*StaggerTableLayout.pairIndices[76]!))
      refine ⟨Or.inr hm, ⟨?_,?_,?_⟩⟩
      · rw [mask_low]; exact hlo
      · rw [mask_high]; exact hhi
      · omega
    · simp only [CoreModel.message, if_neg ht, ite_false]
      exact ⟨Or.inl ht, ⟨hlo,hhi,hs⟩⟩
  · intro j hj
    apply UInt32.toNat_inj.mp
    exact low_read s x rho hz j hj

#print axioms low_read
#print axioms high_read
#print axioms raw_slack
#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.GeneralMessageReady
