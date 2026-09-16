import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingMemory
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable ColdHighPaddingMemory

/-- The actual unmasked pool image after the slow padding path. -/
def tableMemory (input : ByteArray) (i : Nat) : ByteArray :=
  PoolReference.dataMemory (finalMemory input i) (messagePointer i)

theorem extracted_words (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size) (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i)
    (k : Nat) (hk : k<16) :
    PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i) k = Word.ofUInt32 (blockWords input i k) := by
  rw [PairedScheduleData.extractedWord_eq_expectedWord _ _ _ hk
    (messagePointer_bound input hfit i hi)]
  change ScheduleCorrect.expectedWord (finalMemory input i) (DriverTrace.messageOffsetWord i) k = _
  rw [finalMemory_blockAt input hfit hpositive i hi hh k hk,blockWords_eq_readLE32 input i k hk]

private theorem ready_model (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size) (i : Nat)
    (hi : i < DriverTrace.blockCount input) (hh : input.size = DriverTrace.blockOffset i) :
    StaggerMessage.Ready (StaggerTableLayout.resultMemory0 (finalMemory input i)
      (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i))) (blockWords input i) := by
  have hsplit (k : Nat) := StaggerScratch.dirtyWord_split (finalMemory input i) (messagePointer i) k
  -- the dual lane at address 0 is invisible to `Ready`: slot 0 is read only through `low32`
  refine StaggerMessage.ready_dual0 (finalMemory input i)
    (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i)) (blockWords input i)
    (Nat.lt_of_div_eq_zero (by norm_num) ((hsplit 6).2.2.2 (by decide))) ?_
  exact StaggerMessage.ready_junk (finalMemory input i) (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i)) (blockWords input i)
    (fun k => (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32)
    (fun k hk => by
      show (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat = _
      conv_lhs => rw [(hsplit k).1]
      rw [extracted_words input hfit hpositive i hi hh k hk, Word.ofUInt32_toNat])
    (fun k _ => (hsplit k).2.1)
    (fun k _ h2 => Nat.lt_trans ((hsplit k).2.2.1 h2) (by decide))
    (fun k _ h2 _ => (hsplit k).2.2.1 h2)
    (fun k _ hd => by
      have hd' : ¬ (k = 1 ∨ k = 2) := fun h =>
        hd (h.elim (fun h1 => Or.inl h1) (fun h2 => Or.inr (Or.inl h2)))
      have h0 : (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32 = 0 := (hsplit k).2.2.2 hd'
      exact ⟨by show (StaggerScratch.dirtyWord (finalMemory input i) (messagePointer i) k).toNat / 2 ^ 32 < 2 ^ 23; rw [h0]; decide, fun _ => h0⟩)

private theorem ready_transfer (memory : ByteArray) (p : Nat) (words : Nat → UInt32)
    (hc : PoolShape.Clear memory)
    (hr : StaggerMessage.Ready (StaggerTableLayout.resultMemory0 memory
      (StaggerScratch.dirtyWord memory p)) words) :
    StaggerMessage.Ready (PoolReference.dataMemory memory p) words := by
  have hreference : StaggerMessage.Ready (PoolShape.resultMemory true memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory p))
      (PairedScheduleData.reversedWord (MachineState.readWord memory (p+32)))) words := by
    rw [PoolReference.reference_data_eq memory p
      (PoolInvariant.clear_low memory hc) (PoolInvariant.clear_gap memory hc)]
    exact hr
  exact PoolInvariant.ready memory
    (PairedScheduleData.reversedWord (MachineState.readWord memory p))
    (PairedScheduleData.reversedWord (MachineState.readWord memory (p+32))) hc words hreference

theorem ready (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size) (i : Nat)
    (hi : i < DriverTrace.blockCount input) (hh : input.size = DriverTrace.blockOffset i) :
    StaggerMessage.Ready (tableMemory input i) (blockWords input i) := by
  have hl : (MachineState.readWord (finalMemory input i) 0).toNat % 2^144 < 2^32 := by
    rw [finalMemory_lowClear input hfit hpositive i (by omega)]
    decide
  exact ready_transfer (finalMemory input i) (messagePointer i) (blockWords input i)
    (PoolInvariant.clear_of_parts (finalMemory input i) hl
      (finalMemory_gapClear input hfit hpositive i (by omega)) (finalMemory_extraClear input hfit i))
    (ready_model input hfit hpositive i hi hh)

#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
