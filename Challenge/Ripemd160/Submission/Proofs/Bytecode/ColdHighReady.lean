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
      (PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i))) (blockWords input i) := by
  refine StaggerMessage.ready_dual0 (finalMemory input i)
    (PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i)) (blockWords input i)
    (PairedScheduleData.extractedWord_bound _ _ 6) ?_
  exact StaggerMessage.ready_junk (finalMemory input i)
    (PairedScheduleData.extractedWord (finalMemory input i) (messagePointer i)) (blockWords input i)
    (fun _ => 0)
    (fun k hk => by
      rw [extracted_words input hfit hpositive i hi hh k hk, Word.ofUInt32_toNat]
      omega)
    (fun k _ => by norm_num)
    (fun k _ _ => by norm_num)
    (fun k _ _ _ => by norm_num)
    (fun k _ _ => ⟨by norm_num, fun _ => rfl⟩)

private theorem ready_transfer (memory : ByteArray) (p : Nat) (words : Nat → UInt32)
    (hc : PoolShape.Clear memory)
    (hr : StaggerMessage.Ready (StaggerTableLayout.resultMemory0 memory
      (PairedScheduleData.extractedWord memory p)) words) :
    StaggerMessage.Ready (PoolReference.dataMemory memory p) words := by
  have hreference : StaggerMessage.Ready (PoolShape.resultMemory true memory
      (PairedScheduleData.reversedWord (MachineState.readWord memory p))
      (PairedScheduleData.reversedWord (MachineState.readWord memory (p+32)))) words := by
    refine PoolInvariant.ready_of_gap _ _ _
      (fun q hq => PoolReference.reference_data_getD memory p
        (PoolInvariant.clear_low memory hc) (PoolInvariant.clear_gap memory hc) q hq) ?_ hr
    rw [PoolReference.reference_data_getD memory p
      (PoolInvariant.clear_low memory hc) (PoolInvariant.clear_gap memory hc) 54 (by omega)]
    exact Pair13Memory.resultMemory0_byte54 memory _
      (fun k _ => Nat.lt_trans (PairedScheduleData.extractedWord_bound memory p k) (by norm_num))
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
      (finalMemory_gapClear input hfit hpositive i (by omega)) (finalMemory_extraClear input hfit i)
      (finalMemory_zero0 input hfit hpositive i (by omega)))
    (ready_model input hfit hpositive i hi hh)

#print axioms ready
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighReady
