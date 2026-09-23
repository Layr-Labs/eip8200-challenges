import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighMemory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PersistentStaggerIteration
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighInitial
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration

theorem scheduled_byte_above (s : State) (i address : Nat) (ha : 1112≤address) :
    (scheduledState s i).memory[address]?.getD 0 = s.memory[address]?.getD 0 := by
  unfold scheduledState
  split
  · exact StaggerTablePad.getD_padRealResult_outside s.memory _ address ha
  · exact PoolInvariant.resultV2_outside s.memory _ _ address ha

theorem states_byte_above (input : ByteArray) (n address : Nat) (ha : 1112≤address) :
    (states input n).memory[address]?.getD 0 = (PadSkipEntry.entryState input).memory[address]?.getD 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact (scheduled_byte_above _ n address ha).trans ih

theorem entry_fresh (input : ByteArray) (hz : input.size%64=0)
    (address : Nat) (ha : 1056+input.size≤address) :
    (PadSkipEntry.entryState input).memory[address]?.getD 0 = 0 := by
  rw [PadSkipEntry.entryState, PaddingTrace.entryState_skip input hz]
  change (MachineState.writeBytes (PaddingTrace.padLengthReady input).memory
    (MachineState.readPadded input 0 input.size) Padding.messageOffset)[address]?.getD 0 = 0
  rw [Memory.readPadded_zero_size, MachineState.writeBytes_getElem?_getD,
    if_neg (by unfold Padding.messageOffset; omega)]
  rfl

theorem states_fresh (input : ByteArray) (hz : input.size%64=0) (hpositive : 0 < input.size) (n address : Nat)
    (ha : 1056+input.size≤address) :
    (states input n).memory[address]?.getD 0 = 0 := by
  rw [states_byte_above input n address (by omega)]
  exact entry_fresh input hz address ha

theorem lowChain_fresh (input : ByteArray) (hz : input.size%64=0) (hpositive : 0 < input.size) (n address : Nat)
    (ha : 1056+input.size≤address) :
    (StaggerTablePad.lowChain (states input n).memory (UInt256.ofNat input.size))[address]?.getD 0 = 0 := by
  rw [ColdHighMemory.lowChain_outside _ _ address (by omega)]
  exact states_fresh input hz hpositive n address ha

/-- The same freshness for the image the pad block really leaves. -/
theorem padRealChain_fresh (input : ByteArray) (hz : input.size%64=0) (hpositive : 0 < input.size) (n address : Nat)
    (ha : 1056+input.size≤address) :
    (StaggerTablePad.padRealChain (states input n).memory
      (UInt256.ofNat input.size))[address]?.getD 0 = 0 := by
  rw [ColdHighMemory.padRealChain_outside _ _ address (by omega)]
  exact states_fresh input hz hpositive n address ha

#print axioms states_fresh
#print axioms lowChain_fresh
#print axioms padRealChain_fresh
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighInitial
