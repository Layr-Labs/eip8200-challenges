import Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighInitial
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PaddingTraceGeneral
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingMemory
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof
open PersistentStaggerTable PersistentStaggerIteration PaddingTraceGeneral

theorem lengthMemory_byte_congr (input memory other : ByteArray) (i a : Nat)
    (he : memory[a]?.getD 0 = other[a]?.getD 0) :
    (lengthMemory input memory i)[a]?.getD 0 = (lengthMemory input other i)[a]?.getD 0 := by
  induction i with
  | zero =>
    simp only [lengthMemory, MachineState.writeBytes_getElem?_getD]
    split <;> first | rfl | exact he
  | succ i ih =>
    simp only [lengthMemory, MachineState.writeBytes_getElem?_getD]
    split <;> first | rfl | exact ih

theorem lengthMemory_copied (input : ByteArray) (i : Nat) :
    lengthMemory input (PaddingTrace.padCopied input).memory i = PaddingTrace.lengthLoopMemory input i := by
  induction i with
  | zero => rfl
  | succ i ih => simp only [lengthMemory, PaddingTrace.lengthLoopMemory, ih]

def finalMemory (input : ByteArray) (i : Nat) : ByteArray :=
  lengthMemory input
    (StaggerTablePad.padRealChain (states input i).memory (UInt256.ofNat input.size))
    (PaddingTrace.lengthStop input)

theorem finalMemory_byte (input : ByteArray) (hfit : CalldataFits input) (hz : input.size%64=0)
    (hpositive : 0 < input.size)
    (i a : Nat) (ha : 1056+input.size≤a) (hb : a<1056+Padding.paddedLength input.size) :
    (finalMemory input i)[a]?.getD 0 =
      (Padding.paddedMemory (PaddingTrace.padLengthReady input).memory input)[a]?.getD 0 := by
  have he : (StaggerTablePad.padRealChain (states input i).memory
      (UInt256.ofNat input.size))[a]?.getD 0 =
      (PaddingTrace.padCopied input).memory[a]?.getD 0 := by
    rw [ColdHighInitial.padRealChain_fresh input hz hpositive i a ha]
    have h := ColdHighInitial.entry_fresh input hz a ha
    rw [PadSkipEntry.entryState, PaddingTrace.entryState_skip input hz] at h
    exact h.symm
  unfold finalMemory
  rw [lengthMemory_byte_congr input _ _ _ a he, lengthMemory_copied]
  exact PaddingTrace.padFinalMemory_getD_paddedMemory input hfit a hb

theorem finalMemory_blockAt (input : ByteArray) (hfit : CalldataFits input) (hpositive : 0 < input.size) (i : Nat)
    (hi : i<DriverTrace.blockCount input) (hh : input.size=DriverTrace.blockOffset i) :
    ScheduleCorrect.MessageBlockAt (finalMemory input i) (DriverTrace.messageOffsetWord i)
      (Padding.paddedMessage input) (DriverTrace.blockOffset i) := by
  have hz : input.size%64=0 := by rw [hh,DriverTrace.blockOffset];omega
  have hb : DriverTrace.blockOffset i+64≤Padding.paddedLength input.size := by
    rw [DriverTrace.paddedLength_eq_blockCount]
    unfold DriverTrace.blockOffset
    omega
  apply PaddedBlockBridge.paddedBlockAt {states input i with memory := finalMemory input i}
    (PaddingTrace.padLengthReady input).memory input (DriverTrace.messageOffsetWord i)
    (DriverTrace.blockOffset i)
  · intro a ha ha'
    exact finalMemory_byte input hfit hz hpositive i a (by rw [hh];exact ha) (by unfold Padding.messageOffset at *;omega)
  · exact Nat.zero_le _
  · rfl
  · exact hfit
  · exact hb

theorem lengthMemory_below (input memory : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i≤9) (a : Nat) (ha : a<1056) :
    (lengthMemory input memory i)[a]?.getD 0 = memory[a]?.getD 0 := by
  have hb : 64≤Padding.paddedLength input.size := by unfold Padding.paddedLength;omega
  induction i with
  | zero =>
    rw [lengthMemory, MachineState.writeBytes_getElem?_getD, if_neg (by unfold Padding.messageOffset;omega)]
  | succ i ih =>
    rw [lengthMemory, MachineState.writeBytes_getElem?_getD,
      PaddingTrace.lengthAddr_toNat input hfit i (by omega), if_neg (by unfold Padding.messageOffset;omega)]
    exact ih (by omega)

theorem lengthMemory_read0 (input memory : ByteArray) (hfit : CalldataFits input)
    (i : Nat) (hi : i≤9) :
    MachineState.readWord (lengthMemory input memory i) 0 = MachineState.readWord memory 0 := by
  unfold MachineState.readWord
  congr 2
  apply Memory.readPadded_congr
  intro a ha
  simpa only [Nat.zero_add] using lengthMemory_below input memory hfit i hi a (by omega)

/-- The actual image's zero set holds after the slow padding path: the pad chain's six
stores are 18-aligned and below `2 ^ 112`, `zeroSuffix` clears from byte 28, and the length
loop writes at 1056 and above.  No hypothesis on the incoming memory. -/
theorem finalMemory_clear (input : ByteArray) (hfit : CalldataFits input) (i : Nat) :
    PoolShapeV2.ClearV2 (finalMemory input i) := by
  intro a ha
  have hb := (PoolShapeV2.zeroAddressesV2_band a ha).2.1
  unfold finalMemory
  rw [lengthMemory_below input _ hfit _ (PaddingTrace.lengthStop_le input) a hb]
  exact PoolPadInvariant.padRealChain_clear _ _ (size_word_lt input hfit) a ha

#print axioms finalMemory_blockAt
#print axioms finalMemory_clear
end Challenge.Ripemd160.Submission.Proofs.Bytecode.ColdHighPaddingMemory
