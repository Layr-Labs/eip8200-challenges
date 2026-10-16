import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult
import Challenge.Ripemd160.Submission.Bytecode
import Challenge.EvmProof.Memory
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionAbsoluteSelectorRaw

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Payload
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open RecognitionAccumulator RecognitionDigest RecognitionAbsoluteSelectorRaw

private theorem readPadded_append_right (a b : ByteArray) (start n : Nat)
    (hstart : a.size ≤ start) :
    MachineState.readPadded (a ++ b) start n =
      MachineState.readPadded b (start - a.size) n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hia hib
    rw [← Memory.getD0_eq_getElem _ _ hia, ← Memory.getD0_eq_getElem _ _ hib,
      Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    have hi : i < n := by simpa using hia
    rw [if_pos hi, if_pos hi, Memory.getElem?_getD_append, if_neg (by omega)]
    congr 2
    omega

private def codePrefix : ByteArray :=
  submissionByteChunk0
 ++   submissionByteChunk1
 ++   submissionByteChunk2
 ++   submissionByteChunk3
 ++   submissionByteChunk4
 ++   submissionByteChunk5
 ++   submissionByteChunk6
 ++   submissionByteChunk7
 ++   submissionByteChunk8
 ++   submissionByteChunk9
 ++   submissionByteChunk10
 ++   submissionByteChunk11
 ++   submissionByteChunk12
 ++   submissionByteChunk13
 ++   submissionByteChunk14
 ++   submissionByteChunk15
 ++   submissionByteChunk16
 ++   submissionByteChunk17
 ++   submissionByteChunk18
private theorem codePrefix_size : codePrefix.size = 4804 := by
  simp only [codePrefix, ByteArray.size_append,
    submissionByteChunk0_size,
    submissionByteChunk1_size,
    submissionByteChunk2_size,
    submissionByteChunk3_size,
    submissionByteChunk4_size,
    submissionByteChunk5_size,
    submissionByteChunk6_size,
    submissionByteChunk7_size,
    submissionByteChunk8_size,
    submissionByteChunk9_size,
    submissionByteChunk10_size,
    submissionByteChunk11_size,
    submissionByteChunk12_size,
    submissionByteChunk13_size,
    submissionByteChunk14_size,
    submissionByteChunk15_size,
    submissionByteChunk16_size,
    submissionByteChunk17_size,
    submissionByteChunk18_size]
private theorem code_split : submissionBytecode = codePrefix ++ submissionByteChunk19 := rfl

private def sourceNat (n : Nat) : Nat := (10025211223323981654 / n) &&& 9208

private theorem tableRead (n : Nat) (hn : Allowed n) :
    MachineState.readPadded submissionBytecode (sourceNat n) 32 =
      MachineState.readPadded submissionByteChunk19 (sourceNat n - 4804) 32 := by
  have hb : 4804 ≤ sourceNat n := by
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals decide
  rw [code_split, readPadded_append_right _ _ _ _ (by rw [codePrefix_size]; exact hb), codePrefix_size]

private theorem readPadded_append_left (a b : ByteArray) (start n : Nat)
    (hbound : start + n ≤ a.size) :
    MachineState.readPadded (a ++ b) start n = MachineState.readPadded a start n := by
  apply ByteArray.ext_getElem
  · simp
  · intro i hia hib
    rw [← Memory.getD0_eq_getElem _ _ hia, ← Memory.getD0_eq_getElem _ _ hib,
      Memory.readPadded_getElem?_getD, Memory.readPadded_getElem?_getD]
    have hi : i < n := by simpa using hia
    rw [if_pos hi, if_pos hi, Memory.getElem?_getD_append, if_pos (by omega)]

private theorem tablePayload (n : Nat) (hn : Allowed n) :
    MachineState.readPadded submissionByteChunk19 (sourceNat n - 4804) 32 =
      RecognitionDigest.paddedDigest n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change MachineState.readPadded submissionByteChunk19 4236 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3676 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3828 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 4332 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 4076 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3996 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3604 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3948 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3532 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 4116 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3492 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3436 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 4292 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl
  · change MachineState.readPadded submissionByteChunk19 3716 32 = _
    rw [submissionByteChunk19]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_right _ _ _ _ (by decide)]
    rw [readPadded_append_left _ _ _ _ (by decide)]
    rfl

private theorem selected_nat (n : Nat) (hn : Allowed n) :
    (selected (UInt256.ofNat 9208) n).toNat = sourceNat n := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem read_selected (n : Nat) (hn : Allowed n) :
    MachineState.readPadded submissionBytecode (selected (UInt256.ofNat 9208) n).toNat 32 =
      RecognitionDigest.paddedDigest n := by
  rw [selected_nat n hn, tableRead n hn]
  exact tablePayload n hn

#print axioms read_selected
end Challenge.Ripemd160.Submission.Proofs.Bytecode.J2Payload
