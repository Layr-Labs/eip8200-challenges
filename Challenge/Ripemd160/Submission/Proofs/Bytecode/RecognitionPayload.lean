import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult
import Challenge.Ripemd160.Submission.Bytecode
import Challenge.EvmProof.Memory

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPayload
open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open RecognitionAccumulator RecognitionDigest RecognitionSelectorRaw

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
 ++   submissionByteChunk19
private theorem codePrefix_size : codePrefix.size = 4623 := by
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
    submissionByteChunk18_size,
    submissionByteChunk19_size]
private theorem code_split : submissionBytecode = codePrefix ++ submissionByteChunk20 := rfl

private theorem tableRead (n : Nat) :
    MachineState.readPadded submissionBytecode (4819 + 21*((203142/n)%14)) 20 =
      MachineState.readPadded submissionByteChunk20 (196 + 21*((203142/n)%14)) 20 := by
  rw [code_split, readPadded_append_right _ _ _ _ (by rw [codePrefix_size]; omega), codePrefix_size]
  congr 1
  omega

private theorem tablePayload (n : Nat) (hn : Allowed n) :
    MachineState.readPadded submissionByteChunk20 (196 + 21*((203142/n)%14)) 20 =
      MachineState.readPadded payload (21*((203142/n)%14)) 20 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem read_selected (n : Nat) (hn : Allowed n) :
    MachineState.readPadded submissionBytecode (selected (UInt256.ofNat 4819) n).toNat 20 =
      MachineState.readPadded payload (21*((203142/n)%14)) 20 := by
  rw [RecognitionSelectorResult.selected_nat n hn, tableRead]
  exact tablePayload n hn

#print axioms read_selected
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPayload
