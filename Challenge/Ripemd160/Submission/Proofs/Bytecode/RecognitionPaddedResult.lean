import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionSelectorResult

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPaddedResult
open EvmSemantics EvmSemantics.EVM Challenge.EvmProof

/-- Full ABI-word copy at offset zero; scanner preserves the resulting memory. -/
def copied (s : State) (src : UInt256) (rho : List UInt256) : State :=
  {s with
    stack := rho
    pc := s.pc.succ
    activeWords := UInt256.ofNat 1
    memory := MachineState.writeBytes ByteArray.empty
      (MachineState.readPadded s.executionEnv.code src.toNat 32) 0}

theorem copied_memory (s : State) (src : UInt256) (rho : List UInt256) (n : Nat)
    (hread : MachineState.readPadded s.executionEnv.code src.toNat 32 =
      RecognitionDigest.paddedDigest n) :
    (copied s src rho).memory = RecognitionDigest.paddedDigest n := by
  change MachineState.writeBytes ByteArray.empty _ 0 = _
  rw [hread]
  apply ByteArray.ext_getElem
  · rw [MachineState.writeBytes_size]
    split
    · next h => simpa using h.symm
    · simp
  · intro i hi hj
    rw [← Memory.getD0_eq_getElem _ _ hi, ← Memory.getD0_eq_getElem _ _ hj,
      MachineState.writeBytes_getElem?_getD]
    simp only [Nat.zero_le, Nat.zero_add, true_and, Nat.sub_zero, if_pos hj]

#print axioms copied_memory
end Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionPaddedResult
