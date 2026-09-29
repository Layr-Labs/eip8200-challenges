import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedStep
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuardBase

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option linter.unusedSimpArgs false

/-! Shared facts for the entry gates: the first calldata byte and the patterned
guard's jump destination. -/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM

def firstByte (input : ByteArray) : Nat :=
  (YulSemantics.EVM.byteFrom input.toList 0).toNat

theorem firstByte_eq_byteAt (input : ByteArray) :
    UInt256.byteAt (UInt256.ofNat 0) (MachineState.readWord input 0) =
      UInt256.ofNat (firstByte input) := by
  simpa [firstByte] using
    (Challenge.EvmProof.Bytes.byteAt_zero_readWord input 0)

theorem firstByte_lt (input : ByteArray) : firstByte input < 256 := by
  unfold firstByte
  exact (YulSemantics.EVM.byteFrom input.toList 0).toNat_lt

theorem stepS_lt (input : ByteArray) (pc : Nat) (a b : UInt256) (rest : List UInt256)
    (hlen : rest.length + 2 < 1024) (hpc : pc + 1 < 2 ^ 256) :
    DataStepper.runInstr (.op .LT) (PatternedScan.stS input pc (a :: b :: rest)) =
      some (PatternedScan.stS input (pc + 1) (UInt256.lt a b :: rest)) := by
  unfold DataStepper.runInstr
  rw [if_pos (by simpa using hlen)]
  simp only [PatternedScan.stS, Challenge.EvmProof.Word.succ_ofNat hpc]

theorem guard_dest : Decode.isValidJumpDest submissionBytecode 4686 = true := by
  have hpc : Artifact.submissionArtifact.instructionPC 3522 = 4686 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := Artifact.submissionArtifact.isValidJumpDest_index 3522 (by rfl)
  rwa [hpc] at h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
