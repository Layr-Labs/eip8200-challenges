import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedCandidateArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Bytecode
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

abbrev submissionInstructions := FoldedCandidateArtifact.instructions
abbrev submissionArtifact := FoldedCandidateArtifact.artifact

theorem referenceInstructions_count : submissionInstructions.length = 7043 :=
  FoldedCandidateArtifact.instruction_count

def instructionPC (index : Nat) : Nat := submissionArtifact.instructionPC index

@[simp] theorem validJumpDest_loop :
    Decode.isValidJumpDest submissionBytecode 461 = true := by
  have hp : submissionArtifact.instructionPC 150 = 461 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 150 (by rfl)
  rw [hp] at h
  exact h

private def wfOp {operation : Operation}
    (hopcode : Decode.opcodeOf (Challenge.EvmProof.PcEncoding.opByte operation) = some operation)
    (hplain : YulEvmCompiler.plainOp operation)
    (havailable : operation.availableInFork .Osaka = true) :
    Challenge.EvmProof.DataStepper.WellFormed .Osaka (.op operation) :=
  ⟨hopcode, hplain, havailable⟩

def padEnterPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨126, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), by rfl, by decide⟩,
   ⟨127, .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), by rfl, by decide⟩]

def padCopyPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨128, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨129, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨130, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨131, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨132, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨133, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩]

def padGuardPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨145, .push ⟨8, by decide⟩ (UInt256.ofNat 18446744073709551423), by rfl, by decide⟩,
   ⟨146, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨147, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨148, .push ⟨1, by decide⟩ (UInt256.ofNat 143), by rfl, by decide⟩,
   ⟨149, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def padSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨6811, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨6812, .op (.Dup ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6813, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6814, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6815, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

def padFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨6816, .push ⟨2, by decide⟩ (UInt256.ofNat 4583), by rfl, by decide⟩,
   ⟨6817, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6818, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨6819, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6820, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6821, .push ⟨2, by decide⟩ (UInt256.ofNat 968), by rfl, by decide⟩,
   ⟨6822, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6823, .push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨6824, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6825, .push ⟨1, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨6826, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6827, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6828, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def padExitPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨3381, .push ⟨1, by decide⟩ (UInt256.ofNat 198), by rfl, by decide⟩,
   ⟨3382, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨89, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨90, .push ⟨1, by decide⟩ (UInt256.ofNat 222), by rfl, by decide⟩,
   ⟨91, .op (.Swap ⟨15, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨92, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨93, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨94, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨95, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨96, .push ⟨2, by decide⟩ (UInt256.ofNat 461), by rfl, by decide⟩,
   ⟨97, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4601 :
    Decode.isValidJumpDest submissionBytecode 8247 = true := by
  have hp : submissionArtifact.instructionPC 6181 = 8247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 6181 (by rfl)
  rw [hp] at h
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedInherited.Artifact
