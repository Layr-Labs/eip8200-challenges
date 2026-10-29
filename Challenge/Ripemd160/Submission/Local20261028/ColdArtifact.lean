import Challenge.Ripemd160.Submission.Local20261028.CandidateArtifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.newArtifactByteLength
import Challenge.Ripemd160.Submission.Local20261028.ColdBytecode
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Artifact

open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof

def op (opcode : UInt8) : Instr :=
  match Decode.opcodeOf opcode with
  | some decoded => .op decoded
  | none => .op .INVALID

abbrev submissionInstructions := CandidateArtifact.instructions
abbrev submissionArtifact := CandidateArtifact.artifact

theorem referenceInstructions_count : submissionInstructions.length = 7025 :=
  CandidateArtifact.instruction_count

def instructionPC (index : Nat) : Nat := submissionArtifact.instructionPC index

@[simp] theorem validJumpDest_loop :
    Decode.isValidJumpDest submissionBytecode 461 = true := by
  have hp : submissionArtifact.instructionPC 158 = 461 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    rfl
  have h := submissionArtifact.isValidJumpDest_index 158 (by rfl)
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
  [⟨134, .push ⟨30, by decide⟩ (UInt256.ofNat 1766820105243087041267848467410591083712559083657179364930612997358944255), by rfl, by decide⟩,
   ⟨135, .push ⟨31, by decide⟩ (UInt256.ofNat 450552876409790643671482431940419874915447411150352389258589821042463539455), by rfl, by decide⟩]

def padCopyPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨136, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨137, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨138, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩,
   ⟨139, .op .CALLDATACOPY, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨140, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨141, .push ⟨2, by decide⟩ (UInt256.ofNat 1056), by rfl, by decide⟩]

def padGuardPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨153, .push ⟨8, by decide⟩ (UInt256.ofNat 18446744073709551423), by rfl, by decide⟩,
   ⟨154, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨155, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨156, .push ⟨1, by decide⟩ (UInt256.ofNat 143), by rfl, by decide⟩,
   ⟨157, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def padSentinelPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨6810, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨6811, .op (.Dup ⟨12, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6812, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6813, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6814, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩]

def padFooterSetupPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨6815, .push ⟨2, by decide⟩ (UInt256.ofNat 4583), by rfl, by decide⟩,
   ⟨6816, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6817, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨6818, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6819, .op .CALLDATASIZE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6820, .push ⟨2, by decide⟩ (UInt256.ofNat 968), by rfl, by decide⟩,
   ⟨6821, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6822, .push ⟨1, by decide⟩ (UInt256.ofNat 63), by rfl, by decide⟩,
   ⟨6823, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6824, .push ⟨1, by decide⟩ (UInt256.ofNat 89), by rfl, by decide⟩,
   ⟨6825, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6826, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨6827, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def padExitPath : List
    (Challenge.EvmProof.DataStepper.Located submissionArtifact .Osaka) :=
  [⟨3363, .push ⟨1, by decide⟩ (UInt256.ofNat 198), by rfl, by decide⟩,
   ⟨3364, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨97, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨98, .push ⟨1, by decide⟩ (UInt256.ofNat 222), by rfl, by decide⟩,
   ⟨99, .op (.Swap ⟨15, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨100, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨101, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨102, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨103, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨104, .push ⟨2, by decide⟩ (UInt256.ofNat 461), by rfl, by decide⟩,
   ⟨105, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

set_option maxRecDepth 100000 in
@[simp] theorem validJumpDest_4601 :
    Decode.isValidJumpDest submissionBytecode 8247 = true := by
  have hp : submissionArtifact.instructionPC 6181 = 8247 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]
    decide
  have h := submissionArtifact.isValidJumpDest_index 6181 (by rfl)
  rw [hp] at h
  exact h

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.Artifact
