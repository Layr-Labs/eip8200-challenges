import Challenge.Ripemd160.Submission.Local20261028.ColdArtifact
import Challenge.Ripemd160.Submission.Local20261028.FirstEntry
set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
open EvmSemantics EvmSemantics.EVM YulEvmCompiler Challenge.EvmProof
open StackRoundTrace StackRoundTemplate Local20261028
def jumpCode : List Instr := [.push ⟨2,by decide⟩ (UInt256.ofNat 6382), .op .JUMP]
def jumpSite : GenericRoundSite CandidateArtifact.artifact .Osaka jumpCode :=
  StackSiteBuilder.ofSlice jumpCode 92 (by rfl)
    (by change 92 + jumpCode.length ≤ CandidateArtifact.instructions.length; rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide)) (by decide)
theorem jump_pc : jumpSite.startPC = UInt256.ofNat 188 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 92) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel

def joinCode : List Instr := [.op .JUMPDEST]
def joinSite : GenericRoundSite CandidateArtifact.artifact .Osaka joinCode :=
  StackSiteBuilder.ofSlice joinCode 4009 (by rfl)
    (by change 4009 + joinCode.length ≤ CandidateArtifact.instructions.length; rw [CandidateArtifact.instruction_count]; decide)
    (by rw [CandidateArtifact.code_size]; decide)
    (CoreGas.wellFormed_of_check _ (by decide)) (by decide)
theorem join_pc : joinSite.startPC = UInt256.ofNat 6382 := by
  change UInt256.ofNat (CandidateArtifact.artifact.instructionPC 4009) = _
  rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
theorem valid9997 : Decode.isValidJumpDest CandidateArtifact.artifact.code 6382 = true := by
  have hpc : CandidateArtifact.artifact.instructionPC 4009 = 6382 := by
    rw [ArtifactByteLength.instructionPC_eq_byteLength]; decide +kernel
  have h := CandidateArtifact.artifact.isValidJumpDest_index 4009 (by rfl)
  rw [hpc] at h; exact h

#print axioms jumpSite
#print axioms joinSite
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.ColdGuardFixup
