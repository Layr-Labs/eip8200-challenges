import Challenge.Ripemd160.Submission.Proofs.Bytecode.FoldedCandidateArtifact
set_option warningAsError true
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
abbrev instructions := FoldedCandidateArtifact.instructions
abbrev code := FoldedCandidateArtifact.code
abbrev artifact := FoldedCandidateArtifact.artifact
theorem instruction_count : instructions.length = 5393 := FoldedCandidateArtifact.instruction_count
theorem code_size : code.size = 9742 := FoldedCandidateArtifact.code_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.HoistedStoreArtifact
