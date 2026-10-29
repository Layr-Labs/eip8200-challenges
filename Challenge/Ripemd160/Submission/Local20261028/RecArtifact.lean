import Challenge.Ripemd160.Submission.Local20261028.CandidateArtifact
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreArtifact
abbrev instructions := CandidateArtifact.instructions
abbrev code := CandidateArtifact.artifact.code
abbrev artifact := CandidateArtifact.artifact
theorem instruction_count : instructions.length = 7030 := CandidateArtifact.instruction_count
theorem code_size : code.size = 10441 := CandidateArtifact.code_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreArtifact
