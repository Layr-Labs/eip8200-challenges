import Challenge.Ripemd160.Submission.Local20261028.CandidateArtifact
set_option maxRecDepth 100000
namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control
abbrev submissionBytecode := Challenge.Ripemd160.Benchmark.bytecode
theorem referenceBytecode_size : submissionBytecode.size = 10441 := CandidateArtifact.code_size
end Challenge.Ripemd160.Submission.Proofs.Bytecode.Local20261028.Control
