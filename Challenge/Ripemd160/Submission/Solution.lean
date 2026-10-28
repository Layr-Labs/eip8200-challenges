import Challenge.Ripemd160.Submission.Local20261028.RecHoistedStoreCorrect
import Challenge.Ripemd160.Benchmark.Artifact
set_option warningAsError true
namespace Challenge.Ripemd160.Benchmark
/-- Universal correctness of the exact protected submission bytecode. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  Submission.Proofs.Bytecode.Local20261028.Control.HoistedStoreCorrect.correct
end Challenge.Ripemd160.Benchmark
#print axioms Challenge.Ripemd160.Benchmark.candidate
