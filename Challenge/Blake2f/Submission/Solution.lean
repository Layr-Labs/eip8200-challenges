import Challenge.Blake2f.Benchmark.Artifact
import Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace Challenge.Blake2f.Benchmark

/-- Baseline proof for the bundled BLAKE2f reference bytecode. -/
theorem candidate : Challenge.Blake2f.Correct bytecode := by
  change Challenge.Blake2f.Correct Challenge.Blake2f.referenceBytecode
  exact Challenge.Blake2f.Reference.Proofs.Bytecode.ReferenceCorrect.reference_correct

end Challenge.Blake2f.Benchmark
