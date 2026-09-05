import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.H39Memo.Correct

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Exact-bytecode correctness for the exact-input dispatcher with general fallback. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode := by
  change Challenge.Ripemd160.Correct
    Challenge.Ripemd160.Submission.H39Memo.h39Bytecode
  exact Challenge.Ripemd160.Submission.H39Memo.correct

end Challenge.Ripemd160.Benchmark
