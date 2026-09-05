import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

The artifact is the verified-compiler reference output with two semantics-
preserving, size-preserving patches:

* the entry `PUSH2` is retargeted from the first compiler trampoline (pc 14)
  straight at the program body's `JUMPDEST` (pc 1196), collapsing the
  eight-hop trampoline chain to a single hop;
* every `for`-loop guard `LT; ISZERO` (exit when the counter is *not* below
  the bound) is recoded as `EQ; JUMPDEST` (exit when the counter equals the
  bound).  Each loop counter starts at 0 and increments by 1, so on every
  reachable state `i < n` and `i ≠ n` coincide; `EQ` (3 gas) plus the
  stack-neutral `JUMPDEST` filler (1 gas) costs 2 less than
  `LT; ISZERO` (6 gas) per guard execution. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
