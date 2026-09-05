import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

The artifact is the verified-compiler reference output with the entry
`PUSH2` retargeted from the first compiler trampoline (pc 14) straight at the
program body's `JUMPDEST` (pc 1202), collapsing the eight-hop trampoline chain
to a single hop. In the big-path exponent loop, a clear exponent bit now
skips the second Montgomery multiplication: after the square is copied back,
`DUP1; ISZERO; PUSH2 1040; JUMPI` falls through to the product call on a set
bit and jumps directly to the select preamble on a clear bit. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
