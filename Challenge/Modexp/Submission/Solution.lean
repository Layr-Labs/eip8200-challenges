import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Two size-preserving edits on top of the verified-compiler reference output:

* the entry `PUSH2` is retargeted from the first compiler trampoline (pc 14)
  straight at the program body's `JUMPDEST` (pc 1196), collapsing the eight-hop
  trampoline chain to a single hop; and
* the compiler's loop-increment idiom `PUSH1 1; DUP2; ADD; SWAP1; POP` is
  replaced at 18 sites by the equivalent `PUSH1 1; ADD`, with the three freed
  bytes parked after the following unconditional `JUMP` where they are
  unreachable.

Both keep the artifact at 1,284 bytes and 961 instructions, so every jump
target and instruction index is unchanged. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
