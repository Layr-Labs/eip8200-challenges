import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

The artifact is the verified-compiler reference output with three edits: the
entry `PUSH2` is retargeted from the first compiler trampoline (pc 14) straight
at the program body's `JUMPDEST` (pc 1196), collapsing the eight-hop trampoline
chain to a single hop; the EIP-7823 bound-check block is bypassed after loading
the three length words because `Correct` already assumes `ValidInput`; and the
multi-limb exponent loop's second `mulModBig`
call site (pc 1016) is replaced by a hop to an appended guard at pc 1284 that
performs the call only when the exponent bit is set.  The branchless selector
that follows already discards that product on a zero bit. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
