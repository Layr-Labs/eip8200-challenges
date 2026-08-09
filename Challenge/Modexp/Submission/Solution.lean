import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Correctness of the submitted MODEXP bytecode.

Four edits on top of the verified-compiler reference output, none of which
recompiles the Yul:

* the entry `PUSH2` is retargeted from the first compiler trampoline (pc 14)
  straight at the program body's `JUMPDEST`, collapsing the eight-hop
  trampoline chain to a single hop;
* the compiler's loop-increment idiom `PUSH1 1; DUP2; ADD; SWAP1; POP` is
  replaced at 18 sites by the equivalent `PUSH1 1; ADD`, with the three freed
  bytes parked after the following unconditional `JUMP` where they are
  unreachable;
* the exponent loop is replaced by true square-and-multiply; and
* `mulModBig` is replaced by a flat double-and-add whose trip count is a
  scanned bound on the multiplier's bit length.

The first two are semantics-preserving and keep every byte offset. The last
two change behaviour, so each neutralizes its region in place with
`JUMPDEST; PUSH2 <appended>; JUMP` plus unreachable filler padded to exactly
the original byte *and* instruction count, and appends the replacement past
the end of the program. Every instruction index below the appended code is
therefore unchanged, and every jump target still resolves. The last two edits
make gas depend on operand values, so this artifact deliberately has no
value-independent gas bound; `Correct` needs only that a trace exists. -/
theorem candidate : Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Bytecode.SubmissionCorrect.submission_correct

end Challenge.Modexp.Benchmark
