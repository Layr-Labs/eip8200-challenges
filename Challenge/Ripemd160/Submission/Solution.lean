import Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding
import Challenge.Ripemd160.Benchmark.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect
import Challenge.Ripemd160.Submission.Proofs.Bytecode.RetainedTerminalMul.Correct

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 5000000

namespace Challenge.Ripemd160.Benchmark

/-- Compose semantic correctness before expanding either bytecode literal. -/
private theorem submission_correct :
    Challenge.Ripemd160.Correct Challenge.Ripemd160.submissionBytecode :=
  Challenge.Ripemd160.Submission.Proofs.Bytecode.DirectGuard.correct_of_recognition
    Challenge.Ripemd160.Submission.Proofs.Bytecode.RecognitionCorrect.from_entry
      RetainedActual115.from_loaded1000

/-- Bind the protected image once, outside the universal execution predicate. -/
private theorem bytecode_eq_submission :
    bytecode = Challenge.Ripemd160.submissionBytecode :=
  Challenge.Ripemd160.Submission.Proofs.Bytecode.BytecodeBinding.exact

/-- Exact-bytecode correctness for the direct stack-resident compressor. -/
theorem candidate : Challenge.Ripemd160.Correct bytecode :=
  bytecode_eq_submission.symm ▸ submission_correct

end Challenge.Ripemd160.Benchmark

#print axioms Challenge.Ripemd160.Benchmark.candidate
-- Current decoded SHA-256: 5443a71e40bfcd86c097e9ffa5cbb674f4f54bb2036cdc444be7a599b55add71.
-- 9642 bytes; retained-word local score 640024 (98 runtime executions passed).
-- Direct literal-word scanner; final partial-word mask derived from calldata size.
