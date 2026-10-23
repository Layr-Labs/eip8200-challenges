import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCorrect
import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect
import Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- The protected renderer and submission use the same chunks with different
append association. Normalize that association without evaluating every byte. -/
private theorem protectedBytecode_eq : bytecode = Challenge.Modexp.submissionBytecode := by
  delta bytecode Challenge.Modexp.submissionBytecode Challenge.Modexp.submissionBytes
  simp only [ByteArray.append_assoc]

/-- Joins the fixed-width dispatch route to the fast multi-limb MODEXP
implementation and the certified reference fallback. The fast kernel keeps its
high carry and modulus word at offset 128 in the operand stack. -/
theorem candidateFromWindow
    (route : Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute.Route) :
    Challenge.Modexp.Correct bytecode := by
  rw [protectedBytecode_eq]
  exact Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect.submission_correct_of
    route Challenge.Modexp.Submission.Proofs.Fast.Shift.gasSteps_handled
    Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue.bigBailHandled

/-- Universal correctness of the exact submitted bytecode, including the
concrete fixed-width window route and the complete legacy fallback. -/
theorem candidate : Challenge.Modexp.Correct bytecode :=
  candidateFromWindow
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect.route

end Challenge.Modexp.Benchmark

#print axioms Challenge.Modexp.Benchmark.candidate

-- Yukon reuse by @anamdongparkjinhyeong: source @ercumentyildirim, submission 1c21ab97-04ca-470f-ae2d-57e5fa08dc78, commit e638a7a3e1d0afea4389d8748055a867a31cb3d9.
-- Offline candidate: PC 4264 bypasses the PC 4816 forwarding hook and enters PC 5615 directly.
