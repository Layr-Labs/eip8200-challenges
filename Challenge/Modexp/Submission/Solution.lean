import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCorrect
import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect
import Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Joins the fixed-width dispatch route to the fast multi-limb MODEXP
implementation and the certified reference fallback. The submitted program
starts with `PUSH2 5245; JUMP` into the concrete dispatch. -/
theorem candidateFromWindow
    (route : Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute.Route) :
    Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
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
-- Yukon reuse by @ercumentyildirim: source @i34-9, submission b8d53595-3d85-4011-b1a6-5115830c3e7a, commit f9636b7d8de7ebb454cfa2d2e913d58b8cf7e62a.
