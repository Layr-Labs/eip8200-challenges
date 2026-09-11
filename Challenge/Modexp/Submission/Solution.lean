import Challenge.Modexp.Benchmark.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.ShiftCorrect
import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Challenge.Modexp.Benchmark

/-- Joins the fixed-width dispatch route to the fast multi-limb MODEXP
implementation and the certified reference fallback. The submitted program
starts with `PUSH2 4951; JUMP` into the concrete dispatch. -/
theorem candidateFromWindow
    (route : Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute.Route) :
    Challenge.Modexp.Correct bytecode := by
  change Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode
  exact Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect.submission_correct_of
    route Challenge.Modexp.Submission.Proofs.Fast.Shift.gasSteps_handled

/-- Universal correctness of the exact submitted bytecode, including the
concrete fixed-width window route and the complete legacy fallback. -/
theorem candidate : Challenge.Modexp.Correct bytecode :=
  candidateFromWindow
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect.route

end Challenge.Modexp.Benchmark

#print axioms Challenge.Modexp.Benchmark.candidate
