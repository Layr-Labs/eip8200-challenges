import Challenge.Modexp.Submission.Proofs.Fast.ShiftCorrect
import Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect
import Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect
import Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue

set_option warningAsError true

/-!
Immutable frontier64 reference correctness, extracted from the frontier64 Solution source.
No Benchmark.Artifact import and no candidate-byte provider occurs here.
The existing Submission.Bytes/Bytecode/Proofs are the frozen reference closure.
-/

namespace Challenge.Modexp.Submission.Isolation.Baseline

/-- The original route-general theorem, before binding to a submitted artifact. -/
theorem correctFromWindow
    (route : Challenge.Modexp.Submission.Proofs.Bytecode.WindowRoute.Route) :
    Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode :=
  Challenge.Modexp.Submission.Proofs.Fast.WindowCorrect.submission_correct_of
    route Challenge.Modexp.Submission.Proofs.Fast.Shift.gasSteps_handled
    Challenge.Modexp.Submission.Proofs.Fast.BigCUGlue.bigBailHandled

/-- Complete frontier64 correctness, including both early and legacy callers and all
ValidInput fallback routes. This theorem is not a new trusted assumption. -/
theorem correct : Challenge.Modexp.Correct Challenge.Modexp.submissionBytecode :=
  correctFromWindow
    Challenge.Modexp.Submission.Proofs.Bytecode.WindowTwentyOneCorrect.route

end Challenge.Modexp.Submission.Isolation.Baseline
