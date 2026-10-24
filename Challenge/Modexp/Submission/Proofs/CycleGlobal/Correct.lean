import Challenge.Modexp.Submission.Proofs.CycleGlobal.ShiftCorrect
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowCorrect
import Challenge.Modexp.Submission.Proofs.CycleGlobal.WindowTwentyOneCorrect
import Challenge.Modexp.Submission.Proofs.CycleGlobal.BigCUGlue
set_option warningAsError true
namespace CycleSubmission.Global
/-- Universal correctness of the exact cycle candidate, including every fallback. -/
theorem correct : Challenge.Modexp.Correct CycleSubmission.Artifact.bytecode :=
  Fast.WindowCorrect.submission_correct_of WindowTwentyOneCorrect.route
    Fast.Shift.gasSteps_handled Fast.BigCUGlue.bigBailHandled
end CycleSubmission.Global
