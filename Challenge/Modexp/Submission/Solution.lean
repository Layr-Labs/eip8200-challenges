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

-- draw rerun 2026-09-15T14:39:20Z: identical bytes and identical proof, resubmitted under a fresh benchmark seed

-- draw 3 2026-09-15T15:07:14Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 4 2026-09-15T15:52:54Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 4 2026-09-15T16:02:17Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 5 2026-09-15T16:39:08Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 5 2026-09-15T16:41:20Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 6 2026-09-15T17:25:51Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 7 2026-09-15T18:11:37Z: identical bytes and identical proof under a fresh benchmark seed

-- draw 8 2026-09-15T18:58:20Z: identical bytes and identical proof under a fresh benchmark seed
