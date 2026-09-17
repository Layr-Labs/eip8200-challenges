import Challenge.Modexp.Submission.Isolation.BaselineCorrect
import Challenge.Modexp.Submission.Isolation.Candidate

set_option warningAsError true

namespace Challenge.Modexp.Benchmark

/-- Universal correctness of the exact generated combined frontier64+pointer
candidate, transported from the immutable frontier64 reference proof. -/
theorem candidate : Challenge.Modexp.Correct bytecode :=
  Challenge.Modexp.Submission.Isolation.ForwardRefinement.correct
    Challenge.Modexp.Submission.Isolation.Candidate.refinement
    Challenge.Modexp.Submission.Isolation.Baseline.correct

end Challenge.Modexp.Benchmark

#print axioms Challenge.Modexp.Benchmark.candidate

-- Yukon reuse by @anamdongparkjinhyeong: source @ercumentyildirim, submission 1c21ab97-04ca-470f-ae2d-57e5fa08dc78, commit e638a7a3e1d0afea4389d8748055a867a31cb3d9.
-- The local adapter above adds only the separately proved six-byte pointer refinement.
