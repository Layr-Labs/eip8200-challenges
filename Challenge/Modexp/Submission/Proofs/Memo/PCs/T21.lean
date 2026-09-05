import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc21 (i : Nat) (hlo : 1712 ≤ i) (hhi : i ≤ 1746) :
    Artifact.submissionArtifact.instructionPC i =
      [3565,3566,3599,3601,3602,3603,3604,3637,3640,3641,3642,3643,3676,3679,3680,3681,3682,3715,3718,3719,3720,3721,3754,3757,3758,3759,3760,3793,3796,3797,3798,3799,3832,3835,3836][i - 1712]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
