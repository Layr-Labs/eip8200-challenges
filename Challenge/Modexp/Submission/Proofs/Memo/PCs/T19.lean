import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc19 (i : Nat) (hlo : 1642 ≤ i) (hhi : i ≤ 1676) :
    Artifact.submissionArtifact.instructionPC i =
      [3559,3561,3562,3563,3564,3597,3599,3600,3601,3602,3635,3638,3639,3640,3641,3674,3677,3678,3679,3680,3713,3716,3717,3718,3719,3752,3755,3756,3757,3758,3791,3794,3795,3796,3797][i - 1642]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
