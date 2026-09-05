import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc20 (i : Nat) (hlo : 1677 ≤ i) (hhi : i ≤ 1711) :
    Artifact.submissionArtifact.instructionPC i =
      [3830,3833,3834,3835,3836,3869,3872,3873,3874,3875,3908,3911,3912,3913,3914,3947,3950,3951,3952,3953,3986,3989,3990,3991,3992,4025,4028,4029,4030,4031,4034,4035,4068,4069,4070][i - 1677]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
