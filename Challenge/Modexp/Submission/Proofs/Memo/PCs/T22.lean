import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc22 (i : Nat) (hlo : 1747 ≤ i) (hhi : i ≤ 1781) :
    Artifact.submissionArtifact.instructionPC i =
      [3837,3838,3871,3874,3875,3876,3877,3910,3913,3914,3915,3916,3949,3952,3953,3954,3955,3988,3991,3992,3993,3994,4027,4030,4031,4032,4033,4066,4069,4070,4071,4072,4073,4076,4077][i - 1747]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
