import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc19 (i : Nat) (hlo : 1642 ≤ i) (hhi : i ≤ 1672) :
    Artifact.submissionArtifact.instructionPC i =
      [3901,3902,3905,3906,3907,3940,3941,3942,3975,3977,3978,4011,4013,4014,4047,4049,4050,4083,4085,4086,4119,4121,4122,4155,4157,4158,4191,4193,4194,4197,4198][i - 1642]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
