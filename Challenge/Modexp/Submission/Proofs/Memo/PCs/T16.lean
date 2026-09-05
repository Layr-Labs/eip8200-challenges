import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc16 (i : Nat) (hlo : 1537 ≤ i) (hhi : i ≤ 1571) :
    Artifact.submissionArtifact.instructionPC i =
      [3214,3215,3216,3217,3218,3221,3222,3223,3224,3226,3228,3229,3230,3231,3234,3236,3237,3238,3239,3272,3274,3275,3276,3277,3310,3312,3313,3314,3315,3348,3350,3351,3352,3353,3386][i - 1537]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
