import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc18 (i : Nat) (hlo : 1607 ≤ i) (hhi : i ≤ 1641) :
    Artifact.submissionArtifact.instructionPC i =
      [3356,3357,3358,3359,3360,3361,3364,3365,3366,3367,3369,3371,3372,3373,3374,3407,3409,3410,3411,3412,3445,3447,3448,3449,3450,3483,3485,3486,3487,3488,3521,3523,3524,3525,3526][i - 1607]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
