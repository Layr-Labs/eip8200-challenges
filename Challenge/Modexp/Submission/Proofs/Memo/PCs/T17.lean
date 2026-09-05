import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc17 (i : Nat) (hlo : 1572 ≤ i) (hhi : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [3388,3389,3390,3391,3424,3426,3427,3428,3429,3462,3465,3466,3467,3468,3501,3504,3505,3506,3507,3540,3543,3544,3545,3546,3579,3582,3583,3584,3585,3618,3621,3622,3623,3624,3657][i - 1572]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
