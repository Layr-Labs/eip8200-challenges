import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc18 (i : Nat) (hlo : 1607 ≤ i) (hhi : i ≤ 1641) :
    Artifact.submissionArtifact.instructionPC i =
      [3660,3661,3662,3663,3696,3699,3700,3701,3702,3735,3738,3739,3740,3741,3774,3777,3778,3779,3780,3813,3816,3817,3818,3819,3852,3855,3856,3857,3858,3891,3894,3895,3896,3897,3898][i - 1607]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
