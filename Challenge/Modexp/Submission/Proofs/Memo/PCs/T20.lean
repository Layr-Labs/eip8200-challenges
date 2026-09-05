import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc20 (i : Nat) (hlo : 1677 ≤ i) (hhi : i ≤ 1711) :
    Artifact.submissionArtifact.instructionPC i =
      [3391,3392,3393,3396,3397,3398,3399,3401,3403,3404,3405,3406,3409,3411,3412,3413,3414,3447,3449,3450,3451,3452,3485,3487,3488,3489,3490,3523,3525,3526,3527,3528,3561,3563,3564][i - 1677]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
