import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc20 (i : Nat) (hlo : 1673 ≤ i) (hhi : i ≤ 1702) :
    Artifact.submissionArtifact.instructionPC i =
      [4199,4200,4201,4202,4203,4204,4205,4206,4207,4208,4209,4210,4212,4213,4214,4217,4218,4221,4222,4223,4224,4225,4226,4228,4229,4262,4263,4266,4267,4270][i - 1673]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
