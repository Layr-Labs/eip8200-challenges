import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc21 (i : Nat) (hlo : 1712 ≤ i) (hhi : i ≤ 1731) :
    Artifact.submissionArtifact.instructionPC i =
      [4139,4141,4142,4175,4177,4178,4211,4213,4214,4247,4249,4250,4283,4285,4286,4319,4321,4322,4325,4326][i - 1712]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
