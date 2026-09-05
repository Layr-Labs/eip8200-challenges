import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc23 (i : Nat) (hlo : 1782 ≤ i) (hhi : i ≤ 1810) :
    Artifact.submissionArtifact.instructionPC i =
      [4080,4081,4082,4115,4116,4117,4150,4152,4153,4186,4188,4189,4222,4224,4225,4258,4260,4261,4294,4296,4297,4330,4332,4333,4366,4368,4369,4372,4373][i - 1782]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
