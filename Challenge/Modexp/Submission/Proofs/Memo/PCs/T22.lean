import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

/-- Program counters of the appended empty-return block (indices 1732..1735). -/
@[simp] theorem pc22 (i : Nat) (hlo : 1732 ≤ i) (hhi : i ≤ 1735) :
    Artifact.submissionArtifact.instructionPC i =
      [4327,4328,4329,4330][i - 1732]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
