import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc9 (i : Nat) (hlo : 1292 ≤ i) (hhi : i ≤ 1326) :
    Artifact.submissionArtifact.instructionPC i =
      [2033,2034,2035,2036,2037,2038,2039,2040,2041,2042,2043,2044,2045,2046,2047,2048,2049,2051,2052,2053,2054,2056,2058,2059,2060,2061,2093,2095,2096,2097,2098,2099,2101,2102,2103][i - 1292]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
