import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc8 (i : Nat) (hlo : 1257 ≤ i) (hhi : i ≤ 1291) :
    Artifact.submissionArtifact.instructionPC i =
      [1996,1997,1998,2000,2002,2003,2004,2005,2038,2040,2041,2042,2043,2044,2046,2047,2048,2049,2050,2053,2054,2057,2058,2059,2092,2093,2094,2096,2097,2098,2099,2100,2101,2102,2103][i - 1257]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
