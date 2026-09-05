import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc8 (i : Nat) (hlo : 1257 ≤ i) (hhi : i ≤ 1291) :
    Artifact.submissionArtifact.instructionPC i =
      [1897,1898,1899,1900,1932,1934,1935,1936,1937,1970,1972,1973,1974,1975,2008,2010,2011,2012,2013,2016,2017,2019,2020,2021,2022,2023,2024,2025,2026,2027,2028,2029,2030,2031,2032][i - 1257]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
