import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc9 (i : Nat) (hlo : 1292 ≤ i) (hhi : i ≤ 1326) :
    Artifact.submissionArtifact.instructionPC i =
      [1915,1917,1918,1919,1920,1953,1955,1956,1957,1958,1959,1962,1963,1966,1967,1968,1970,1971,1972,1974,1975,1976,1977,1978,1979,1980,1981,1982,1983,1984,1985,1986,1987,1988,1989][i - 1292]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
