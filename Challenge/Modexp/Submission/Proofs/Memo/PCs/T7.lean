import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc7 (i : Nat) (hlo : 1222 ≤ i) (hhi : i ≤ 1256) :
    Artifact.submissionArtifact.instructionPC i =
      [1885,1887,1889,1890,1891,1892,1925,1927,1928,1929,1930,1963,1965,1966,1967,1968,1969,1972,1973,1976,1977,1978,1980,1981,1982,1983,1984,1985,1986,1988,1989,1990,1991,1993,1995][i - 1222]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
