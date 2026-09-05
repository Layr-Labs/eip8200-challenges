import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc10 (i : Nat) (hlo : 1327 ≤ i) (hhi : i ≤ 1361) :
    Artifact.submissionArtifact.instructionPC i =
      [1991,1993,1994,1995,1996,1998,2000,2001,2002,2003,2036,2038,2039,2040,2041,2074,2076,2077,2078,2079,2080,2083,2084,2087,2088,2089,2091,2092,2093,2094,2095,2096,2097,2098,2099][i - 1327]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
