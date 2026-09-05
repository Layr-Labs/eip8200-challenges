import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc13 (i : Nat) (hlo : 1432 ≤ i) (hhi : i ≤ 1466) :
    Artifact.submissionArtifact.instructionPC i =
      [2248,2250,2251,2252,2253,2255,2257,2258,2259,2260,2293,2295,2296,2297,2298,2331,2333,2334,2335,2336,2367,2369,2370,2371,2372,2373,2376,2377,2380,2381,2382,2415,2417,2418,2420][i - 1432]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
