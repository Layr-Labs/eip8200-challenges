import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc11 (i : Nat) (hlo : 1362 ≤ i) (hhi : i ≤ 1396) :
    Artifact.submissionArtifact.instructionPC i =
      [2318,2320,2322,2323,2324,2325,2358,2360,2361,2362,2363,2396,2398,2399,2400,2401,2434,2436,2437,2438,2439,2440,2443,2444,2447,2448,2449,2482,2483,2484,2486,2487,2488,2489,2490][i - 1362]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
