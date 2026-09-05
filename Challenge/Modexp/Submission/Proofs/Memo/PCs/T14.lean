import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc14 (i : Nat) (hlo : 1467 ≤ i) (hhi : i ≤ 1501) :
    Artifact.submissionArtifact.instructionPC i =
      [2422,2423,2424,2425,2426,2427,2428,2429,2430,2431,2432,2433,2435,2436,2469,2470,2473,2474,2476,2477,2478,2479,2481,2483,2484,2485,2486,2488,2490,2491,2492,2493,2526,2528,2529][i - 1467]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
