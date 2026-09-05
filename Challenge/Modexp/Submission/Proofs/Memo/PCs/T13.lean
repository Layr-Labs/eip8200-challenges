import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc13 (i : Nat) (hlo : 1432 ≤ i) (hhi : i ≤ 1466) :
    Artifact.submissionArtifact.instructionPC i =
      [2405,2408,2409,2411,2412,2413,2414,2416,2418,2419,2420,2421,2453,2455,2456,2457,2458,2491,2493,2494,2495,2496,2529,2531,2532,2533,2534,2567,2569,2570,2571,2572,2575,2576,2609][i - 1432]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
