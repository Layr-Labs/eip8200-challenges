import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc12 (i : Nat) (hlo : 1397 ≤ i) (hhi : i ≤ 1431) :
    Artifact.submissionArtifact.instructionPC i =
      [2491,2492,2493,2494,2495,2496,2497,2498,2500,2501,2502,2503,2505,2507,2508,2509,2510,2512,2514,2515,2516,2517,2550,2552,2553,2554,2555,2588,2590,2591,2592,2593,2626,2628,2629][i - 1397]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
