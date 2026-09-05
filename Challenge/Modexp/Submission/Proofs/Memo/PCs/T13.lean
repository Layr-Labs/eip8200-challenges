import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc13 (i : Nat) (hlo : 1432 ≤ i) (hhi : i ≤ 1466) :
    Artifact.submissionArtifact.instructionPC i =
      [2630,2631,2632,2635,2636,2639,2640,2641,2674,2675,2676,2678,2679,2680,2681,2682,2683,2684,2685,2686,2687,2688,2689,2690,2692,2693,2694,2695,2697,2699,2700,2701,2702,2704,2706][i - 1432]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
