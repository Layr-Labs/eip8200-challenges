import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc15 (i : Nat) (hlo : 1502 ≤ i) (hhi : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2747,2748,2749,2750,2783,2785,2786,2787,2788,2791,2792,2825,2826,2827,2829,2830,2831,2832,2833,2834,2835,2836,2837,2838,2839,2840,2841,2842,2843,2844,2845,2846,2847,2848,2849][i - 1502]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
