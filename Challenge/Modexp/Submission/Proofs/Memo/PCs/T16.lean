import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc16 (i : Nat) (hlo : 1537 ≤ i) (hhi : i ≤ 1571) :
    Artifact.submissionArtifact.instructionPC i =
      [2673,2674,2675,2676,2709,2711,2712,2713,2714,2747,2749,2750,2751,2752,2785,2787,2788,2789,2790,2791,2794,2795,2798,2799,2800,2833,2834,2835,2837,2838,2839,2840,2841,2842,2843][i - 1537]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
