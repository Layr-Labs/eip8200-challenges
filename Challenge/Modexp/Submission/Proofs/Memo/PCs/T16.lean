import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc16 (i : Nat) (hlo : 1537 ≤ i) (hhi : i ≤ 1571) :
    Artifact.submissionArtifact.instructionPC i =
      [2854,2856,2858,2859,2860,2861,2893,2895,2896,2897,2898,2931,2933,2934,2935,2936,2969,2971,2972,2973,2974,3007,3009,3010,3011,3012,3045,3047,3048,3049,3050,3083,3085,3086,3087][i - 1537]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
