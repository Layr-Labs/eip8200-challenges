import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc14 (i : Nat) (hlo : 1467 ≤ i) (hhi : i ≤ 1501) :
    Artifact.submissionArtifact.instructionPC i =
      [2707,2708,2709,2742,2744,2745,2746,2747,2780,2782,2783,2784,2785,2818,2820,2821,2822,2823,2856,2858,2859,2860,2861,2894,2896,2897,2898,2899,2932,2935,2936,2937,2938,2971,2974][i - 1467]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
