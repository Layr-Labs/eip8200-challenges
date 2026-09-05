import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc17 (i : Nat) (hlo : 1572 ≤ i) (hhi : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [2844,2845,2846,2847,2848,2849,2851,2852,2853,2854,2856,2858,2859,2860,2861,2863,2865,2866,2867,2868,2901,2903,2904,2905,2906,2939,2941,2942,2943,2944,2977,2979,2980,2981,2982][i - 1572]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
