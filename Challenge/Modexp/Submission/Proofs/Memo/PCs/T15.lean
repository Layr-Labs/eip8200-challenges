import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc15 (i : Nat) (hlo : 1502 ≤ i) (hhi : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2975,2976,2977,3010,3013,3014,3015,3016,3049,3052,3053,3054,3055,3056,3059,3060,3063,3064,3065,3098,3099,3100,3133,3135,3136,3169,3171,3172,3205,3207,3208,3210,3211,3212,3213][i - 1502]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
