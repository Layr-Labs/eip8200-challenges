import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc18 (i : Nat) (hlo : 1607 ≤ i) (hhi : i ≤ 1641) :
    Artifact.submissionArtifact.instructionPC i =
      [3015,3017,3018,3019,3020,3053,3055,3056,3057,3058,3091,3094,3095,3096,3097,3130,3133,3134,3135,3136,3169,3172,3173,3174,3175,3208,3211,3212,3213,3214,3215,3218,3219,3222,3223][i - 1607]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
