import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc17 (i : Nat) (hlo : 1572 ≤ i) (hhi : i ≤ 1606) :
    Artifact.submissionArtifact.instructionPC i =
      [3088,3121,3124,3125,3126,3127,3160,3163,3164,3165,3166,3199,3202,3203,3204,3205,3208,3209,3242,3243,3244,3277,3279,3280,3313,3315,3316,3349,3351,3352,3354,3355,3356,3357,3358][i - 1572]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
