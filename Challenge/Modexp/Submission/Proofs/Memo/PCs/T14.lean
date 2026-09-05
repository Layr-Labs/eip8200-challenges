import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc14 (i : Nat) (hlo : 1467 ≤ i) (hhi : i ≤ 1501) :
    Artifact.submissionArtifact.instructionPC i =
      [2614,2615,2616,2617,2618,2619,2620,2621,2622,2623,2624,2625,2627,2628,2629,2630,2632,2634,2635,2636,2637,2669,2671,2672,2673,2674,2707,2709,2710,2711,2712,2745,2747,2748,2749][i - 1467]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
