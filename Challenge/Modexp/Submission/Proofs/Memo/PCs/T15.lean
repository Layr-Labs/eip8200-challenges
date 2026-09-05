import Challenge.Modexp.Submission.Proofs.Bytecode.MainDefs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Memo.PCs

open Challenge.Modexp.Submission.Proofs.Bytecode

@[simp] theorem pc15 (i : Nat) (hlo : 1502 ≤ i) (hhi : i ≤ 1536) :
    Artifact.submissionArtifact.instructionPC i =
      [2530,2531,2564,2566,2567,2568,2569,2602,2604,2605,2606,2607,2608,2611,2612,2615,2616,2617,2650,2651,2652,2654,2655,2656,2657,2659,2660,2661,2662,2664,2666,2667,2668,2669,2671][i - 1502]! := by
  interval_cases i <;> decide +kernel

end Challenge.Modexp.Submission.Proofs.Memo.PCs
