import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast.CcbSeed

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) = p.instructionPC base +
      (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem seedPCAnchor :
    Artifact.submissionArtifact.instructionPC 2736 = 3768 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2736 ≤ i) (hii : i ≤ 2763) :
    Artifact.submissionArtifact.instructionPC i =
      ([3768,3769,3772,3773,3775,3776,3777,3779,3780,3781,3782,3785,3786,3787,3788,3791,3792,3793,3794,3795,3796,3797,3800,3801,3802,3804,3805,3808] : List Nat)[i - 2736]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2736 .JUMPDEST,
   pushAt 2737 2 9344,
   opAt 2738 .MLOAD,
   pushAt 2739 1 128,
   opAt 2740 .LT,
   opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 1 8,
   opAt 2743 (.Swap ⟨0, by decide⟩),
   opAt 2744 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   pushAt 2746 2 3792,
   opAt 2747 (.Dup ⟨3, by decide⟩),
   opAt 2748 (.Dup ⟨0, by decide⟩),
   opAt 2749 (.Dup ⟨0, by decide⟩),
   pushAt 2750 2 2203,
   opAt 2751 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 .JUMPDEST,
   pushAt 2753 0 0,
   opAt 2754 .NOT,
   opAt 2755 .ADD,
   opAt 2756 (.Dup ⟨0, by decide⟩),
   pushAt 2757 2 3781,
   opAt 2758 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2759 .POP,
   pushAt 2760 1 5,
   opAt 2761 .SUB,
   pushAt 2762 2 2520,
   opAt 2763 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3768 = true :=
  Artifact.isValidJumpDest_index 2736 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3781 = true :=
  Artifact.isValidJumpDest_index 2745 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3792 = true :=
  Artifact.isValidJumpDest_index 2752 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
