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
    Artifact.submissionArtifact.instructionPC 2720 = 3775 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2720 ≤ i) (hii : i ≤ 2747) :
    Artifact.submissionArtifact.instructionPC i =
      ([3775,3776,3779,3780,3782,3783,3784,3786,3787,3788,3789,3792,3793,3794,3795,3798,3799,3800,3801,3802,3803,3804,3807,3808,3809,3811,3812,3815] : List Nat)[i - 2720]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2720 .JUMPDEST,
   pushAt 2721 2 9344,
   opAt 2722 .MLOAD,
   pushAt 2723 1 128,
   opAt 2724 .LT,
   opAt 2725 (.Dup ⟨0, by decide⟩),
   pushAt 2726 1 8,
   opAt 2727 (.Swap ⟨0, by decide⟩),
   opAt 2728 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2729 .JUMPDEST,
   pushAt 2730 2 3799,
   opAt 2731 (.Dup ⟨3, by decide⟩),
   opAt 2732 (.Dup ⟨0, by decide⟩),
   opAt 2733 (.Dup ⟨0, by decide⟩),
   pushAt 2734 2 2219,
   opAt 2735 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2736 .JUMPDEST,
   pushAt 2737 0 0,
   opAt 2738 .NOT,
   opAt 2739 .ADD,
   opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 2 3788,
   opAt 2742 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2743 .POP,
   pushAt 2744 1 5,
   opAt 2745 .SUB,
   pushAt 2746 2 2510,
   opAt 2747 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3775 = true :=
  Artifact.isValidJumpDest_index 2720 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3788 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3799 = true :=
  Artifact.isValidJumpDest_index 2736 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
