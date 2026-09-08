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
    Artifact.submissionArtifact.instructionPC 2727 = 3754 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2727 ≤ i) (hii : i ≤ 2754) :
    Artifact.submissionArtifact.instructionPC i =
      [3754,3755,3758,3759,3761,3762,3763,3765,3766,3767,3768,3771,3772,3773,3774,3777,3778,3779,3780,3781,3782,3783,3786,3787,3788,3790,3791,3794][i - 2727]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2727 .JUMPDEST,
   pushAt 2728 2 9344,
   opAt 2729 .MLOAD,
   pushAt 2730 1 128,
   opAt 2731 .LT,
   opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 1 8,
   opAt 2734 (.Swap ⟨0, by decide⟩),
   opAt 2735 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2736 .JUMPDEST,
   pushAt 2737 2 3778,
   opAt 2738 (.Dup ⟨3, by decide⟩),
   opAt 2739 (.Dup ⟨0, by decide⟩),
   opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 2 2209,
   opAt 2742 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2743 .JUMPDEST,
   pushAt 2744 0 0,
   opAt 2745 .NOT,
   opAt 2746 .ADD,
   opAt 2747 (.Dup ⟨0, by decide⟩),
   pushAt 2748 2 3767,
   opAt 2749 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2750 .POP,
   pushAt 2751 1 5,
   opAt 2752 .SUB,
   pushAt 2753 2 2491,
   opAt 2754 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3754 = true :=
  Artifact.isValidJumpDest_index 2727 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3767 = true :=
  Artifact.isValidJumpDest_index 2736 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3778 = true :=
  Artifact.isValidJumpDest_index 2743 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
