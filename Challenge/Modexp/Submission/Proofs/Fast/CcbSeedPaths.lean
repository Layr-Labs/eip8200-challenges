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
    Artifact.submissionArtifact.instructionPC 2729 = 3804 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2729 ≤ i) (hii : i ≤ 2756) :
    Artifact.submissionArtifact.instructionPC i =
      ([3804,3805,3808,3809,3811,3812,3813,3815,3816,3817,3818,3821,3822,3823,3824,3827,3828,3829,3830,3831,3832,3833,3836,3837,3838,3840,3841,3844] : List Nat)[i - 2729]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2729 .JUMPDEST,
   pushAt 2730 2 9344,
   opAt 2731 .MLOAD,
   pushAt 2732 1 128,
   opAt 2733 .LT,
   opAt 2734 (.Dup ⟨0, by decide⟩),
   pushAt 2735 1 8,
   opAt 2736 (.Swap ⟨0, by decide⟩),
   opAt 2737 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2738 .JUMPDEST,
   pushAt 2739 2 3828,
   opAt 2740 (.Dup ⟨3, by decide⟩),
   opAt 2741 (.Dup ⟨0, by decide⟩),
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 2 2142,
   opAt 2744 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2745 .JUMPDEST,
   pushAt 2746 0 0,
   opAt 2747 .NOT,
   opAt 2748 .ADD,
   opAt 2749 (.Dup ⟨0, by decide⟩),
   pushAt 2750 2 3817,
   opAt 2751 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2752 .POP,
   pushAt 2753 1 5,
   opAt 2754 .SUB,
   pushAt 2755 2 2565,
   opAt 2756 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3804 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3817 = true :=
  Artifact.isValidJumpDest_index 2738 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3828 = true :=
  Artifact.isValidJumpDest_index 2745 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
