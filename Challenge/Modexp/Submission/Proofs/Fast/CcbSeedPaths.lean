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
    Artifact.submissionArtifact.instructionPC 2776 = 4029 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2776 ≤ i) (hii : i ≤ 2803) :
    Artifact.submissionArtifact.instructionPC i =
      ([4029,4030,4033,4034,4036,4037,4038,4040,4041,4042,4043,4046,4047,4048,4049,4052,4053,4054,4055,4056,4057,4058,4061,4062,4063,4065,4066,4069] : List Nat)[i - 2776]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2776 .JUMPDEST,
   pushAt 2777 2 9344,
   opAt 2778 .MLOAD,
   pushAt 2779 1 128,
   opAt 2780 .LT,
   opAt 2781 (.Dup ⟨0, by decide⟩),
   pushAt 2782 1 8,
   opAt 2783 (.Swap ⟨0, by decide⟩),
   opAt 2784 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2785 .JUMPDEST,
   pushAt 2786 2 4053,
   opAt 2787 (.Dup ⟨3, by decide⟩),
   opAt 2788 (.Dup ⟨0, by decide⟩),
   opAt 2789 (.Dup ⟨0, by decide⟩),
   pushAt 2790 2 2480,
   opAt 2791 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2792 .JUMPDEST,
   pushAt 2793 0 0,
   opAt 2794 .NOT,
   opAt 2795 .ADD,
   opAt 2796 (.Dup ⟨0, by decide⟩),
   pushAt 2797 2 4042,
   opAt 2798 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2799 .POP,
   pushAt 2800 1 5,
   opAt 2801 .SUB,
   pushAt 2802 2 2890,
   opAt 2803 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2776 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4042 = true :=
  Artifact.isValidJumpDest_index 2785 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4053 = true :=
  Artifact.isValidJumpDest_index 2792 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
