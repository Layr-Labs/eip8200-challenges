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
    Artifact.submissionArtifact.instructionPC 2642 = 4016 := by rfl

@[simp] theorem seedPC (i : Nat) (hi : 2642 ≤ i) (hii : i ≤ 2669) :
    Artifact.submissionArtifact.instructionPC i =
      [4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,4035,
       4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,4053,4056][i - 2642]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2642 + (i - 2642)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2642 +
        (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2642).take
          (i - 2642))).length :=
      instructionPC_add Artifact.submissionArtifact 2642 (i - 2642)
    _ = _ := by
      rw [seedPCAnchor]
      interval_cases i <;> rfl

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2642 .JUMPDEST,
   pushAt 2643 2 9344,
   opAt 2644 .MLOAD,
   pushAt 2645 1 128,
   opAt 2646 .LT,
   opAt 2647 (.Dup ⟨0, by decide⟩),
   pushAt 2648 1 8,
   opAt 2649 (.Swap ⟨0, by decide⟩),
   opAt 2650 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2651 .JUMPDEST,
   pushAt 2652 2 4040,
   opAt 2653 (.Dup ⟨3, by decide⟩),
   opAt 2654 (.Dup ⟨0, by decide⟩),
   opAt 2655 (.Dup ⟨0, by decide⟩),
   pushAt 2656 2 5305,
   opAt 2657 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2658 .JUMPDEST,
   pushAt 2659 0 0,
   opAt 2660 .NOT,
   opAt 2661 .ADD,
   opAt 2662 (.Dup ⟨0, by decide⟩),
   pushAt 2663 2 4029,
   opAt 2664 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2665 .POP,
   pushAt 2666 1 5,
   opAt 2667 .SUB,
   pushAt 2668 2 2877,
   opAt 2669 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2642 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2651 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2658 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
