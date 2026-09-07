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
    Artifact.submissionArtifact.instructionPC 2570 = 4016 := by rfl

@[simp] theorem seedPC (i : Nat) (hi : 2570 ≤ i) (hii : i ≤ 2597) :
    Artifact.submissionArtifact.instructionPC i =
      [4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,4035,
       4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,4053,4056][i - 2570]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2570 + (i - 2570)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2570 +
        (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2570).take
          (i - 2570))).length :=
      instructionPC_add Artifact.submissionArtifact 2570 (i - 2570)
    _ = _ := by
      rw [seedPCAnchor]
      interval_cases i <;> rfl

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2570 .JUMPDEST,
   pushAt 2571 2 9344,
   opAt 2572 .MLOAD,
   pushAt 2573 1 128,
   opAt 2574 .LT,
   opAt 2575 (.Dup ⟨0, by decide⟩),
   pushAt 2576 1 8,
   opAt 2577 (.Swap ⟨0, by decide⟩),
   opAt 2578 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2579 .JUMPDEST,
   pushAt 2580 2 4040,
   opAt 2581 (.Dup ⟨3, by decide⟩),
   opAt 2582 (.Dup ⟨0, by decide⟩),
   opAt 2583 (.Dup ⟨0, by decide⟩),
   pushAt 2584 2 2467,
   opAt 2585 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2586 .JUMPDEST,
   pushAt 2587 0 0,
   opAt 2588 .NOT,
   opAt 2589 .ADD,
   opAt 2590 (.Dup ⟨0, by decide⟩),
   pushAt 2591 2 4029,
   opAt 2592 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2593 .POP,
   pushAt 2594 1 5,
   opAt 2595 .SUB,
   pushAt 2596 2 2877,
   opAt 2597 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2570 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2579 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2586 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
