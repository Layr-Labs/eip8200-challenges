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
    Artifact.submissionArtifact.instructionPC 2538 = 4016 := by rfl

@[simp] theorem seedPC (i : Nat) (hi : 2538 ≤ i) (hii : i ≤ 2565) :
    Artifact.submissionArtifact.instructionPC i =
      [4016,4017,4020,4021,4023,4024,4025,4027,4028,4029,4030,4033,4034,4035,
       4036,4039,4040,4041,4042,4043,4044,4045,4048,4049,4050,4052,4053,4056][i - 2538]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2538 + (i - 2538)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2538 +
        (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2538).take
          (i - 2538))).length :=
      instructionPC_add Artifact.submissionArtifact 2538 (i - 2538)
    _ = _ := by
      rw [seedPCAnchor]
      interval_cases i <;> rfl

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2538 .JUMPDEST,
   pushAt 2539 2 9344,
   opAt 2540 .MLOAD,
   pushAt 2541 1 128,
   opAt 2542 .LT,
   opAt 2543 (.Dup ⟨0, by decide⟩),
   pushAt 2544 1 8,
   opAt 2545 (.Swap ⟨0, by decide⟩),
   opAt 2546 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2547 .JUMPDEST,
   pushAt 2548 2 4040,
   opAt 2549 (.Dup ⟨3, by decide⟩),
   opAt 2550 (.Dup ⟨0, by decide⟩),
   opAt 2551 (.Dup ⟨0, by decide⟩),
   pushAt 2552 2 2467,
   opAt 2553 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2554 .JUMPDEST,
   pushAt 2555 0 0,
   opAt 2556 .NOT,
   opAt 2557 .ADD,
   opAt 2558 (.Dup ⟨0, by decide⟩),
   pushAt 2559 2 4029,
   opAt 2560 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2561 .POP,
   pushAt 2562 1 5,
   opAt 2563 .SUB,
   pushAt 2564 2 2877,
   opAt 2565 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4016 = true :=
  Artifact.isValidJumpDest_index 2538 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4029 = true :=
  Artifact.isValidJumpDest_index 2547 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4040 = true :=
  Artifact.isValidJumpDest_index 2554 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
