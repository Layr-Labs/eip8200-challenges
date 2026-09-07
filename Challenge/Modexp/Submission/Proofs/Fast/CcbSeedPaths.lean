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
    Artifact.submissionArtifact.instructionPC 2544 = 3934 := by rfl

@[simp] theorem seedPC (i : Nat) (hi : 2544 ≤ i) (hii : i ≤ 2571) :
    Artifact.submissionArtifact.instructionPC i =
      [3934,3935,3938,3939,3941,3942,3943,3945,3946,3947,3948,3951,3952,3953,
       3954,3957,3958,3959,3960,3961,3962,3963,3966,3967,3968,3970,3971,3974][i - 2544]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2544 + (i - 2544)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2544 +
        (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2544).take
          (i - 2544))).length :=
      instructionPC_add Artifact.submissionArtifact 2544 (i - 2544)
    _ = _ := by
      rw [seedPCAnchor]
      interval_cases i <;> rfl

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   pushAt 2545 2 9344,
   opAt 2546 .MLOAD,
   pushAt 2547 1 128,
   opAt 2548 .LT,
   opAt 2549 (.Dup ⟨0, by decide⟩),
   pushAt 2550 1 8,
   opAt 2551 (.Swap ⟨0, by decide⟩),
   opAt 2552 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2553 .JUMPDEST,
   pushAt 2554 2 3958,
   opAt 2555 (.Dup ⟨3, by decide⟩),
   opAt 2556 (.Dup ⟨0, by decide⟩),
   opAt 2557 (.Dup ⟨0, by decide⟩),
   pushAt 2558 2 2467,
   opAt 2559 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2560 .JUMPDEST,
   pushAt 2561 0 0,
   opAt 2562 .NOT,
   opAt 2563 .ADD,
   opAt 2564 (.Dup ⟨0, by decide⟩),
   pushAt 2565 2 3947,
   opAt 2566 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2567 .POP,
   pushAt 2568 1 5,
   opAt 2569 .SUB,
   pushAt 2570 2 2877,
   opAt 2571 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3934 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2553 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3958 = true :=
  Artifact.isValidJumpDest_index 2560 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
