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
    Artifact.submissionArtifact.instructionPC 2491 = 3930 := by rfl

@[simp] theorem seedPC (i : Nat) (hi : 2491 ≤ i) (hii : i ≤ 2518) :
    Artifact.submissionArtifact.instructionPC i =
      [3930,3931,3934,3935,3937,3938,3939,3941,3942,3943,3944,3947,3948,3949,
       3950,3953,3954,3955,3956,3957,3958,3959,3962,3963,3964,3966,3967,3970][i - 2491]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2491 + (i - 2491)) := by
      rw [Nat.add_sub_of_le hi]
    _ = Artifact.submissionArtifact.instructionPC 2491 +
        (assembleBytes ((Artifact.submissionArtifact.instructions.drop 2491).take
          (i - 2491))).length :=
      instructionPC_add Artifact.submissionArtifact 2491 (i - 2491)
    _ = _ := by
      rw [seedPCAnchor]
      interval_cases i <;> rfl

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2491 .JUMPDEST,
   pushAt 2492 2 9344,
   opAt 2493 .MLOAD,
   pushAt 2494 1 128,
   opAt 2495 .LT,
   opAt 2496 (.Dup ⟨0, by decide⟩),
   pushAt 2497 1 8,
   opAt 2498 (.Swap ⟨0, by decide⟩),
   opAt 2499 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2500 .JUMPDEST,
   pushAt 2501 2 3954,
   opAt 2502 (.Dup ⟨3, by decide⟩),
   opAt 2503 (.Dup ⟨0, by decide⟩),
   opAt 2504 (.Dup ⟨0, by decide⟩),
   pushAt 2505 2 2463,
   opAt 2506 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2507 .JUMPDEST,
   pushAt 2508 0 0,
   opAt 2509 .NOT,
   opAt 2510 .ADD,
   opAt 2511 (.Dup ⟨0, by decide⟩),
   pushAt 2512 2 3943,
   opAt 2513 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .POP,
   pushAt 2515 1 5,
   opAt 2516 .SUB,
   pushAt 2517 2 2873,
   opAt 2518 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3930 = true :=
  Artifact.isValidJumpDest_index 2491 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3943 = true :=
  Artifact.isValidJumpDest_index 2500 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3954 = true :=
  Artifact.isValidJumpDest_index 2507 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
