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
    Artifact.submissionArtifact.instructionPC 2494 = 4011 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2494 ≤ i) (hii : i ≤ 2521) :
    Artifact.submissionArtifact.instructionPC i =
      ([4011,4012,4015,4016,4018,4019,4020,4022,4023,4024,4025,4028,4029,4030,4031,4034,4035,4036,4037,4038,4039,4040,4043,4044,4045,4047,4048,4051] : List Nat)[i - 2494]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2494 .JUMPDEST,
   pushAt 2495 2 9344,
   opAt 2496 .MLOAD,
   pushAt 2497 1 128,
   opAt 2498 .LT,
   opAt 2499 (.Dup ⟨0, by decide⟩),
   pushAt 2500 1 8,
   opAt 2501 (.Swap ⟨0, by decide⟩),
   opAt 2502 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2503 .JUMPDEST,
   pushAt 2504 2 4035,
   opAt 2505 (.Dup ⟨3, by decide⟩),
   opAt 2506 (.Dup ⟨0, by decide⟩),
   opAt 2507 (.Dup ⟨0, by decide⟩),
   pushAt 2508 2 2462,
   opAt 2509 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2510 .JUMPDEST,
   pushAt 2511 0 0,
   opAt 2512 .NOT,
   opAt 2513 .ADD,
   opAt 2514 (.Dup ⟨0, by decide⟩),
   pushAt 2515 2 4024,
   opAt 2516 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .POP,
   pushAt 2518 1 5,
   opAt 2519 .SUB,
   pushAt 2520 2 2872,
   opAt 2521 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4011 = true :=
  Artifact.isValidJumpDest_index 2494 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4024 = true :=
  Artifact.isValidJumpDest_index 2503 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4035 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
