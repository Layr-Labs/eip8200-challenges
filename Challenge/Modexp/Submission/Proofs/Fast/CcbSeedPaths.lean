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
    Artifact.submissionArtifact.instructionPC 2476 = 4011 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2476 ≤ i) (hii : i ≤ 2503) :
    Artifact.submissionArtifact.instructionPC i =
      ([4011,4012,4015,4016,4018,4019,4020,4022,4023,4024,4025,4028,4029,4030,4031,4034,4035,4036,4037,4038,4039,4040,4043,4044,4045,4047,4048,4051] : List Nat)[i - 2476]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2476 .JUMPDEST,
   pushAt 2477 2 9344,
   opAt 2478 .MLOAD,
   pushAt 2479 1 128,
   opAt 2480 .LT,
   opAt 2481 (.Dup ⟨0, by decide⟩),
   pushAt 2482 1 8,
   opAt 2483 (.Swap ⟨0, by decide⟩),
   opAt 2484 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2485 .JUMPDEST,
   pushAt 2486 2 4035,
   opAt 2487 (.Dup ⟨3, by decide⟩),
   opAt 2488 (.Dup ⟨0, by decide⟩),
   opAt 2489 (.Dup ⟨0, by decide⟩),
   pushAt 2490 2 2462,
   opAt 2491 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2492 .JUMPDEST,
   pushAt 2493 0 0,
   opAt 2494 .NOT,
   opAt 2495 .ADD,
   opAt 2496 (.Dup ⟨0, by decide⟩),
   pushAt 2497 2 4024,
   opAt 2498 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2499 .POP,
   pushAt 2500 1 5,
   opAt 2501 .SUB,
   pushAt 2502 2 2872,
   opAt 2503 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4011 = true :=
  Artifact.isValidJumpDest_index 2476 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4024 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4035 = true :=
  Artifact.isValidJumpDest_index 2492 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
