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
    Artifact.submissionArtifact.instructionPC 2475 = 4011 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2475 ≤ i) (hii : i ≤ 2502) :
    Artifact.submissionArtifact.instructionPC i =
      ([4011,4012,4015,4016,4018,4019,4020,4022,4023,4024,4025,4028,4029,4030,4031,4034,4035,4036,4037,4038,4039,4040,4043,4044,4045,4047,4048,4051] : List Nat)[i - 2475]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2475 .JUMPDEST,
   pushAt 2476 2 9344,
   opAt 2477 .MLOAD,
   pushAt 2478 1 128,
   opAt 2479 .LT,
   opAt 2480 (.Dup ⟨0, by decide⟩),
   pushAt 2481 1 8,
   opAt 2482 (.Swap ⟨0, by decide⟩),
   opAt 2483 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2484 .JUMPDEST,
   pushAt 2485 2 4035,
   opAt 2486 (.Dup ⟨3, by decide⟩),
   opAt 2487 (.Dup ⟨0, by decide⟩),
   opAt 2488 (.Dup ⟨0, by decide⟩),
   pushAt 2489 2 2462,
   opAt 2490 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2491 .JUMPDEST,
   pushAt 2492 0 0,
   opAt 2493 .NOT,
   opAt 2494 .ADD,
   opAt 2495 (.Dup ⟨0, by decide⟩),
   pushAt 2496 2 4024,
   opAt 2497 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2498 .POP,
   pushAt 2499 1 5,
   opAt 2500 .SUB,
   pushAt 2501 2 2872,
   opAt 2502 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4011 = true :=
  Artifact.isValidJumpDest_index 2475 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4024 = true :=
  Artifact.isValidJumpDest_index 2484 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4035 = true :=
  Artifact.isValidJumpDest_index 2491 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
