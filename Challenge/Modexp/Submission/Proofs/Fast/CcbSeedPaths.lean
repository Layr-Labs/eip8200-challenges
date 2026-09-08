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
    Artifact.submissionArtifact.instructionPC 2518 = 4011 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2518 ≤ i) (hii : i ≤ 2545) :
    Artifact.submissionArtifact.instructionPC i =
      ([4011,4012,4015,4016,4018,4019,4020,4022,4023,4024,4025,4028,4029,4030,4031,4034,4035,4036,4037,4038,4039,4040,4043,4044,4045,4047,4048,4051] : List Nat)[i - 2518]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   pushAt 2519 2 9344,
   opAt 2520 .MLOAD,
   pushAt 2521 1 128,
   opAt 2522 .LT,
   opAt 2523 (.Dup ⟨0, by decide⟩),
   pushAt 2524 1 8,
   opAt 2525 (.Swap ⟨0, by decide⟩),
   opAt 2526 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .JUMPDEST,
   pushAt 2528 2 4035,
   opAt 2529 (.Dup ⟨3, by decide⟩),
   opAt 2530 (.Dup ⟨0, by decide⟩),
   opAt 2531 (.Dup ⟨0, by decide⟩),
   pushAt 2532 2 2462,
   opAt 2533 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2534 .JUMPDEST,
   pushAt 2535 0 0,
   opAt 2536 .NOT,
   opAt 2537 .ADD,
   opAt 2538 (.Dup ⟨0, by decide⟩),
   pushAt 2539 2 4024,
   opAt 2540 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2541 .POP,
   pushAt 2542 1 5,
   opAt 2543 .SUB,
   pushAt 2544 2 2872,
   opAt 2545 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4011 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4024 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4035 = true :=
  Artifact.isValidJumpDest_index 2534 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
