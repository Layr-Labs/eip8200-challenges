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
    Artifact.submissionArtifact.instructionPC 2483 = 3801 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2483 ≤ i) (hii : i ≤ 2510) :
    Artifact.submissionArtifact.instructionPC i =
      ([3801,3802,3805,3806,3808,3809,3810,3812,3813,3814,3815,3818,3819,3820,3821,3824,3825,3826,3827,3828,3829,3830,3833,3834,3835,3837,3838,3841] : List Nat)[i - 2483]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2483 .JUMPDEST,
   pushAt 2484 2 9344,
   opAt 2485 .MLOAD,
   pushAt 2486 1 128,
   opAt 2487 .LT,
   opAt 2488 (.Dup ⟨0, by decide⟩),
   pushAt 2489 1 8,
   opAt 2490 (.Swap ⟨0, by decide⟩),
   opAt 2491 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2492 .JUMPDEST,
   pushAt 2493 2 3825,
   opAt 2494 (.Dup ⟨3, by decide⟩),
   opAt 2495 (.Dup ⟨0, by decide⟩),
   opAt 2496 (.Dup ⟨0, by decide⟩),
   pushAt 2497 2 2432,
   opAt 2498 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2499 .JUMPDEST,
   pushAt 2500 0 0,
   opAt 2501 .NOT,
   opAt 2502 .ADD,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 3814,
   opAt 2505 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2506 .POP,
   pushAt 2507 1 5,
   opAt 2508 .SUB,
   pushAt 2509 2 2662,
   opAt 2510 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3801 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3814 = true :=
  Artifact.isValidJumpDest_index 2492 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3825 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
