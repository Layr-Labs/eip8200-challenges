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
    Artifact.submissionArtifact.instructionPC 2483 = 3498 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2483 ≤ i) (hii : i ≤ 2510) :
    Artifact.submissionArtifact.instructionPC i =
      [3498,3499,3502,3503,3505,3506,3507,3509,3510,3511,3512,3515,3516,3517,3518,3521,3522,3523,3524,3525,3526,3527,3530,3531,3532,3534,3535,3538][i - 2483]! := by
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
   pushAt 2493 2 3522,
   opAt 2494 (.Dup ⟨3, by decide⟩),
   opAt 2495 (.Dup ⟨0, by decide⟩),
   opAt 2496 (.Dup ⟨0, by decide⟩),
   pushAt 2497 2 2209,
   opAt 2498 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2499 .JUMPDEST,
   pushAt 2500 0 0,
   opAt 2501 .NOT,
   opAt 2502 .ADD,
   opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 3511,
   opAt 2505 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2506 .POP,
   pushAt 2507 1 5,
   opAt 2508 .SUB,
   pushAt 2509 2 2491,
   opAt 2510 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3498 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3511 = true :=
  Artifact.isValidJumpDest_index 2492 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3522 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
