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
    Artifact.submissionArtifact.instructionPC 2504 = 3519 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2504 ≤ i) (hii : i ≤ 2531) :
    Artifact.submissionArtifact.instructionPC i =
      ([3519,3520,3523,3524,3526,3527,3528,3530,3531,3532,3533,3536,3537,3538,3539,3542,3543,3544,3545,3546,3547,3548,3551,3552,3553,3555,3556,3559] : List Nat)[i - 2504]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   pushAt 2505 2 9344,
   opAt 2506 .MLOAD,
   pushAt 2507 1 128,
   opAt 2508 .LT,
   opAt 2509 (.Dup ⟨0, by decide⟩),
   pushAt 2510 1 8,
   opAt 2511 (.Swap ⟨0, by decide⟩),
   opAt 2512 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2513 .JUMPDEST,
   pushAt 2514 2 3543,
   opAt 2515 (.Dup ⟨3, by decide⟩),
   opAt 2516 (.Dup ⟨0, by decide⟩),
   opAt 2517 (.Dup ⟨0, by decide⟩),
   pushAt 2518 2 2219,
   opAt 2519 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2520 .JUMPDEST,
   pushAt 2521 0 0,
   opAt 2522 .NOT,
   opAt 2523 .ADD,
   opAt 2524 (.Dup ⟨0, by decide⟩),
   pushAt 2525 2 3532,
   opAt 2526 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2527 .POP,
   pushAt 2528 1 5,
   opAt 2529 .SUB,
   pushAt 2530 2 2510,
   opAt 2531 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3519 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3532 = true :=
  Artifact.isValidJumpDest_index 2513 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3543 = true :=
  Artifact.isValidJumpDest_index 2520 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
