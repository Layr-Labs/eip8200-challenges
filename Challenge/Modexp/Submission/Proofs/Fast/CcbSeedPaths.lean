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
    Artifact.submissionArtifact.instructionPC 2488 = 3519 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2488 ≤ i) (hii : i ≤ 2515) :
    Artifact.submissionArtifact.instructionPC i =
      ([3519,3520,3523,3524,3526,3527,3528,3530,3531,3532,3533,3536,3537,3538,3539,3542,3543,3544,3545,3546,3547,3548,3551,3552,3553,3555,3556,3559] : List Nat)[i - 2488]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2488 .JUMPDEST,
   pushAt 2489 2 9344,
   opAt 2490 .MLOAD,
   pushAt 2491 1 128,
   opAt 2492 .LT,
   opAt 2493 (.Dup ⟨0, by decide⟩),
   pushAt 2494 1 8,
   opAt 2495 (.Swap ⟨0, by decide⟩),
   opAt 2496 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2497 .JUMPDEST,
   pushAt 2498 2 3543,
   opAt 2499 (.Dup ⟨3, by decide⟩),
   opAt 2500 (.Dup ⟨0, by decide⟩),
   opAt 2501 (.Dup ⟨0, by decide⟩),
   pushAt 2502 2 2219,
   opAt 2503 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   pushAt 2505 0 0,
   opAt 2506 .NOT,
   opAt 2507 .ADD,
   opAt 2508 (.Dup ⟨0, by decide⟩),
   pushAt 2509 2 3532,
   opAt 2510 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2511 .POP,
   pushAt 2512 1 5,
   opAt 2513 .SUB,
   pushAt 2514 2 2510,
   opAt 2515 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3519 = true :=
  Artifact.isValidJumpDest_index 2488 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3532 = true :=
  Artifact.isValidJumpDest_index 2497 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3543 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
