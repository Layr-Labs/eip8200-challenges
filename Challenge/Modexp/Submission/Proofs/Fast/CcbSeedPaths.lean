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
    Artifact.submissionArtifact.instructionPC 2506 = 3273 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2506 ≤ i) (hii : i ≤ 2533) :
    Artifact.submissionArtifact.instructionPC i =
      ([3273,3274,3277,3278,3280,3281,3282,3284,3285,3286,3287,3290,3291,3292,3293,3296,3297,3298,3299,3300,3301,3302,3305,3306,3307,3309,3310,3313] : List Nat)[i - 2506]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2506 .JUMPDEST,
   pushAt 2507 2 9344,
   opAt 2508 .MLOAD,
   pushAt 2509 1 128,
   opAt 2510 .LT,
   opAt 2511 (.Dup ⟨0, by decide⟩),
   pushAt 2512 1 8,
   opAt 2513 (.Swap ⟨0, by decide⟩),
   opAt 2514 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2515 .JUMPDEST,
   pushAt 2516 2 3297,
   opAt 2517 (.Dup ⟨3, by decide⟩),
   opAt 2518 (.Dup ⟨0, by decide⟩),
   opAt 2519 (.Dup ⟨0, by decide⟩),
   pushAt 2520 2 1910,
   opAt 2521 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2522 .JUMPDEST,
   pushAt 2523 0 0,
   opAt 2524 .NOT,
   opAt 2525 .ADD,
   opAt 2526 (.Dup ⟨0, by decide⟩),
   pushAt 2527 2 3286,
   opAt 2528 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2529 .POP,
   pushAt 2530 1 5,
   opAt 2531 .SUB,
   pushAt 2532 2 2070,
   opAt 2533 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2506 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3286 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3297 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
