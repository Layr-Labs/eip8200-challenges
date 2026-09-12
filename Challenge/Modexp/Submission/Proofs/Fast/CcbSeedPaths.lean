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
    Artifact.submissionArtifact.instructionPC 2501 = 3261 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2501 ≤ i) (hii : i ≤ 2528) :
    Artifact.submissionArtifact.instructionPC i =
      ([3261,3262,3265,3266,3268,3269,3270,3272,3273,3274,3275,3278,3279,3280,3281,3284,3285,3286,3287,3288,3289,3290,3293,3294,3295,3297,3298,3301] : List Nat)[i - 2501]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2501 .JUMPDEST,
   pushAt 2502 2 2784,
   opAt 2503 .MLOAD,
   pushAt 2504 1 128,
   opAt 2505 .LT,
   opAt 2506 (.Dup ⟨0, by decide⟩),
   pushAt 2507 1 8,
   opAt 2508 (.Swap ⟨0, by decide⟩),
   opAt 2509 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2510 .JUMPDEST,
   pushAt 2511 2 3285,
   opAt 2512 (.Dup ⟨3, by decide⟩),
   opAt 2513 (.Dup ⟨0, by decide⟩),
   opAt 2514 (.Dup ⟨0, by decide⟩),
   pushAt 2515 2 1898,
   opAt 2516 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2517 .JUMPDEST,
   pushAt 2518 0 0,
   opAt 2519 .NOT,
   opAt 2520 .ADD,
   opAt 2521 (.Dup ⟨0, by decide⟩),
   pushAt 2522 2 3274,
   opAt 2523 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2524 .POP,
   pushAt 2525 1 5,
   opAt 2526 .SUB,
   pushAt 2527 2 2058,
   opAt 2528 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3261 = true :=
  Artifact.isValidJumpDest_index 2501 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3274 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3285 = true :=
  Artifact.isValidJumpDest_index 2517 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
