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
    Artifact.submissionArtifact.instructionPC 2495 = 3249 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2501 ≤ i) (hii : i ≤ 2528) :
    Artifact.submissionArtifact.instructionPC i =
      ([3261,3262,3265,3266,3268,3269,3270,3272,3273,3274,3275,3278,3279,3280,3281,3284,3285,3286,3287,3288,3289,3290,3293,3294,3295,3297,3298,3301] : List Nat)[i - 2501]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2495 .JUMPDEST,
   pushAt 2496 2 9344,
   opAt 2497 .MLOAD,
   pushAt 2498 1 128,
   opAt 2499 .LT,
   opAt 2500 (.Dup ⟨0, by decide⟩),
   pushAt 2501 1 8,
   opAt 2502 (.Swap ⟨0, by decide⟩),
   opAt 2503 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2504 .JUMPDEST,
   pushAt 2505 2 3273,
   opAt 2506 (.Dup ⟨3, by decide⟩),
   opAt 2507 (.Dup ⟨0, by decide⟩),
   opAt 2508 (.Dup ⟨0, by decide⟩),
   pushAt 2509 2 1894,
   opAt 2510 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2511 .JUMPDEST,
   pushAt 2512 0 0,
   opAt 2513 .NOT,
   opAt 2514 .ADD,
   opAt 2515 (.Dup ⟨0, by decide⟩),
   pushAt 2516 2 3262,
   opAt 2517 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .POP,
   pushAt 2519 1 5,
   opAt 2520 .SUB,
   pushAt 2521 2 2054,
   opAt 2522 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3249 = true :=
  Artifact.isValidJumpDest_index 2495 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3262 = true :=
  Artifact.isValidJumpDest_index 2504 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3273 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
