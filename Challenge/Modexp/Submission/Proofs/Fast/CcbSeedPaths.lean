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
    Artifact.submissionArtifact.instructionPC 2502 = 3264 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2502 ≤ i) (hii : i ≤ 2529) :
    Artifact.submissionArtifact.instructionPC i =
      ([3264,3265,3268,3269,3271,3272,3273,3275,3276,3277,3278,3281,3282,3283,3284,3287,3288,3289,3290,3291,3292,3293,3296,3297,3298,3300,3301,3304] : List Nat)[i - 2502]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2502 .JUMPDEST,
   pushAt 2503 2 9344,
   opAt 2504 .MLOAD,
   pushAt 2505 1 128,
   opAt 2506 .LT,
   opAt 2507 (.Dup ⟨0, by decide⟩),
   pushAt 2508 1 8,
   opAt 2509 (.Swap ⟨0, by decide⟩),
   opAt 2510 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2511 .JUMPDEST,
   pushAt 2512 2 3288,
   opAt 2513 (.Dup ⟨3, by decide⟩),
   opAt 2514 (.Dup ⟨0, by decide⟩),
   opAt 2515 (.Dup ⟨0, by decide⟩),
   pushAt 2516 2 1910,
   opAt 2517 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2518 .JUMPDEST,
   pushAt 2519 0 0,
   opAt 2520 .NOT,
   opAt 2521 .ADD,
   opAt 2522 (.Dup ⟨0, by decide⟩),
   pushAt 2523 2 3277,
   opAt 2524 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2525 .POP,
   pushAt 2526 1 5,
   opAt 2527 .SUB,
   pushAt 2528 2 2070,
   opAt 2529 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3264 = true :=
  Artifact.isValidJumpDest_index 2502 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3277 = true :=
  Artifact.isValidJumpDest_index 2511 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3288 = true :=
  Artifact.isValidJumpDest_index 2518 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
