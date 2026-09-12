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
    Artifact.submissionArtifact.instructionPC 2497 = 3252 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2497 ≤ i) (hii : i ≤ 2524) :
    Artifact.submissionArtifact.instructionPC i =
      ([3252,3253,3256,3257,3259,3260,3261,3263,3264,3265,3266,3269,3270,3271,3272,3275,3276,3277,3278,3279,3280,3281,3284,3285,3286,3288,3289,3292] : List Nat)[i - 2497]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2497 .JUMPDEST,
   pushAt 2498 2 9344,
   opAt 2499 .MLOAD,
   pushAt 2500 1 128,
   opAt 2501 .LT,
   opAt 2502 (.Dup ⟨0, by decide⟩),
   pushAt 2503 1 8,
   opAt 2504 (.Swap ⟨0, by decide⟩),
   opAt 2505 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2506 .JUMPDEST,
   pushAt 2507 2 3276,
   opAt 2508 (.Dup ⟨3, by decide⟩),
   opAt 2509 (.Dup ⟨0, by decide⟩),
   opAt 2510 (.Dup ⟨0, by decide⟩),
   pushAt 2511 2 1898,
   opAt 2512 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2513 .JUMPDEST,
   pushAt 2514 0 0,
   opAt 2515 .NOT,
   opAt 2516 .ADD,
   opAt 2517 (.Dup ⟨0, by decide⟩),
   pushAt 2518 2 3265,
   opAt 2519 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2520 .POP,
   pushAt 2521 1 5,
   opAt 2522 .SUB,
   pushAt 2523 2 2058,
   opAt 2524 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3252 = true :=
  Artifact.isValidJumpDest_index 2497 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3265 = true :=
  Artifact.isValidJumpDest_index 2506 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3276 = true :=
  Artifact.isValidJumpDest_index 2513 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
