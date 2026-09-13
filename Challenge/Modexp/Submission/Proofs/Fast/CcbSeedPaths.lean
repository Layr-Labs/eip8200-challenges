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
    Artifact.submissionArtifact.instructionPC 2505 = 3333 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2505 ≤ i) (hii : i ≤ 2532) :
    Artifact.submissionArtifact.instructionPC i =
      ([3333,3334,3337,3338,3340,3341,3342,3344,3345,3346,3347,3350,3351,3352,3353,3356,3357,3358,3359,3360,3361,3362,3365,3366,3367,3369,3370,3373] : List Nat)[i - 2505]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2505 .JUMPDEST,
   pushAt 2506 2 2688,
   opAt 2507 .MLOAD,
   pushAt 2508 1 128,
   opAt 2509 .LT,
   opAt 2510 (.Dup ⟨0, by decide⟩),
   pushAt 2511 1 8,
   opAt 2512 (.Swap ⟨0, by decide⟩),
   opAt 2513 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2514 .JUMPDEST,
   pushAt 2515 2 3357,
   opAt 2516 (.Dup ⟨3, by decide⟩),
   opAt 2517 (.Dup ⟨0, by decide⟩),
   opAt 2518 (.Dup ⟨0, by decide⟩),
   pushAt 2519 2 2025,
   opAt 2520 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2521 .JUMPDEST,
   pushAt 2522 0 0,
   opAt 2523 .NOT,
   opAt 2524 .ADD,
   opAt 2525 (.Dup ⟨0, by decide⟩),
   pushAt 2526 2 3346,
   opAt 2527 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2528 .POP,
   pushAt 2529 1 5,
   opAt 2530 .SUB,
   pushAt 2531 2 2185,
   opAt 2532 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3333 = true :=
  Artifact.isValidJumpDest_index 2505 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3346 = true :=
  Artifact.isValidJumpDest_index 2514 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3357 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
