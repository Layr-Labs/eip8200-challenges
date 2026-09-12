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
    Artifact.submissionArtifact.instructionPC 2521 = 3296 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2521 ≤ i) (hii : i ≤ 2548) :
    Artifact.submissionArtifact.instructionPC i =
      ([3296,3297,3300,3301,3303,3304,3305,3307,3308,3309,3310,3313,3314,3315,3316,3319,3320,3321,3322,3323,3324,3325,3328,3329,3330,3332,3333,3336] : List Nat)[i - 2521]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2521 .JUMPDEST,
   pushAt 2522 2 2784,
   opAt 2523 .MLOAD,
   pushAt 2524 1 128,
   opAt 2525 .LT,
   opAt 2526 (.Dup ⟨0, by decide⟩),
   pushAt 2527 1 8,
   opAt 2528 (.Swap ⟨0, by decide⟩),
   opAt 2529 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2530 .JUMPDEST,
   pushAt 2531 2 3320,
   opAt 2532 (.Dup ⟨3, by decide⟩),
   opAt 2533 (.Dup ⟨0, by decide⟩),
   opAt 2534 (.Dup ⟨0, by decide⟩),
   pushAt 2535 2 1939,
   opAt 2536 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2537 .JUMPDEST,
   pushAt 2538 0 0,
   opAt 2539 .NOT,
   opAt 2540 .ADD,
   opAt 2541 (.Dup ⟨0, by decide⟩),
   pushAt 2542 2 3309,
   opAt 2543 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .POP,
   pushAt 2545 1 5,
   opAt 2546 .SUB,
   pushAt 2547 2 2099,
   opAt 2548 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3296 = true :=
  Artifact.isValidJumpDest_index 2521 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3309 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3320 = true :=
  Artifact.isValidJumpDest_index 2537 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
