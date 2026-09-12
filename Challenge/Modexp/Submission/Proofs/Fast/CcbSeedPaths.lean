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
    Artifact.submissionArtifact.instructionPC 2528 = 3296 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2528 ≤ i) (hii : i ≤ 2555) :
    Artifact.submissionArtifact.instructionPC i =
      ([3296,3297,3300,3301,3303,3304,3305,3307,3308,3309,3310,3313,3314,3315,3316,3319,3320,3321,3322,3323,3324,3325,3328,3329,3330,3332,3333,3336] : List Nat)[i - 2528]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2528 .JUMPDEST,
   pushAt 2529 2 9344,
   opAt 2530 .MLOAD,
   pushAt 2531 1 128,
   opAt 2532 .LT,
   opAt 2533 (.Dup ⟨0, by decide⟩),
   pushAt 2534 1 8,
   opAt 2535 (.Swap ⟨0, by decide⟩),
   opAt 2536 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2537 .JUMPDEST,
   pushAt 2538 2 3320,
   opAt 2539 (.Dup ⟨3, by decide⟩),
   opAt 2540 (.Dup ⟨0, by decide⟩),
   opAt 2541 (.Dup ⟨0, by decide⟩),
   pushAt 2542 2 1946,
   opAt 2543 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2544 .JUMPDEST,
   pushAt 2545 0 0,
   opAt 2546 .NOT,
   opAt 2547 .ADD,
   opAt 2548 (.Dup ⟨0, by decide⟩),
   pushAt 2549 2 3309,
   opAt 2550 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2551 .POP,
   pushAt 2552 1 5,
   opAt 2553 .SUB,
   pushAt 2554 2 2106,
   opAt 2555 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3296 = true :=
  Artifact.isValidJumpDest_index 2528 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3309 = true :=
  Artifact.isValidJumpDest_index 2537 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3320 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
