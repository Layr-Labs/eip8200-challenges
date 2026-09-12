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
    Artifact.submissionArtifact.instructionPC 2576 = 3396 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2576 ≤ i) (hii : i ≤ 2603) :
    Artifact.submissionArtifact.instructionPC i =
      ([3396,3397,3400,3401,3403,3404,3405,3407,3408,3409,3410,3413,3414,3415,3416,3419,3420,3421,3422,3423,3424,3425,3428,3429,3430,3432,3433,3436] : List Nat)[i - 2576]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2576 .JUMPDEST,
   pushAt 2577 2 9344,
   opAt 2578 .MLOAD,
   pushAt 2579 1 128,
   opAt 2580 .LT,
   opAt 2581 (.Dup ⟨0, by decide⟩),
   pushAt 2582 1 8,
   opAt 2583 (.Swap ⟨0, by decide⟩),
   opAt 2584 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2585 .JUMPDEST,
   pushAt 2586 2 3420,
   opAt 2587 (.Dup ⟨3, by decide⟩),
   opAt 2588 (.Dup ⟨0, by decide⟩),
   opAt 2589 (.Dup ⟨0, by decide⟩),
   pushAt 2590 2 2033,
   opAt 2591 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2592 .JUMPDEST,
   pushAt 2593 0 0,
   opAt 2594 .NOT,
   opAt 2595 .ADD,
   opAt 2596 (.Dup ⟨0, by decide⟩),
   pushAt 2597 2 3409,
   opAt 2598 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2599 .POP,
   pushAt 2600 1 5,
   opAt 2601 .SUB,
   pushAt 2602 2 2193,
   opAt 2603 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3396 = true :=
  Artifact.isValidJumpDest_index 2576 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3409 = true :=
  Artifact.isValidJumpDest_index 2585 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3420 = true :=
  Artifact.isValidJumpDest_index 2592 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
