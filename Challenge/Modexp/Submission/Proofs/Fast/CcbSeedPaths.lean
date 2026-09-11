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
    Artifact.submissionArtifact.instructionPC 2627 = 3455 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2627 ≤ i) (hii : i ≤ 2654) :
    Artifact.submissionArtifact.instructionPC i =
      ([3455,3456,3459,3460,3462,3463,3464,3466,3467,3468,3469,3472,3473,3474,3475,3478,3479,3480,3481,3482,3483,3484,3487,3488,3489,3491,3492,3495] : List Nat)[i - 2627]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2627 .JUMPDEST,
   pushAt 2628 2 9344,
   opAt 2629 .MLOAD,
   pushAt 2630 1 128,
   opAt 2631 .LT,
   opAt 2632 (.Dup ⟨0, by decide⟩),
   pushAt 2633 1 8,
   opAt 2634 (.Swap ⟨0, by decide⟩),
   opAt 2635 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2636 .JUMPDEST,
   pushAt 2637 2 3479,
   opAt 2638 (.Dup ⟨3, by decide⟩),
   opAt 2639 (.Dup ⟨0, by decide⟩),
   opAt 2640 (.Dup ⟨0, by decide⟩),
   pushAt 2641 2 2056,
   opAt 2642 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2643 .JUMPDEST,
   pushAt 2644 0 0,
   opAt 2645 .NOT,
   opAt 2646 .ADD,
   opAt 2647 (.Dup ⟨0, by decide⟩),
   pushAt 2648 2 3468,
   opAt 2649 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2650 .POP,
   pushAt 2651 1 5,
   opAt 2652 .SUB,
   pushAt 2653 2 2218,
   opAt 2654 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3455 = true :=
  Artifact.isValidJumpDest_index 2627 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3468 = true :=
  Artifact.isValidJumpDest_index 2636 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3479 = true :=
  Artifact.isValidJumpDest_index 2643 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
