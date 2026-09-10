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
    Artifact.submissionArtifact.instructionPC 2740 = 3775 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2740 ≤ i) (hii : i ≤ 2767) :
    Artifact.submissionArtifact.instructionPC i =
      ([3775,3776,3779,3780,3782,3783,3784,3786,3787,3788,3789,3792,3793,3794,3795,3798,3799,3800,3801,3802,3803,3804,3807,3808,3809,3811,3812,3815] : List Nat)[i - 2740]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2740 .JUMPDEST,
   pushAt 2741 2 9344,
   opAt 2742 .MLOAD,
   pushAt 2743 1 128,
   opAt 2744 .LT,
   opAt 2745 (.Dup ⟨0, by decide⟩),
   pushAt 2746 1 8,
   opAt 2747 (.Swap ⟨0, by decide⟩),
   opAt 2748 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2749 .JUMPDEST,
   pushAt 2750 2 3799,
   opAt 2751 (.Dup ⟨3, by decide⟩),
   opAt 2752 (.Dup ⟨0, by decide⟩),
   opAt 2753 (.Dup ⟨0, by decide⟩),
   pushAt 2754 2 2219,
   opAt 2755 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2756 .JUMPDEST,
   pushAt 2757 0 0,
   opAt 2758 .NOT,
   opAt 2759 .ADD,
   opAt 2760 (.Dup ⟨0, by decide⟩),
   pushAt 2761 2 3788,
   opAt 2762 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2763 .POP,
   pushAt 2764 1 5,
   opAt 2765 .SUB,
   pushAt 2766 2 2510,
   opAt 2767 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3775 = true :=
  Artifact.isValidJumpDest_index 2740 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3788 = true :=
  Artifact.isValidJumpDest_index 2749 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3799 = true :=
  Artifact.isValidJumpDest_index 2756 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
