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
    Artifact.submissionArtifact.instructionPC 2747 = 3758 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2747 ≤ i) (hii : i ≤ 2774) :
    Artifact.submissionArtifact.instructionPC i =
      ([3758,3759,3762,3763,3765,3766,3767,3769,3770,3771,3772,3775,3776,3777,3778,3781,3782,3783,3784,3785,3786,3787,3790,3791,3792,3794,3795,3798] : List Nat)[i - 2747]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2747 .JUMPDEST,
   pushAt 2748 2 9344,
   opAt 2749 .MLOAD,
   pushAt 2750 1 128,
   opAt 2751 .LT,
   opAt 2752 (.Dup ⟨0, by decide⟩),
   pushAt 2753 1 8,
   opAt 2754 (.Swap ⟨0, by decide⟩),
   opAt 2755 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2756 .JUMPDEST,
   pushAt 2757 2 3782,
   opAt 2758 (.Dup ⟨3, by decide⟩),
   opAt 2759 (.Dup ⟨0, by decide⟩),
   opAt 2760 (.Dup ⟨0, by decide⟩),
   pushAt 2761 2 2189,
   opAt 2762 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2763 .JUMPDEST,
   pushAt 2764 0 0,
   opAt 2765 .NOT,
   opAt 2766 .ADD,
   opAt 2767 (.Dup ⟨0, by decide⟩),
   pushAt 2768 2 3771,
   opAt 2769 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2770 .POP,
   pushAt 2771 1 5,
   opAt 2772 .SUB,
   pushAt 2773 2 2509,
   opAt 2774 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3758 = true :=
  Artifact.isValidJumpDest_index 2747 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3771 = true :=
  Artifact.isValidJumpDest_index 2756 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3782 = true :=
  Artifact.isValidJumpDest_index 2763 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
