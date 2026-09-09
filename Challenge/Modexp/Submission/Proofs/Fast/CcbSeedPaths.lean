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
    Artifact.submissionArtifact.instructionPC 2737 = 3739 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2737 ≤ i) (hii : i ≤ 2764) :
    Artifact.submissionArtifact.instructionPC i =
      ([3739,3740,3743,3744,3746,3747,3748,3750,3751,3752,3753,3756,3757,3758,3759,3762,3763,3764,3765,3766,3767,3768,3771,3772,3773,3775,3776,3779] : List Nat)[i - 2737]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2737 .JUMPDEST,
   pushAt 2738 2 9344,
   opAt 2739 .MLOAD,
   pushAt 2740 1 128,
   opAt 2741 .LT,
   opAt 2742 (.Dup ⟨0, by decide⟩),
   pushAt 2743 1 8,
   opAt 2744 (.Swap ⟨0, by decide⟩),
   opAt 2745 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2746 .JUMPDEST,
   pushAt 2747 2 3763,
   opAt 2748 (.Dup ⟨3, by decide⟩),
   opAt 2749 (.Dup ⟨0, by decide⟩),
   opAt 2750 (.Dup ⟨0, by decide⟩),
   pushAt 2751 2 2203,
   opAt 2752 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2753 .JUMPDEST,
   pushAt 2754 0 0,
   opAt 2755 .NOT,
   opAt 2756 .ADD,
   opAt 2757 (.Dup ⟨0, by decide⟩),
   pushAt 2758 2 3752,
   opAt 2759 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2760 .POP,
   pushAt 2761 1 5,
   opAt 2762 .SUB,
   pushAt 2763 2 2491,
   opAt 2764 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3739 = true :=
  Artifact.isValidJumpDest_index 2737 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3752 = true :=
  Artifact.isValidJumpDest_index 2746 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3763 = true :=
  Artifact.isValidJumpDest_index 2753 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
