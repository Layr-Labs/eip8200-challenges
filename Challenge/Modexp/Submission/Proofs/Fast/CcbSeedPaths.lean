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
    Artifact.submissionArtifact.instructionPC 2739 = 3739 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2739 ≤ i) (hii : i ≤ 2766) :
    Artifact.submissionArtifact.instructionPC i =
      ([3739,3740,3743,3744,3746,3747,3748,3750,3751,3752,3753,3756,3757,3758,3759,3762,3763,3764,3765,3766,3767,3768,3771,3772,3773,3775,3776,3779] : List Nat)[i - 2739]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2739 .JUMPDEST,
   pushAt 2740 2 9344,
   opAt 2741 .MLOAD,
   pushAt 2742 1 128,
   opAt 2743 .LT,
   opAt 2744 (.Dup ⟨0, by decide⟩),
   pushAt 2745 1 8,
   opAt 2746 (.Swap ⟨0, by decide⟩),
   opAt 2747 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2748 .JUMPDEST,
   pushAt 2749 2 3763,
   opAt 2750 (.Dup ⟨3, by decide⟩),
   opAt 2751 (.Dup ⟨0, by decide⟩),
   opAt 2752 (.Dup ⟨0, by decide⟩),
   pushAt 2753 2 2203,
   opAt 2754 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2755 .JUMPDEST,
   pushAt 2756 0 0,
   opAt 2757 .NOT,
   opAt 2758 .ADD,
   opAt 2759 (.Dup ⟨0, by decide⟩),
   pushAt 2760 2 3752,
   opAt 2761 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2762 .POP,
   pushAt 2763 1 5,
   opAt 2764 .SUB,
   pushAt 2765 2 2491,
   opAt 2766 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3739 = true :=
  Artifact.isValidJumpDest_index 2739 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3752 = true :=
  Artifact.isValidJumpDest_index 2748 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3763 = true :=
  Artifact.isValidJumpDest_index 2755 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
