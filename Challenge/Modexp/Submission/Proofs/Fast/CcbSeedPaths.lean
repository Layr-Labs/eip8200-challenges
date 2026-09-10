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
    Artifact.submissionArtifact.instructionPC 2697 = 3739 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2697 ≤ i) (hii : i ≤ 2724) :
    Artifact.submissionArtifact.instructionPC i =
      ([3739,3740,3743,3744,3746,3747,3748,3750,3751,3752,3753,3756,3757,3758,3759,3762,3763,3764,3765,3766,3767,3768,3771,3772,3773,3775,3776,3779] : List Nat)[i - 2697]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2697 .JUMPDEST,
   pushAt 2698 2 9344,
   opAt 2699 .MLOAD,
   pushAt 2700 1 128,
   opAt 2701 .LT,
   opAt 2702 (.Dup ⟨0, by decide⟩),
   pushAt 2703 1 8,
   opAt 2704 (.Swap ⟨0, by decide⟩),
   opAt 2705 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2706 .JUMPDEST,
   pushAt 2707 2 3763,
   opAt 2708 (.Dup ⟨3, by decide⟩),
   opAt 2709 (.Dup ⟨0, by decide⟩),
   opAt 2710 (.Dup ⟨0, by decide⟩),
   pushAt 2711 2 2199,
   opAt 2712 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2713 .JUMPDEST,
   pushAt 2714 0 0,
   opAt 2715 .NOT,
   opAt 2716 .ADD,
   opAt 2717 (.Dup ⟨0, by decide⟩),
   pushAt 2718 2 3752,
   opAt 2719 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2720 .POP,
   pushAt 2721 1 5,
   opAt 2722 .SUB,
   pushAt 2723 2 2481,
   opAt 2724 .JUMP]

theorem jumpDest4016 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3739 = true :=
  Artifact.isValidJumpDest_index 2697 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3752 = true :=
  Artifact.isValidJumpDest_index 2706 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3763 = true :=
  Artifact.isValidJumpDest_index 2713 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
