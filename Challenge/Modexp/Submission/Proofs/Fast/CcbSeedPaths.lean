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
    Artifact.submissionArtifact.instructionPC 2674 = 3543 := by rfl

@[simp] theorem seedPC (i : Nat)
    (hi : 2674 ≤ i) (hii : i ≤ 2701) :
    Artifact.submissionArtifact.instructionPC i =
      ([3543,3544,3547,3548,3550,3551,3552,3554,3555,3556,3557,3560,3561,3562,3563,3566,3567,3568,3569,3570,3571,3572,3575,3576,3577,3579,3580,3583] : List Nat)[i - 2674]! := by
  interval_cases i <;> decide

def entryPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2674 .JUMPDEST,
   pushAt 2675 2 9344,
   opAt 2676 .MLOAD,
   pushAt 2677 1 128,
   opAt 2678 .LT,
   opAt 2679 (.Dup ⟨0, by decide⟩),
   pushAt 2680 1 8,
   opAt 2681 (.Swap ⟨0, by decide⟩),
   opAt 2682 .SHL]

def callPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2683 .JUMPDEST,
   pushAt 2684 2 3567,
   opAt 2685 (.Dup ⟨3, by decide⟩),
   opAt 2686 (.Dup ⟨0, by decide⟩),
   opAt 2687 (.Dup ⟨0, by decide⟩),
   pushAt 2688 2 2137,
   opAt 2689 .JUMP]

def retPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2690 .JUMPDEST,
   pushAt 2691 0 0,
   opAt 2692 .NOT,
   opAt 2693 .ADD,
   opAt 2694 (.Dup ⟨0, by decide⟩),
   pushAt 2695 2 3556,
   opAt 2696 .JUMPI]

def finishPath : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2697 .POP,
   pushAt 2698 1 5,
   opAt 2699 .SUB,
   pushAt 2700 2 2299,
   opAt 2701 .JUMP]

theorem jumpDest3973 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3543 = true :=
  Artifact.isValidJumpDest_index 2674 (by rfl)

theorem jumpDest4029 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3556 = true :=
  Artifact.isValidJumpDest_index 2683 (by rfl)

theorem jumpDest4040 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3567 = true :=
  Artifact.isValidJumpDest_index 2690 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast.CcbSeed
