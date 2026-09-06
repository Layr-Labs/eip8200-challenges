import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2481..2503 and bytes
3741..3775. It copies CC to RR, computes the remaining RR counter from the
limb count, and rejoins the unchanged RR loop at byte 1569.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Fast

private theorem instructionPC_add
    (p : Challenge.EvmProof.ProgramArtifact) (base count : Nat) :
    p.instructionPC (base + count) =
      p.instructionPC base +
        (assembleBytes ((p.instructions.drop base).take count)).length := by
  simp only [Challenge.EvmProof.ProgramArtifact.instructionPC, List.take_add,
    assembleBytes_append, List.length_append]

private theorem helperPCAnchor :
    Artifact.submissionArtifact.instructionPC 2481 = 3741 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2481 ≤ i) (hhi : i ≤ 2503) :
    Artifact.submissionArtifact.instructionPC i =
      [3741, 3742, 3745, 3746, 3749, 3752, 3753, 3754,
       3756, 3757, 3758, 3760, 3761, 3762, 3764, 3765,
       3766, 3768, 3769, 3770, 3771, 3772, 3775][i - 2481]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2481 + (i - 2481)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2481 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2481).take
              (i - 2481))).length :=
      instructionPC_add Artifact.submissionArtifact 2481 (i - 2481)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2481 .JUMPDEST,
   pushAt 2482 2 9344,
   opAt 2483 .MLOAD,
   pushAt 2484 2 5120,
   pushAt 2485 2 6144,
   opAt 2486 .MCOPY,
   opAt 2487 (.Dup ⟨1, by decide⟩),
   pushAt 2488 1 3,
   opAt 2489 .LT,
   opAt 2490 (.Dup ⟨2, by decide⟩),
   pushAt 2491 1 7,
   opAt 2492 .LT,
   opAt 2493 (.Dup ⟨3, by decide⟩),
   pushAt 2494 1 15,
   opAt 2495 .LT,
   opAt 2496 (.Dup ⟨4, by decide⟩),
   pushAt 2497 1 31,
   opAt 2498 .LT,
   opAt 2499 .ADD,
   opAt 2500 .ADD,
   opAt 2501 .ADD,
   pushAt 2502 2 1569,
   opAt 2503 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths

