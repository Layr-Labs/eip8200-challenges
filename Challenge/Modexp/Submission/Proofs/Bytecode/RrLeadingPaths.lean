import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2363..2385 and bytes
3600..3634. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2369 = 3615 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2369 ≤ i) (hhi : i ≤ 2391) :
    Artifact.submissionArtifact.instructionPC i =
      [3615, 3616, 3619, 3620, 3623, 3626, 3627, 3628,
       3630, 3631, 3632, 3634, 3635, 3636, 3638, 3639,
       3640, 3642, 3643, 3644, 3645, 3646, 3649][i - 2369]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2369 + (i - 2369)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2369 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2369).take
              (i - 2369))).length :=
      instructionPC_add Artifact.submissionArtifact 2369 (i - 2369)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2369 .JUMPDEST,
   pushAt 2370 2 9344,
   opAt 2371 .MLOAD,
   pushAt 2372 2 5120,
   pushAt 2373 2 6144,
   opAt 2374 .MCOPY,
   opAt 2375 (.Dup ⟨1, by decide⟩),
   pushAt 2376 1 3,
   opAt 2377 .LT,
   opAt 2378 (.Dup ⟨2, by decide⟩),
   pushAt 2379 1 7,
   opAt 2380 .LT,
   opAt 2381 (.Dup ⟨3, by decide⟩),
   pushAt 2382 1 15,
   opAt 2383 .LT,
   opAt 2384 (.Dup ⟨4, by decide⟩),
   pushAt 2385 1 31,
   opAt 2386 .LT,
   opAt 2387 .ADD,
   opAt 2388 .ADD,
   opAt 2389 .ADD,
   pushAt 2390 2 1569,
   opAt 2391 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
