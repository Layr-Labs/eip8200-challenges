import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2338..2360 and bytes
3571..3605. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2338 = 3571 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2338 ≤ i) (hhi : i ≤ 2360) :
    Artifact.submissionArtifact.instructionPC i =
      [3571, 3572, 3575, 3576, 3579, 3582, 3583, 3584,
       3586, 3587, 3588, 3590, 3591, 3592, 3594, 3595,
       3596, 3598, 3599, 3600, 3601, 3602, 3605][i - 2338]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2338 + (i - 2338)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2338 +
          (assembleBytes
            ((Artifact.submissionArtifact.instructions.drop 2338).take
              (i - 2338))).length :=
      instructionPC_add Artifact.submissionArtifact 2338 (i - 2338)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2338 .JUMPDEST,
   pushAt 2339 2 9344,
   opAt 2340 .MLOAD,
   pushAt 2341 2 5120,
   pushAt 2342 2 6144,
   opAt 2343 .MCOPY,
   opAt 2344 (.Dup ⟨1, by decide⟩),
   pushAt 2345 1 3,
   opAt 2346 .LT,
   opAt 2347 (.Dup ⟨2, by decide⟩),
   pushAt 2348 1 7,
   opAt 2349 .LT,
   opAt 2350 (.Dup ⟨3, by decide⟩),
   pushAt 2351 1 15,
   opAt 2352 .LT,
   opAt 2353 (.Dup ⟨4, by decide⟩),
   pushAt 2354 1 31,
   opAt 2355 .LT,
   opAt 2356 .ADD,
   opAt 2357 .ADD,
   opAt 2358 .ADD,
   pushAt 2359 2 1569,
   opAt 2360 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
