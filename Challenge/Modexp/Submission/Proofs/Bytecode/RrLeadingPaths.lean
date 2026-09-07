import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2333..2355 and bytes
3564..3598. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2333 = 3564 := by
  rfl

@[simp] theorem helperPC (i : Nat) (hlo : 2333 ≤ i) (hhi : i ≤ 2355) :
    Artifact.submissionArtifact.instructionPC i =
      [3564, 3565, 3568, 3569, 3572, 3575, 3576, 3577,
       3579, 3580, 3581, 3583, 3584, 3585, 3587, 3588,
       3589, 3591, 3592, 3593, 3594, 3595, 3598][i - 2333]! := by
  calc
    Artifact.submissionArtifact.instructionPC i =
        Artifact.submissionArtifact.instructionPC (2333 + (i - 2333)) := by
      rw [Nat.add_sub_of_le hlo]
    _ = Artifact.submissionArtifact.instructionPC 2333 +
          (assembleBytes
              ((Artifact.submissionArtifact.instructions.drop 2333).take
              (i - 2333))).length :=
      instructionPC_add Artifact.submissionArtifact 2333 (i - 2333)
    _ = _ := by
      rw [helperPCAnchor]
      interval_cases i <;> rfl

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2333 .JUMPDEST,
   pushAt 2334 2 9344,
   opAt 2335 .MLOAD,
   pushAt 2336 2 5120,
   pushAt 2337 2 6144,
   opAt 2338 .MCOPY,
   opAt 2339 (.Dup ⟨1, by decide⟩),
   pushAt 2340 1 3,
   opAt 2341 .LT,
   opAt 2342 (.Dup ⟨2, by decide⟩),
   pushAt 2343 1 7,
   opAt 2344 .LT,
   opAt 2345 (.Dup ⟨3, by decide⟩),
   pushAt 2346 1 15,
   opAt 2347 .LT,
   opAt 2348 (.Dup ⟨4, by decide⟩),
   pushAt 2349 1 31,
   opAt 2350 .LT,
   opAt 2351 .ADD,
   opAt 2352 .ADD,
   opAt 2353 .ADD,
   pushAt 2354 2 1569,
   opAt 2355 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
