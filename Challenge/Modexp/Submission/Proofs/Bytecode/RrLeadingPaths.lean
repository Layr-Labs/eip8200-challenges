import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The appended helper occupies instruction indices 2338..2360 and bytes
3335..3369. It copies CC to RR, computes the remaining RR counter from the
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
    Artifact.submissionArtifact.instructionPC 2432 = 3323 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2432 ≤ i) (hhi : i ≤ 2454) :
    Artifact.submissionArtifact.instructionPC i =
      ([3323,3324,3327,3328,3331,3334,3335,3336,3338,3339,3340,3342,3343,3344,3346,3347,3348,3350,3351,3352,3353,3354,3357] : List Nat)[i - 2432]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2432 .JUMPDEST,
   pushAt 2433 2 9344,
   opAt 2434 .MLOAD,
   pushAt 2435 2 5120,
   pushAt 2436 2 6144,
   opAt 2437 .MCOPY,
   opAt 2438 (.Dup ⟨1, by decide⟩),
   pushAt 2439 1 3,
   opAt 2440 .LT,
   opAt 2441 (.Dup ⟨2, by decide⟩),
   pushAt 2442 1 7,
   opAt 2443 .LT,
   opAt 2444 (.Dup ⟨3, by decide⟩),
   pushAt 2445 1 15,
   opAt 2446 .LT,
   opAt 2447 (.Dup ⟨4, by decide⟩),
   pushAt 2448 1 31,
   opAt 2449 .LT,
   opAt 2450 .ADD,
   opAt 2451 .ADD,
   opAt 2452 .ADD,
   pushAt 2453 2 1564,
   opAt 2454 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1564 = true :=
  jumpDest1564

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
