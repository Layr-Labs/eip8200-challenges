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
    Artifact.submissionArtifact.instructionPC 2437 = 3330 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2437 ≤ i) (hhi : i ≤ 2459) :
    Artifact.submissionArtifact.instructionPC i =
      ([3330,3331,3334,3335,3338,3341,3342,3343,3345,3346,3347,3349,3350,3351,3353,3354,3355,3357,3358,3359,3360,3361,3364] : List Nat)[i - 2437]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2437 .JUMPDEST,
   pushAt 2438 2 9344,
   opAt 2439 .MLOAD,
   pushAt 2440 2 5120,
   pushAt 2441 2 6144,
   opAt 2442 .MCOPY,
   opAt 2443 (.Dup ⟨1, by decide⟩),
   pushAt 2444 1 3,
   opAt 2445 .LT,
   opAt 2446 (.Dup ⟨2, by decide⟩),
   pushAt 2447 1 7,
   opAt 2448 .LT,
   opAt 2449 (.Dup ⟨3, by decide⟩),
   pushAt 2450 1 15,
   opAt 2451 .LT,
   opAt 2452 (.Dup ⟨4, by decide⟩),
   pushAt 2453 1 31,
   opAt 2454 .LT,
   opAt 2455 .ADD,
   opAt 2456 .ADD,
   opAt 2457 .ADD,
   pushAt 2458 2 1569,
   opAt 2459 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
