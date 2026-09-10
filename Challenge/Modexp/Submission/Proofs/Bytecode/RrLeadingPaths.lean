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
    Artifact.submissionArtifact.instructionPC 2443 = 3314 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2443 ≤ i) (hhi : i ≤ 2465) :
    Artifact.submissionArtifact.instructionPC i =
      ([3314,3315,3318,3319,3322,3325,3326,3327,3329,3330,3331,3333,3334,3335,3337,3338,3339,3341,3342,3343,3344,3345,3348] : List Nat)[i - 2443]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2443 .JUMPDEST,
   pushAt 2444 2 9344,
   opAt 2445 .MLOAD,
   pushAt 2446 2 5120,
   pushAt 2447 2 6144,
   opAt 2448 .MCOPY,
   opAt 2449 (.Dup ⟨1, by decide⟩),
   pushAt 2450 1 3,
   opAt 2451 .LT,
   opAt 2452 (.Dup ⟨2, by decide⟩),
   pushAt 2453 1 7,
   opAt 2454 .LT,
   opAt 2455 (.Dup ⟨3, by decide⟩),
   pushAt 2456 1 15,
   opAt 2457 .LT,
   opAt 2458 (.Dup ⟨4, by decide⟩),
   pushAt 2459 1 31,
   opAt 2460 .LT,
   opAt 2461 .ADD,
   opAt 2462 .ADD,
   opAt 2463 .ADD,
   pushAt 2464 2 1562,
   opAt 2465 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1562 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
