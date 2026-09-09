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
    Artifact.submissionArtifact.instructionPC 2444 = 3315 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2444 ≤ i) (hhi : i ≤ 2466) :
    Artifact.submissionArtifact.instructionPC i =
      ([3315,3316,3319,3320,3323,3326,3327,3328,3330,3331,3332,3334,3335,3336,3338,3339,3340,3342,3343,3344,3345,3346,3349] : List Nat)[i - 2444]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2444 .JUMPDEST,
   pushAt 2445 2 9344,
   opAt 2446 .MLOAD,
   pushAt 2447 2 5120,
   pushAt 2448 2 6144,
   opAt 2449 .MCOPY,
   opAt 2450 (.Dup ⟨1, by decide⟩),
   pushAt 2451 1 3,
   opAt 2452 .LT,
   opAt 2453 (.Dup ⟨2, by decide⟩),
   pushAt 2454 1 7,
   opAt 2455 .LT,
   opAt 2456 (.Dup ⟨3, by decide⟩),
   pushAt 2457 1 15,
   opAt 2458 .LT,
   opAt 2459 (.Dup ⟨4, by decide⟩),
   pushAt 2460 1 31,
   opAt 2461 .LT,
   opAt 2462 .ADD,
   opAt 2463 .ADD,
   opAt 2464 .ADD,
   pushAt 2465 2 1569,
   opAt 2466 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
