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
    Artifact.submissionArtifact.instructionPC 2435 = 3294 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2435 ≤ i) (hhi : i ≤ 2457) :
    Artifact.submissionArtifact.instructionPC i =
      ([3294,3295,3298,3299,3302,3305,3306,3307,3309,3310,3311,3313,3314,3315,3317,3318,3319,3321,3322,3323,3324,3325,3328] : List Nat)[i - 2435]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2435 .JUMPDEST,
   pushAt 2436 2 9344,
   opAt 2437 .MLOAD,
   pushAt 2438 2 5120,
   pushAt 2439 2 6144,
   opAt 2440 .MCOPY,
   opAt 2441 (.Dup ⟨1, by decide⟩),
   pushAt 2442 1 3,
   opAt 2443 .LT,
   opAt 2444 (.Dup ⟨2, by decide⟩),
   pushAt 2445 1 7,
   opAt 2446 .LT,
   opAt 2447 (.Dup ⟨3, by decide⟩),
   pushAt 2448 1 15,
   opAt 2449 .LT,
   opAt 2450 (.Dup ⟨4, by decide⟩),
   pushAt 2451 1 31,
   opAt 2452 .LT,
   opAt 2453 .ADD,
   opAt 2454 .ADD,
   opAt 2455 .ADD,
   pushAt 2456 2 1564,
   opAt 2457 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1564 = true :=
  jumpDest1564

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
