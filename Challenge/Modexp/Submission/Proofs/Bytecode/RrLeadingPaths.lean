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
    Artifact.submissionArtifact.instructionPC 2397 = 3298 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2397 ≤ i) (hhi : i ≤ 2419) :
    Artifact.submissionArtifact.instructionPC i =
      ([3298,3299,3302,3303,3306,3309,3310,3311,3313,3314,3315,3317,3318,3319,3321,3322,3323,3325,3326,3327,3328,3329,3332] : List Nat)[i - 2397]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2397 .JUMPDEST,
   pushAt 2398 2 9344,
   opAt 2399 .MLOAD,
   pushAt 2400 2 5120,
   pushAt 2401 2 6144,
   opAt 2402 .MCOPY,
   opAt 2403 (.Dup ⟨1, by decide⟩),
   pushAt 2404 1 3,
   opAt 2405 .LT,
   opAt 2406 (.Dup ⟨2, by decide⟩),
   pushAt 2407 1 7,
   opAt 2408 .LT,
   opAt 2409 (.Dup ⟨3, by decide⟩),
   pushAt 2410 1 15,
   opAt 2411 .LT,
   opAt 2412 (.Dup ⟨4, by decide⟩),
   pushAt 2413 1 31,
   opAt 2414 .LT,
   opAt 2415 .ADD,
   opAt 2416 .ADD,
   opAt 2417 .ADD,
   pushAt 2418 2 1552,
   opAt 2419 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1552 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
