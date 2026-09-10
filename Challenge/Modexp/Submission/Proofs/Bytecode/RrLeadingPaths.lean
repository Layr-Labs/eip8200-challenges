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
    Artifact.submissionArtifact.instructionPC 2431 = 3366 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2431 ≤ i) (hhi : i ≤ 2453) :
    Artifact.submissionArtifact.instructionPC i =
      ([3366,3367,3370,3371,3374,3377,3378,3379,3381,3382,3383,3385,3386,3387,3389,3390,3391,3393,3394,3395,3396,3397,3400] : List Nat)[i - 2431]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2431 .JUMPDEST,
   pushAt 2432 2 9344,
   opAt 2433 .MLOAD,
   pushAt 2434 2 5120,
   pushAt 2435 2 6144,
   opAt 2436 .MCOPY,
   opAt 2437 (.Dup ⟨1, by decide⟩),
   pushAt 2438 1 3,
   opAt 2439 .LT,
   opAt 2440 (.Dup ⟨2, by decide⟩),
   pushAt 2441 1 7,
   opAt 2442 .LT,
   opAt 2443 (.Dup ⟨3, by decide⟩),
   pushAt 2444 1 15,
   opAt 2445 .LT,
   opAt 2446 (.Dup ⟨4, by decide⟩),
   pushAt 2447 1 31,
   opAt 2448 .LT,
   opAt 2449 .ADD,
   opAt 2450 .ADD,
   opAt 2451 .ADD,
   pushAt 2452 2 1519,
   opAt 2453 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1519 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
