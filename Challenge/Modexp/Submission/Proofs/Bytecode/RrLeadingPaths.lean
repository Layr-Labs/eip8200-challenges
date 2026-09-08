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
    Artifact.submissionArtifact.instructionPC 2472 = 3584 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2472 ≤ i) (hhi : i ≤ 2494) :
    Artifact.submissionArtifact.instructionPC i =
      ([3584,3585,3588,3589,3592,3595,3596,3597,3599,3600,3601,3603,3604,3605,3607,3608,3609,3611,3612,3613,3614,3615,3618] : List Nat)[i - 2472]! := by
  interval_cases i <;> decide

def helperPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2472 .JUMPDEST,
   pushAt 2473 2 9344,
   opAt 2474 .MLOAD,
   pushAt 2475 2 5120,
   pushAt 2476 2 6144,
   opAt 2477 .MCOPY,
   opAt 2478 (.Dup ⟨1, by decide⟩),
   pushAt 2479 1 3,
   opAt 2480 .LT,
   opAt 2481 (.Dup ⟨2, by decide⟩),
   pushAt 2482 1 7,
   opAt 2483 .LT,
   opAt 2484 (.Dup ⟨3, by decide⟩),
   pushAt 2485 1 15,
   opAt 2486 .LT,
   opAt 2487 (.Dup ⟨4, by decide⟩),
   pushAt 2488 1 31,
   opAt 2489 .LT,
   opAt 2490 .ADD,
   opAt 2491 .ADD,
   opAt 2492 .ADD,
   pushAt 2493 2 1569,
   opAt 2494 .JUMP]

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
