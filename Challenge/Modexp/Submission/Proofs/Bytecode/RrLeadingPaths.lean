import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Located direct RR-leading helper

The fixed-width RR helper now keeps its 23-byte footprint: it dispatches
`n > 3` to an appended generic counter and directly materializes counter zero
for the common `n ≤ 3` case.  The appended fallback occupies indices
3868..3885 and bytes 5323..5346.
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
    Artifact.submissionArtifact.instructionPC 2444 = 3330 := by
  rfl

@[simp] theorem helperPC (i : Nat)
    (hlo : 2444 ≤ i) (hhi : i ≤ 2466) :
    Artifact.submissionArtifact.instructionPC i =
      ([3330,3331,3334,3335,3338,3341,3342,3343,3345,3346,3349,3350,
        3351,3354,3355,3357,3358,3359,3360,3361,3362,3363,3364] : List Nat)[i - 2444]! := by
  interval_cases i <;> decide

@[simp] theorem fallbackPC (i : Nat)
    (hlo : 3868 ≤ i) (hhi : i ≤ 3885) :
    Artifact.submissionArtifact.instructionPC i =
      ([5323,5324,5325,5327,5328,5329,5331,5332,5333,5335,5336,5337,
        5339,5340,5341,5342,5343,5346] : List Nat)[i - 3868]! := by
  interval_cases i <;> decide

@[simp] theorem jump5323 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5323 = true :=
  Artifact.isValidJumpDest_index 3868 (by rfl)

def helperPrefixPath :
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
   pushAt 2453 2 5323,
   opAt 2454 .JUMPI]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 3868 .JUMPDEST,
   opAt 3869 (.Dup ⟨1, by decide⟩),
   pushAt 3870 1 3,
   opAt 3871 .LT,
   opAt 3872 (.Dup ⟨2, by decide⟩),
   pushAt 3873 1 7,
   opAt 3874 .LT,
   opAt 3875 (.Dup ⟨3, by decide⟩),
   pushAt 3876 1 15,
   opAt 3877 .LT,
   opAt 3878 (.Dup ⟨4, by decide⟩),
   pushAt 3879 1 31,
   opAt 3880 .LT,
   opAt 3881 .ADD,
   opAt 3882 .ADD,
   opAt 3883 .ADD,
   pushAt 3884 2 1569,
   opAt 3885 .JUMP]

def helperSmallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  helperPrefixPath ++
    [pushAt 2455 0 0,
     pushAt 2456 2 1569,
     opAt 2457 .JUMP]

def helperLargePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  helperPrefixPath ++ fallbackPath

@[simp] theorem jump1569 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1569 = true :=
  jumpDest1569

end Challenge.Modexp.Submission.Proofs.Bytecode.RrLeadingPaths
