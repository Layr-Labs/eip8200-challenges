import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def rawGuardBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2414 .JUMPDEST,
   opAt 2415 (.Dup ⟨2, by decide⟩),
   opAt 2416 (.Dup ⟨1, by decide⟩),
   opAt 2417 .EQ,
   opAt 2418 .ISZERO,
   pushAt 2419 2 3661,
   opAt 2420 .JUMPI]

def rawHitBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2421 (.Dup ⟨0, by decide⟩),
   pushAt 2422 1 96,
   pushAt 2423 2 2048,
   opAt 2424 .CALLDATACOPY,
   pushAt 2425 2 1755,
   pushAt 2426 2 2048,
   pushAt 2427 2 2048,
   pushAt 2428 2 6144,
   pushAt 2429 2 1939,
   opAt 2430 .JUMP]

@[simp] theorem rawPC (i : Nat) (hi : 2414 ≤ i) (hii : i < 2431) :
    Artifact.submissionArtifact.instructionPC i =
      [3695,3696,3697,3698,3699,3700,3703,3704,3705,3707,3710,3711,3714,3717,3720,3723,3726][i - 2414]! := by
  interval_cases i <;> rfl

end Challenge.Modexp.Submission.Proofs.Fast
