import Challenge.Modexp.Submission.Proofs.Fast.Defs
set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Fast
open EvmSemantics EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Bytecode

def rawEntryBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1195 2 3606,
   opAt 1196 .JUMP]

def rawGuardBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2361 .JUMPDEST,
   opAt 2362 (.Dup ⟨2, by decide⟩),
   opAt 2363 (.Dup ⟨1, by decide⟩),
   opAt 2364 .EQ,
   opAt 2365 .ISZERO,
   pushAt 2366 2 3638,
   opAt 2367 .JUMPI]

def rawHitBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2368 (.Dup ⟨0, by decide⟩),
   pushAt 2369 1 96,
   pushAt 2370 2 2048,
   opAt 2371 .CALLDATACOPY,
   pushAt 2372 2 1755,
   pushAt 2373 2 2048,
   pushAt 2374 2 2048,
   pushAt 2375 2 6144,
   pushAt 2376 2 1939,
   opAt 2377 .JUMP]

def rawMissBlock : List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 2378 .JUMPDEST,
   opAt 2379 (.Dup ⟨2, by decide⟩),
   pushAt 2380 1 31,
   opAt 2381 .ADD,
   pushAt 2382 1 5,
   opAt 2383 .SHR,
   opAt 2384 (.Dup ⟨3, by decide⟩),
   opAt 2385 (.Dup ⟨1, by decide⟩),
   pushAt 2386 1 5,
   opAt 2387 .SHL,
   opAt 2388 .SUB,
   pushAt 2389 1 3,
   opAt 2390 .SHL,
   pushAt 2391 1 96,
   opAt 2392 .CALLDATALOAD,
   opAt 2393 (.Swap ⟨0, by decide⟩),
   opAt 2394 .SHR,
   opAt 2395 (.Dup ⟨2, by decide⟩),
   pushAt 2396 2 992,
   opAt 2397 .ADD,
   opAt 2398 .MSTORE,
   pushAt 2399 1 1,
   pushAt 2400 2 1668,
   opAt 2401 .JUMP]

@[simp] theorem rawPC (i : Nat) (hi : 2361 ≤ i) (hii : i < 2402) :
    Artifact.submissionArtifact.instructionPC i =
      [3606,3607,3608,3609,3610,3611,3614,3615,3616,3618,3621,3622,3625,3628,3631,3634,3637,3638,3639,3640,3642,3643,3645,3646,3647,3648,3650,3651,3652,3654,3655,3657,3658,3659,3660,3661,3664,3665,3666,3668,3671][i - 2361]! := by
  interval_cases i <;> rfl

theorem rawJump3606 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3606 = true :=
  Artifact.isValidJumpDest_index 2361 (by rfl)

theorem rawJump3638 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3638 = true :=
  Artifact.isValidJumpDest_index 2378 (by rfl)

theorem rawJump1668 : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1668 = true :=
  Artifact.isValidJumpDest_index 1216 (by rfl)

end Challenge.Modexp.Submission.Proofs.Fast
