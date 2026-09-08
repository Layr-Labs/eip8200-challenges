import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..4015 and instruction indices2572..2641.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2406 ≤ i) (hii : i ≤ 2442) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2406]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2443 ≤ i) (hii : i ≤ 2475) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2443]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2406 .JUMPDEST, opAt 2407 (.Dup ⟨3, by decide⟩),
   pushAt 2408 1 3, opAt 2409 .EQ, pushAt 2410 2 3926,
   opAt 2411 .JUMPI]

def oneWidth : List Located :=
  [opAt 2412 (.Dup ⟨3, by decide⟩), pushAt 2413 1 1,
   opAt 2414 .EQ, opAt 2415 .ISZERO, pushAt 2416 2 3997,
   opAt 2417 .JUMPI]

def checkThree : List Located :=
  [pushAt 2418 2 9472, opAt 2419 .MLOAD, opAt 2420 .CALLDATALOAD,
   pushAt 2421 0 0, opAt 2422 .BYTE, pushAt 2423 1 3,
   opAt 2424 .EQ, opAt 2425 .ISZERO, pushAt 2426 2 3997,
   opAt 2427 .JUMPI]

def threeHit : List Located :=
  [pushAt 2428 1 1, pushAt 2429 2 3947, opAt 2430 .JUMP]

def check65537 : List Located :=
  [opAt 2431 .JUMPDEST, pushAt 2432 2 9472, opAt 2433 .MLOAD,
   opAt 2434 .CALLDATALOAD, pushAt 2435 1 232, opAt 2436 .SHR,
   pushAt 2437 3 65537, opAt 2438 .EQ, opAt 2439 .ISZERO,
   pushAt 2440 2 3997, opAt 2441 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2442 1 16]

def start : List Located :=
  [opAt 2443 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2444 .JUMPDEST, pushAt 2445 2 3965, pushAt 2446 2 2048,
   pushAt 2447 2 2048, pushAt 2448 2 2048, pushAt 2449 2 1939,
   opAt 2450 .JUMP]

def squareReturn : List Located :=
  [opAt 2451 .JUMPDEST, pushAt 2452 1 1,
   opAt 2453 (.Swap ⟨0, by decide⟩), opAt 2454 .SUB,
   opAt 2455 (.Dup ⟨0, by decide⟩), pushAt 2456 2 3948,
   opAt 2457 .JUMPI]

def product : List Located :=
  [opAt 2458 .POP, pushAt 2459 2 3992, pushAt 2460 2 1024,
   pushAt 2461 2 1024, pushAt 2462 2 2048, pushAt 2463 2 1939,
   opAt 2464 .JUMP]

def finish : List Located :=
  [opAt 2465 .JUMPDEST, pushAt 2466 2 1876, opAt 2467 .JUMP]

def fallback : List Located :=
  [opAt 2468 .JUMPDEST, opAt 2469 (.Dup ⟨0, by decide⟩),
   pushAt 2470 2 4096, pushAt 2471 2 1024, opAt 2472 .MCOPY,
   pushAt 2473 0 0, pushAt 2474 2 1769, opAt 2475 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2406 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2431 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2443 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2444 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2451 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2465 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
