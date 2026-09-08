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
    (hi : 2440 ≤ i) (hii : i ≤ 2476) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2440]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2477 ≤ i) (hii : i ≤ 2509) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2477]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2440 .JUMPDEST, opAt 2441 (.Dup ⟨3, by decide⟩),
   pushAt 2442 1 3, opAt 2443 .EQ, pushAt 2444 2 3926,
   opAt 2445 .JUMPI]

def oneWidth : List Located :=
  [opAt 2446 (.Dup ⟨3, by decide⟩), pushAt 2447 1 1,
   opAt 2448 .EQ, opAt 2449 .ISZERO, pushAt 2450 2 3997,
   opAt 2451 .JUMPI]

def checkThree : List Located :=
  [pushAt 2452 2 9472, opAt 2453 .MLOAD, opAt 2454 .CALLDATALOAD,
   pushAt 2455 0 0, opAt 2456 .BYTE, pushAt 2457 1 3,
   opAt 2458 .EQ, opAt 2459 .ISZERO, pushAt 2460 2 3997,
   opAt 2461 .JUMPI]

def threeHit : List Located :=
  [pushAt 2462 1 1, pushAt 2463 2 3947, opAt 2464 .JUMP]

def check65537 : List Located :=
  [opAt 2465 .JUMPDEST, pushAt 2466 2 9472, opAt 2467 .MLOAD,
   opAt 2468 .CALLDATALOAD, pushAt 2469 1 232, opAt 2470 .SHR,
   pushAt 2471 3 65537, opAt 2472 .EQ, opAt 2473 .ISZERO,
   pushAt 2474 2 3997, opAt 2475 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2476 1 16]

def start : List Located :=
  [opAt 2477 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2478 .JUMPDEST, pushAt 2479 2 3965, pushAt 2480 2 2048,
   pushAt 2481 2 2048, pushAt 2482 2 2048, pushAt 2483 2 1939,
   opAt 2484 .JUMP]

def squareReturn : List Located :=
  [opAt 2485 .JUMPDEST, pushAt 2486 1 1,
   opAt 2487 (.Swap ⟨0, by decide⟩), opAt 2488 .SUB,
   opAt 2489 (.Dup ⟨0, by decide⟩), pushAt 2490 2 3948,
   opAt 2491 .JUMPI]

def product : List Located :=
  [opAt 2492 .POP, pushAt 2493 2 3992, pushAt 2494 2 1024,
   pushAt 2495 2 1024, pushAt 2496 2 2048, pushAt 2497 2 1939,
   opAt 2498 .JUMP]

def finish : List Located :=
  [opAt 2499 .JUMPDEST, pushAt 2500 2 1876, opAt 2501 .JUMP]

def fallback : List Located :=
  [opAt 2502 .JUMPDEST, opAt 2503 (.Dup ⟨0, by decide⟩),
   pushAt 2504 2 4096, pushAt 2505 2 1024, opAt 2506 .MCOPY,
   pushAt 2507 0 0, pushAt 2508 2 1769, opAt 2509 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2440 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2465 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2477 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2478 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2502 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
