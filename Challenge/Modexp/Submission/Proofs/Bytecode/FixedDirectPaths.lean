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
    (hi : 2464 ≤ i) (hii : i ≤ 2500) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2464]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2501 ≤ i) (hii : i ≤ 2533) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2501]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2437 .JUMPDEST, opAt 2438 (.Dup ⟨3, by decide⟩),
   pushAt 2439 1 3, opAt 2440 .EQ, pushAt 2441 2 3779,
   opAt 2442 .JUMPI]

def oneWidth : List Located :=
  [opAt 2443 (.Dup ⟨3, by decide⟩), pushAt 2444 1 1,
   opAt 2445 .EQ, opAt 2446 .ISZERO, pushAt 2447 2 3850,
   opAt 2448 .JUMPI]

def checkThree : List Located :=
  [pushAt 2449 2 9472, opAt 2450 .MLOAD, opAt 2451 .CALLDATALOAD,
   pushAt 2452 0 0, opAt 2453 .BYTE, pushAt 2454 1 3,
   opAt 2455 .EQ, opAt 2456 .ISZERO, pushAt 2457 2 3850,
   opAt 2458 .JUMPI]

def threeHit : List Located :=
  [pushAt 2459 1 1, pushAt 2460 2 3800, opAt 2461 .JUMP]

def check65537 : List Located :=
  [opAt 2462 .JUMPDEST, pushAt 2463 2 9472, opAt 2464 .MLOAD,
   opAt 2465 .CALLDATALOAD, pushAt 2466 1 232, opAt 2467 .SHR,
   pushAt 2468 3 65537, opAt 2469 .EQ, opAt 2470 .ISZERO,
   pushAt 2471 2 3850, opAt 2472 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2473 1 16]

def start : List Located :=
  [opAt 2474 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2475 .JUMPDEST, pushAt 2476 2 3818, pushAt 2477 2 2048,
   pushAt 2478 2 2048, pushAt 2479 2 2048, pushAt 2480 2 1908,
   opAt 2481 .JUMP]

def squareReturn : List Located :=
  [opAt 2482 .JUMPDEST, pushAt 2483 1 1,
   opAt 2484 (.Swap ⟨0, by decide⟩), opAt 2485 .SUB,
   opAt 2486 (.Dup ⟨0, by decide⟩), pushAt 2487 2 3801,
   opAt 2488 .JUMPI]

def product : List Located :=
  [opAt 2489 .POP, pushAt 2490 2 3845, pushAt 2491 2 1024,
   pushAt 2492 2 1024, pushAt 2493 2 2048, pushAt 2494 2 1908,
   opAt 2495 .JUMP]

def finish : List Located :=
  [opAt 2496 .JUMPDEST, pushAt 2497 2 1845, opAt 2498 .JUMP]

def fallback : List Located :=
  [opAt 2499 .JUMPDEST, opAt 2500 (.Dup ⟨0, by decide⟩),
   pushAt 2501 2 4096, pushAt 2502 2 1024, opAt 2503 .MCOPY,
   pushAt 2504 0 0, pushAt 2505 2 1739, opAt 2506 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3740 = true :=
  Artifact.isValidJumpDest_index 2437 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3779 = true :=
  Artifact.isValidJumpDest_index 2462 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3800 = true :=
  Artifact.isValidJumpDest_index 2474 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3801 = true :=
  Artifact.isValidJumpDest_index 2475 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3818 = true :=
  Artifact.isValidJumpDest_index 2482 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3845 = true :=
  Artifact.isValidJumpDest_index 2496 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3850 = true :=
  Artifact.isValidJumpDest_index 2499 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
