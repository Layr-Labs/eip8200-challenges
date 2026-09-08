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
    (hi : 2424 ≤ i) (hii : i ≤ 2460) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2424]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2461 ≤ i) (hii : i ≤ 2493) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2461]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2424 .JUMPDEST, opAt 2425 (.Dup ⟨3, by decide⟩),
   pushAt 2426 1 3, opAt 2427 .EQ, pushAt 2428 2 3926,
   opAt 2429 .JUMPI]

def oneWidth : List Located :=
  [opAt 2430 (.Dup ⟨3, by decide⟩), pushAt 2431 1 1,
   opAt 2432 .EQ, opAt 2433 .ISZERO, pushAt 2434 2 3997,
   opAt 2435 .JUMPI]

def checkThree : List Located :=
  [pushAt 2436 2 9472, opAt 2437 .MLOAD, opAt 2438 .CALLDATALOAD,
   pushAt 2439 0 0, opAt 2440 .BYTE, pushAt 2441 1 3,
   opAt 2442 .EQ, opAt 2443 .ISZERO, pushAt 2444 2 3997,
   opAt 2445 .JUMPI]

def threeHit : List Located :=
  [pushAt 2446 1 1, pushAt 2447 2 3947, opAt 2448 .JUMP]

def check65537 : List Located :=
  [opAt 2449 .JUMPDEST, pushAt 2450 2 9472, opAt 2451 .MLOAD,
   opAt 2452 .CALLDATALOAD, pushAt 2453 1 232, opAt 2454 .SHR,
   pushAt 2455 3 65537, opAt 2456 .EQ, opAt 2457 .ISZERO,
   pushAt 2458 2 3997, opAt 2459 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2460 1 16]

def start : List Located :=
  [opAt 2461 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2462 .JUMPDEST, pushAt 2463 2 3965, pushAt 2464 2 2048,
   pushAt 2465 2 2048, pushAt 2466 2 2048, pushAt 2467 2 1939,
   opAt 2468 .JUMP]

def squareReturn : List Located :=
  [opAt 2469 .JUMPDEST, pushAt 2470 1 1,
   opAt 2471 (.Swap ⟨0, by decide⟩), opAt 2472 .SUB,
   opAt 2473 (.Dup ⟨0, by decide⟩), pushAt 2474 2 3948,
   opAt 2475 .JUMPI]

def product : List Located :=
  [opAt 2476 .POP, pushAt 2477 2 3992, pushAt 2478 2 1024,
   pushAt 2479 2 1024, pushAt 2480 2 2048, pushAt 2481 2 1939,
   opAt 2482 .JUMP]

def finish : List Located :=
  [opAt 2483 .JUMPDEST, pushAt 2484 2 1876, opAt 2485 .JUMP]

def fallback : List Located :=
  [opAt 2486 .JUMPDEST, opAt 2487 (.Dup ⟨0, by decide⟩),
   pushAt 2488 2 4096, pushAt 2489 2 1024, opAt 2490 .MCOPY,
   pushAt 2491 0 0, pushAt 2492 2 1769, opAt 2493 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2424 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2449 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2461 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2462 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2469 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2483 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2486 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
