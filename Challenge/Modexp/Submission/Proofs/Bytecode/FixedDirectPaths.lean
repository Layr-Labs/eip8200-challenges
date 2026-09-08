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
    (hi : 2448 ≤ i) (hii : i ≤ 2484) :
    Artifact.submissionArtifact.instructionPC i =
      ([3887,3888,3889,3891,3892,3895,3896,3897,3899,3900,3901,3904,3905,3908,3909,3910,3911,3912,3914,3915,3916,3919,3920,3922,3925,3926,3927,3930,3931,3932,3934,3935,3939,3940,3941,3944,3945] : List Nat)[i - 2448]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2485 ≤ i) (hii : i ≤ 2517) :
    Artifact.submissionArtifact.instructionPC i =
      ([3947,3948,3949,3952,3955,3958,3961,3964,3965,3966,3968,3969,3970,3971,3974,3975,3976,3979,3982,3985,3988,3991,3992,3993,3996,3997,3998,3999,4002,4005,4006,4007,4010] : List Nat)[i - 2485]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2448 .JUMPDEST, opAt 2449 (.Dup ⟨3, by decide⟩),
   pushAt 2450 1 3, opAt 2451 .EQ, pushAt 2452 2 3926,
   opAt 2453 .JUMPI]

def oneWidth : List Located :=
  [opAt 2454 (.Dup ⟨3, by decide⟩), pushAt 2455 1 1,
   opAt 2456 .EQ, opAt 2457 .ISZERO, pushAt 2458 2 3997,
   opAt 2459 .JUMPI]

def checkThree : List Located :=
  [pushAt 2460 2 9472, opAt 2461 .MLOAD, opAt 2462 .CALLDATALOAD,
   pushAt 2463 0 0, opAt 2464 .BYTE, pushAt 2465 1 3,
   opAt 2466 .EQ, opAt 2467 .ISZERO, pushAt 2468 2 3997,
   opAt 2469 .JUMPI]

def threeHit : List Located :=
  [pushAt 2470 1 1, pushAt 2471 2 3947, opAt 2472 .JUMP]

def check65537 : List Located :=
  [opAt 2473 .JUMPDEST, pushAt 2474 2 9472, opAt 2475 .MLOAD,
   opAt 2476 .CALLDATALOAD, pushAt 2477 1 232, opAt 2478 .SHR,
   pushAt 2479 3 65537, opAt 2480 .EQ, opAt 2481 .ISZERO,
   pushAt 2482 2 3997, opAt 2483 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2484 1 16]

def start : List Located :=
  [opAt 2485 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2486 .JUMPDEST, pushAt 2487 2 3965, pushAt 2488 2 2048,
   pushAt 2489 2 2048, pushAt 2490 2 2048, pushAt 2491 2 1939,
   opAt 2492 .JUMP]

def squareReturn : List Located :=
  [opAt 2493 .JUMPDEST, pushAt 2494 1 1,
   opAt 2495 (.Swap ⟨0, by decide⟩), opAt 2496 .SUB,
   opAt 2497 (.Dup ⟨0, by decide⟩), pushAt 2498 2 3948,
   opAt 2499 .JUMPI]

def product : List Located :=
  [opAt 2500 .POP, pushAt 2501 2 3992, pushAt 2502 2 1024,
   pushAt 2503 2 1024, pushAt 2504 2 2048, pushAt 2505 2 1939,
   opAt 2506 .JUMP]

def finish : List Located :=
  [opAt 2507 .JUMPDEST, pushAt 2508 2 1876, opAt 2509 .JUMP]

def fallback : List Located :=
  [opAt 2510 .JUMPDEST, opAt 2511 (.Dup ⟨0, by decide⟩),
   pushAt 2512 2 4096, pushAt 2513 2 1024, opAt 2514 .MCOPY,
   pushAt 2515 0 0, pushAt 2516 2 1769, opAt 2517 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2448 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2473 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2486 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2493 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2507 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
