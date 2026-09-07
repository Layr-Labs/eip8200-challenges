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
  [opAt 2464 .JUMPDEST, opAt 2465 (.Dup ⟨3, by decide⟩),
   pushAt 2466 1 3, opAt 2467 .EQ, pushAt 2468 2 3926,
   opAt 2469 .JUMPI]

def oneWidth : List Located :=
  [opAt 2470 (.Dup ⟨3, by decide⟩), pushAt 2471 1 1,
   opAt 2472 .EQ, opAt 2473 .ISZERO, pushAt 2474 2 3997,
   opAt 2475 .JUMPI]

def checkThree : List Located :=
  [pushAt 2476 2 9472, opAt 2477 .MLOAD, opAt 2478 .CALLDATALOAD,
   pushAt 2479 0 0, opAt 2480 .BYTE, pushAt 2481 1 3,
   opAt 2482 .EQ, opAt 2483 .ISZERO, pushAt 2484 2 3997,
   opAt 2485 .JUMPI]

def threeHit : List Located :=
  [pushAt 2486 1 1, pushAt 2487 2 3947, opAt 2488 .JUMP]

def check65537 : List Located :=
  [opAt 2489 .JUMPDEST, pushAt 2490 2 9472, opAt 2491 .MLOAD,
   opAt 2492 .CALLDATALOAD, pushAt 2493 1 232, opAt 2494 .SHR,
   pushAt 2495 3 65537, opAt 2496 .EQ, opAt 2497 .ISZERO,
   pushAt 2498 2 3997, opAt 2499 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2500 1 16]

def start : List Located :=
  [opAt 2501 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2502 .JUMPDEST, pushAt 2503 2 3965, pushAt 2504 2 2048,
   pushAt 2505 2 2048, pushAt 2506 2 2048, pushAt 2507 2 1939,
   opAt 2508 .JUMP]

def squareReturn : List Located :=
  [opAt 2509 .JUMPDEST, pushAt 2510 1 1,
   opAt 2511 (.Swap ⟨0, by decide⟩), opAt 2512 .SUB,
   opAt 2513 (.Dup ⟨0, by decide⟩), pushAt 2514 2 3948,
   opAt 2515 .JUMPI]

def product : List Located :=
  [opAt 2516 .POP, pushAt 2517 2 3992, pushAt 2518 2 1024,
   pushAt 2519 2 1024, pushAt 2520 2 2048, pushAt 2521 2 1939,
   opAt 2522 .JUMP]

def finish : List Located :=
  [opAt 2523 .JUMPDEST, pushAt 2524 2 1876, opAt 2525 .JUMP]

def fallback : List Located :=
  [opAt 2526 .JUMPDEST, opAt 2527 (.Dup ⟨0, by decide⟩),
   pushAt 2528 2 4096, pushAt 2529 2 1024, opAt 2530 .MCOPY,
   pushAt 2531 0 0, pushAt 2532 2 1769, opAt 2533 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3887 = true :=
  Artifact.isValidJumpDest_index 2464 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3926 = true :=
  Artifact.isValidJumpDest_index 2489 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3947 = true :=
  Artifact.isValidJumpDest_index 2501 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3948 = true :=
  Artifact.isValidJumpDest_index 2502 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2509 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3992 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2526 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
