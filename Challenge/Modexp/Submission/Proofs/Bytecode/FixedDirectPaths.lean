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
    (hi : 2485 ≤ i) (hii : i ≤ 2521) :
    Artifact.submissionArtifact.instructionPC i =
      ([3892,3893,3894,3896,3897,3900,3901,3902,3904,3905,3906,3909,3910,3913,3914,3915,3916,3917,3919,3920,3921,3924,3925,3927,3930,3931,3932,3935,3936,3937,3939,3940,3944,3945,3946,3949,3950] : List Nat)[i - 2485]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2522 ≤ i) (hii : i ≤ 2554) :
    Artifact.submissionArtifact.instructionPC i =
      ([3952,3953,3954,3957,3960,3963,3966,3969,3970,3971,3973,3974,3975,3976,3979,3980,3981,3984,3987,3990,3993,3996,3997,3998,4001,4002,4003,4004,4007,4010,4011,4012,4015] : List Nat)[i - 2522]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2485 .JUMPDEST, opAt 2486 (.Dup ⟨3, by decide⟩),
   pushAt 2487 1 3, opAt 2488 .EQ, pushAt 2489 2 3931,
   opAt 2490 .JUMPI]

def oneWidth : List Located :=
  [opAt 2491 (.Dup ⟨3, by decide⟩), pushAt 2492 1 1,
   opAt 2493 .EQ, opAt 2494 .ISZERO, pushAt 2495 2 4002,
   opAt 2496 .JUMPI]

def checkThree : List Located :=
  [pushAt 2497 2 9472, opAt 2498 .MLOAD, opAt 2499 .CALLDATALOAD,
   pushAt 2500 0 0, opAt 2501 .BYTE, pushAt 2502 1 3,
   opAt 2503 .EQ, opAt 2504 .ISZERO, pushAt 2505 2 4002,
   opAt 2506 .JUMPI]

def threeHit : List Located :=
  [pushAt 2507 1 1, pushAt 2508 2 3952, opAt 2509 .JUMP]

def check65537 : List Located :=
  [opAt 2510 .JUMPDEST, pushAt 2511 2 9472, opAt 2512 .MLOAD,
   opAt 2513 .CALLDATALOAD, pushAt 2514 1 232, opAt 2515 .SHR,
   pushAt 2516 3 65537, opAt 2517 .EQ, opAt 2518 .ISZERO,
   pushAt 2519 2 4002, opAt 2520 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2521 1 16]

def start : List Located :=
  [opAt 2522 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2523 .JUMPDEST, pushAt 2524 2 3970, pushAt 2525 2 2048,
   pushAt 2526 2 2048, pushAt 2527 2 2048, pushAt 2528 2 1939,
   opAt 2529 .JUMP]

def squareReturn : List Located :=
  [opAt 2530 .JUMPDEST, pushAt 2531 1 1,
   opAt 2532 (.Swap ⟨0, by decide⟩), opAt 2533 .SUB,
   opAt 2534 (.Dup ⟨0, by decide⟩), pushAt 2535 2 3953,
   opAt 2536 .JUMPI]

def product : List Located :=
  [opAt 2537 .POP, pushAt 2538 2 3997, pushAt 2539 2 1024,
   pushAt 2540 2 1024, pushAt 2541 2 2048, pushAt 2542 2 1939,
   opAt 2543 .JUMP]

def finish : List Located :=
  [opAt 2544 .JUMPDEST, pushAt 2545 2 1876, opAt 2546 .JUMP]

def fallback : List Located :=
  [opAt 2547 .JUMPDEST, opAt 2548 (.Dup ⟨0, by decide⟩),
   pushAt 2549 2 4096, pushAt 2550 2 1024, opAt 2551 .MCOPY,
   pushAt 2552 0 0, pushAt 2553 2 1769, opAt 2554 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2485 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2510 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3952 = true :=
  Artifact.isValidJumpDest_index 2522 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3953 = true :=
  Artifact.isValidJumpDest_index 2523 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2544 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2547 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
