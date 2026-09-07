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
    (hi : 2490 ≤ i) (hii : i ≤ 2526) :
    Artifact.submissionArtifact.instructionPC i =
      ([3892,3893,3894,3896,3897,3900,3901,3902,3904,3905,3906,3909,3910,3913,3914,3915,3916,3917,3919,3920,3921,3924,3925,3927,3930,3931,3932,3935,3936,3937,3939,3940,3944,3945,3946,3949,3950] : List Nat)[i - 2490]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2527 ≤ i) (hii : i ≤ 2559) :
    Artifact.submissionArtifact.instructionPC i =
      ([3952,3953,3954,3957,3960,3963,3966,3969,3970,3971,3973,3974,3975,3976,3979,3980,3981,3984,3987,3990,3993,3996,3997,3998,4001,4002,4003,4004,4007,4010,4011,4012,4015] : List Nat)[i - 2527]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2490 .JUMPDEST, opAt 2491 (.Dup ⟨3, by decide⟩),
   pushAt 2492 1 3, opAt 2493 .EQ, pushAt 2494 2 3931,
   opAt 2495 .JUMPI]

def oneWidth : List Located :=
  [opAt 2496 (.Dup ⟨3, by decide⟩), pushAt 2497 1 1,
   opAt 2498 .EQ, opAt 2499 .ISZERO, pushAt 2500 2 4002,
   opAt 2501 .JUMPI]

def checkThree : List Located :=
  [pushAt 2502 2 9472, opAt 2503 .MLOAD, opAt 2504 .CALLDATALOAD,
   pushAt 2505 0 0, opAt 2506 .BYTE, pushAt 2507 1 3,
   opAt 2508 .EQ, opAt 2509 .ISZERO, pushAt 2510 2 4002,
   opAt 2511 .JUMPI]

def threeHit : List Located :=
  [pushAt 2512 1 1, pushAt 2513 2 3952, opAt 2514 .JUMP]

def check65537 : List Located :=
  [opAt 2515 .JUMPDEST, pushAt 2516 2 9472, opAt 2517 .MLOAD,
   opAt 2518 .CALLDATALOAD, pushAt 2519 1 232, opAt 2520 .SHR,
   pushAt 2521 3 65537, opAt 2522 .EQ, opAt 2523 .ISZERO,
   pushAt 2524 2 4002, opAt 2525 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2526 1 16]

def start : List Located :=
  [opAt 2527 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2528 .JUMPDEST, pushAt 2529 2 3970, pushAt 2530 2 2048,
   pushAt 2531 2 2048, pushAt 2532 2 2048, pushAt 2533 2 1939,
   opAt 2534 .JUMP]

def squareReturn : List Located :=
  [opAt 2535 .JUMPDEST, pushAt 2536 1 1,
   opAt 2537 (.Swap ⟨0, by decide⟩), opAt 2538 .SUB,
   opAt 2539 (.Dup ⟨0, by decide⟩), pushAt 2540 2 3953,
   opAt 2541 .JUMPI]

def product : List Located :=
  [opAt 2542 .POP, pushAt 2543 2 3997, pushAt 2544 2 1024,
   pushAt 2545 2 1024, pushAt 2546 2 2048, pushAt 2547 2 1939,
   opAt 2548 .JUMP]

def finish : List Located :=
  [opAt 2549 .JUMPDEST, pushAt 2550 2 1876, opAt 2551 .JUMP]

def fallback : List Located :=
  [opAt 2552 .JUMPDEST, opAt 2553 (.Dup ⟨0, by decide⟩),
   pushAt 2554 2 4096, pushAt 2555 2 1024, opAt 2556 .MCOPY,
   pushAt 2557 0 0, pushAt 2558 2 1769, opAt 2559 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2490 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2515 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3952 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3953 = true :=
  Artifact.isValidJumpDest_index 2528 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2535 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2549 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2552 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
