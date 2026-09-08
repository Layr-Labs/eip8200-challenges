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

@[simp] theorem directPC0 (i : Nat) (hi : 2468 ≤ i) (hii : i ≤ 2504) :
    Artifact.submissionArtifact.instructionPC i =
      [3892,3893,3894,3896,3897,3900,3901,3902,3904,3905,
       3906,3909,3910,3913,3914,3915,3916,3917,3919,3920,
       3921,3924,3925,3927,3930,3931,3932,3935,3936,3937,
       3939,3940,3944,3945,3946,3949,3950][i - 2468]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2505 ≤ i) (hii : i ≤ 2537) :
    Artifact.submissionArtifact.instructionPC i =
      [3952,3953,3954,3957,3960,3963,3966,3969,3970,3971,
       3973,3974,3975,3976,3979,3980,3981,3984,3987,3990,
       3993,3996,3997,3998,4001,4002,4003,4004,4007,4010,
       4011,4012,4015][i - 2505]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2468 .JUMPDEST, opAt 2469 (.Dup ⟨3, by decide⟩),
   pushAt 2470 1 3, opAt 2471 .EQ, pushAt 2472 2 3931,
   opAt 2473 .JUMPI]

def oneWidth : List Located :=
  [opAt 2474 (.Dup ⟨3, by decide⟩), pushAt 2475 1 1,
   opAt 2476 .EQ, opAt 2477 .ISZERO, pushAt 2478 2 4002,
   opAt 2479 .JUMPI]

def checkThree : List Located :=
  [pushAt 2480 2 9472, opAt 2481 .MLOAD, opAt 2482 .CALLDATALOAD,
   pushAt 2483 0 0, opAt 2484 .BYTE, pushAt 2485 1 3,
   opAt 2486 .EQ, opAt 2487 .ISZERO, pushAt 2488 2 4002,
   opAt 2489 .JUMPI]

def threeHit : List Located :=
  [pushAt 2490 1 1, pushAt 2491 2 3952, opAt 2492 .JUMP]

def check65537 : List Located :=
  [opAt 2493 .JUMPDEST, pushAt 2494 2 9472, opAt 2495 .MLOAD,
   opAt 2496 .CALLDATALOAD, pushAt 2497 1 232, opAt 2498 .SHR,
   pushAt 2499 3 65537, opAt 2500 .EQ, opAt 2501 .ISZERO,
   pushAt 2502 2 4002, opAt 2503 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2504 1 16]

def start : List Located :=
  [opAt 2505 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2506 .JUMPDEST, pushAt 2507 2 3970, pushAt 2508 2 2048,
   pushAt 2509 2 2048, pushAt 2510 2 2048, pushAt 2511 2 4057,
   opAt 2512 .JUMP]

def squareReturn : List Located :=
  [opAt 2513 .JUMPDEST, pushAt 2514 1 1,
   opAt 2515 (.Swap ⟨0, by decide⟩), opAt 2516 .SUB,
   opAt 2517 (.Dup ⟨0, by decide⟩), pushAt 2518 2 3953,
   opAt 2519 .JUMPI]

def product : List Located :=
  [opAt 2520 .POP, pushAt 2521 2 3997, pushAt 2522 2 1024,
   pushAt 2523 2 1024, pushAt 2524 2 2048, pushAt 2525 2 4057,
   opAt 2526 .JUMP]

def finish : List Located :=
  [opAt 2527 .JUMPDEST, pushAt 2528 2 1876, opAt 2529 .JUMP]

def fallback : List Located :=
  [opAt 2530 .JUMPDEST, opAt 2531 (.Dup ⟨0, by decide⟩),
   pushAt 2532 2 4096, pushAt 2533 2 1024, opAt 2534 .MCOPY,
   pushAt 2535 0 0, pushAt 2536 2 1769, opAt 2537 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2468 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2493 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3952 = true :=
  Artifact.isValidJumpDest_index 2505 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3953 = true :=
  Artifact.isValidJumpDest_index 2506 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2513 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2527 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2530 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
