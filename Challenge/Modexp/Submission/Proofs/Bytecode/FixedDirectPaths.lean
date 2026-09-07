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

@[simp] theorem directPC0 (i : Nat) (hi : 2500 ≤ i) (hii : i ≤ 2536) :
    Artifact.submissionArtifact.instructionPC i =
      [3892,3893,3894,3896,3897,3900,3901,3902,3904,3905,
       3906,3909,3910,3913,3914,3915,3916,3917,3919,3920,
       3921,3924,3925,3927,3930,3931,3932,3935,3936,3937,
       3939,3940,3944,3945,3946,3949,3950][i - 2500]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2537 ≤ i) (hii : i ≤ 2569) :
    Artifact.submissionArtifact.instructionPC i =
      [3952,3953,3954,3957,3960,3963,3966,3969,3970,3971,
       3973,3974,3975,3976,3979,3980,3981,3984,3987,3990,
       3993,3996,3997,3998,4001,4002,4003,4004,4007,4010,
       4011,4012,4015][i - 2537]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2500 .JUMPDEST, opAt 2501 (.Dup ⟨3, by decide⟩),
   pushAt 2502 1 3, opAt 2503 .EQ, pushAt 2504 2 3931,
   opAt 2505 .JUMPI]

def oneWidth : List Located :=
  [opAt 2506 (.Dup ⟨3, by decide⟩), pushAt 2507 1 1,
   opAt 2508 .EQ, opAt 2509 .ISZERO, pushAt 2510 2 4002,
   opAt 2511 .JUMPI]

def checkThree : List Located :=
  [pushAt 2512 2 9472, opAt 2513 .MLOAD, opAt 2514 .CALLDATALOAD,
   pushAt 2515 0 0, opAt 2516 .BYTE, pushAt 2517 1 3,
   opAt 2518 .EQ, opAt 2519 .ISZERO, pushAt 2520 2 4002,
   opAt 2521 .JUMPI]

def threeHit : List Located :=
  [pushAt 2522 1 1, pushAt 2523 2 3952, opAt 2524 .JUMP]

def check65537 : List Located :=
  [opAt 2525 .JUMPDEST, pushAt 2526 2 9472, opAt 2527 .MLOAD,
   opAt 2528 .CALLDATALOAD, pushAt 2529 1 232, opAt 2530 .SHR,
   pushAt 2531 3 65537, opAt 2532 .EQ, opAt 2533 .ISZERO,
   pushAt 2534 2 4002, opAt 2535 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2536 1 16]

def start : List Located :=
  [opAt 2537 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2538 .JUMPDEST, pushAt 2539 2 3970, pushAt 2540 2 2048,
   pushAt 2541 2 2048, pushAt 2542 2 2048, pushAt 2543 2 1939,
   opAt 2544 .JUMP]

def squareReturn : List Located :=
  [opAt 2545 .JUMPDEST, pushAt 2546 1 1,
   opAt 2547 (.Swap ⟨0, by decide⟩), opAt 2548 .SUB,
   opAt 2549 (.Dup ⟨0, by decide⟩), pushAt 2550 2 3953,
   opAt 2551 .JUMPI]

def product : List Located :=
  [opAt 2552 .POP, pushAt 2553 2 3997, pushAt 2554 2 1024,
   pushAt 2555 2 1024, pushAt 2556 2 2048, pushAt 2557 2 1939,
   opAt 2558 .JUMP]

def finish : List Located :=
  [opAt 2559 .JUMPDEST, pushAt 2560 2 1876, opAt 2561 .JUMP]

def fallback : List Located :=
  [opAt 2562 .JUMPDEST, opAt 2563 (.Dup ⟨0, by decide⟩),
   pushAt 2564 2 4096, pushAt 2565 2 1024, opAt 2566 .MCOPY,
   pushAt 2567 0 0, pushAt 2568 2 1769, opAt 2569 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2500 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2525 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3952 = true :=
  Artifact.isValidJumpDest_index 2537 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3953 = true :=
  Artifact.isValidJumpDest_index 2538 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2545 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3997 = true :=
  Artifact.isValidJumpDest_index 2559 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4002 = true :=
  Artifact.isValidJumpDest_index 2562 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
