import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..4014 and instruction indices2572..2641.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2572 ≤ i) (hii : i ≤ 2608) :
    Artifact.submissionArtifact.instructionPC i =
      [3892,3893,3894,3896,3897,3900,3901,3902,3904,3905,
       3906,3909,3910,3913,3914,3915,3916,3917,3919,3920,
       3921,3924,3925,3927,3930,3931,3932,3935,3936,3937,
       3939,3940,3944,3945,3946,3949,3950][i - 2572]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2609 ≤ i) (hii : i ≤ 2641) :
    Artifact.submissionArtifact.instructionPC i =
      [3952,3953,3954,3957,3960,3963,3966,3969,3970,3971,
       3972,3973,3974,3975,3978,3979,3980,3983,3986,3989,
       3992,3995,3996,3997,4000,4001,4002,4003,4006,4009,
       4010,4011,4014][i - 2609]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2572 .JUMPDEST, opAt 2573 (.Dup ⟨3, by decide⟩),
   pushAt 2574 1 3, opAt 2575 .EQ, pushAt 2576 2 3931,
   opAt 2577 .JUMPI]

def oneWidth : List Located :=
  [opAt 2578 (.Dup ⟨3, by decide⟩), pushAt 2579 1 1,
   opAt 2580 .EQ, opAt 2581 .ISZERO, pushAt 2582 2 4001,
   opAt 2583 .JUMPI]

def checkThree : List Located :=
  [pushAt 2584 2 9472, opAt 2585 .MLOAD, opAt 2586 .CALLDATALOAD,
   pushAt 2587 0 0, opAt 2588 .BYTE, pushAt 2589 1 3,
   opAt 2590 .EQ, opAt 2591 .ISZERO, pushAt 2592 2 4001,
   opAt 2593 .JUMPI]

def threeHit : List Located :=
  [pushAt 2594 1 1, pushAt 2595 2 3952, opAt 2596 .JUMP]

def check65537 : List Located :=
  [opAt 2597 .JUMPDEST, pushAt 2598 2 9472, opAt 2599 .MLOAD,
   opAt 2600 .CALLDATALOAD, pushAt 2601 1 232, opAt 2602 .SHR,
   pushAt 2603 3 65537, opAt 2604 .EQ, opAt 2605 .ISZERO,
   pushAt 2606 2 4001, opAt 2607 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2608 1 16]

def start : List Located :=
  [opAt 2609 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2610 .JUMPDEST, pushAt 2611 2 3970, pushAt 2612 2 2048,
   pushAt 2613 2 2048, pushAt 2614 2 2048, pushAt 2615 2 1939,
   opAt 2616 .JUMP]

def squareReturn : List Located :=
  [opAt 2617 .JUMPDEST, pushAt 2618 0 0,
   opAt 2619 .NOT, opAt 2620 .ADD,
   opAt 2621 (.Dup ⟨0, by decide⟩), pushAt 2622 2 3953,
   opAt 2623 .JUMPI]

def product : List Located :=
  [opAt 2624 .POP, pushAt 2625 2 3996, pushAt 2626 2 1024,
   pushAt 2627 2 1024, pushAt 2628 2 2048, pushAt 2629 2 1939,
   opAt 2630 .JUMP]

def finish : List Located :=
  [opAt 2631 .JUMPDEST, pushAt 2632 2 1876, opAt 2633 .JUMP]

def fallback : List Located :=
  [opAt 2634 .JUMPDEST, opAt 2635 (.Dup ⟨0, by decide⟩),
   pushAt 2636 2 4096, pushAt 2637 2 1024, opAt 2638 .MCOPY,
   pushAt 2639 0 0, pushAt 2640 2 1769, opAt 2641 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3892 = true :=
  Artifact.isValidJumpDest_index 2572 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3931 = true :=
  Artifact.isValidJumpDest_index 2597 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3952 = true :=
  Artifact.isValidJumpDest_index 2609 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3953 = true :=
  Artifact.isValidJumpDest_index 2610 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3970 = true :=
  Artifact.isValidJumpDest_index 2617 (by rfl)

theorem jumpDest3996 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3996 = true :=
  Artifact.isValidJumpDest_index 2631 (by rfl)

theorem jumpDest4001 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4001 = true :=
  Artifact.isValidJumpDest_index 2634 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
