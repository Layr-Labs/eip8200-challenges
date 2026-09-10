import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The direct handler starts at pc3412 and bypasses the protected island via3423.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat) (hi : 2601 ≤ i) (hii : i ≤ 2640) :
    Artifact.submissionArtifact.instructionPC i =
      ([3412,3413,3414,3417,3418,3419,3422,3423,3424,3426,3427,3430,3431,3432,3434,3435,3438,3439,3442,3443,3444,3445,3446,3448,3449,3452,3453,3455,3458,3459,3460,3463,3464,3465,3467,3468,3472,3473,3476,3477] : List Nat)[i - 2601]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat) (hi : 2641 ≤ i) (hii : i ≤ 2673) :
    Artifact.submissionArtifact.instructionPC i =
      ([3479,3480,3481,3484,3487,3490,3493,3496,3497,3498,3500,3501,3502,3503,3506,3507,3508,3511,3514,3517,3520,3523,3524,3525,3528,3529,3530,3531,3534,3537,3538,3539,3542] : List Nat)[i - 2641]! := by
  interval_cases i <;> decide


def entryPrefix : List Located :=
  [opAt 2601 .JUMPDEST,
   opAt 2602 (.Dup ⟨3, by decide⟩),
   pushAt 2603 2 3423,
   opAt 2604 .JUMP,
   opAt 2608 .JUMPDEST,
   pushAt 2609 1 3,
   opAt 2610 .EQ,
   pushAt 2611 2 3459,
   opAt 2612 .JUMPI]

def oneWidth : List Located :=
  [opAt 2613 (.Dup ⟨3, by decide⟩),
   pushAt 2614 1 1,
   opAt 2615 .XOR,
   pushAt 2616 2 3529,
   opAt 2617 .JUMPI]

def checkThree : List Located :=
  [pushAt 2618 2 9472,
   opAt 2619 .MLOAD,
   opAt 2620 .CALLDATALOAD,
   pushAt 2621 0 0,
   opAt 2622 .BYTE,
   pushAt 2623 1 3,
   opAt 2624 .XOR,
   pushAt 2625 2 3529,
   opAt 2626 .JUMPI]

def threeHit : List Located :=
  [pushAt 2627 1 1,
   pushAt 2628 2 3479,
   opAt 2629 .JUMP]

def check65537 : List Located :=
  [opAt 2630 .JUMPDEST,
   pushAt 2631 2 9472,
   opAt 2632 .MLOAD,
   opAt 2633 .CALLDATALOAD,
   pushAt 2634 1 232,
   opAt 2635 .SHR,
   pushAt 2636 3 65537,
   opAt 2637 .XOR,
   pushAt 2638 2 3529,
   opAt 2639 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2640 1 16]

def start : List Located :=
  [opAt 2641 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2642 .JUMPDEST,
   pushAt 2643 2 3497,
   pushAt 2644 2 2048,
   pushAt 2645 2 2048,
   pushAt 2646 2 2048,
   pushAt 2647 2 4137,
   opAt 2648 .JUMP]

def squareReturn : List Located :=
  [opAt 2649 .JUMPDEST,
   pushAt 2650 1 1,
   opAt 2651 (.Swap ⟨0, by decide⟩),
   opAt 2652 .SUB,
   opAt 2653 (.Dup ⟨0, by decide⟩),
   pushAt 2654 2 3480,
   opAt 2655 .JUMPI]

def product : List Located :=
  [opAt 2656 .POP,
   pushAt 2657 2 3524,
   pushAt 2658 2 1024,
   pushAt 2659 2 1024,
   pushAt 2660 2 2048,
   pushAt 2661 2 4137,
   opAt 2662 .JUMP]

def finish : List Located :=
  [opAt 2663 .JUMPDEST,
   pushAt 2664 2 1802,
   opAt 2665 .JUMP]

def fallback : List Located :=
  [opAt 2666 .JUMPDEST,
   opAt 2667 (.Dup ⟨0, by decide⟩),
   pushAt 2668 2 4096,
   pushAt 2669 2 1024,
   opAt 2670 .MCOPY,
   pushAt 2671 0 0,
   pushAt 2672 2 1703,
   opAt 2673 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3412 = true :=
  Artifact.isValidJumpDest_index 2601 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3459 = true :=
  Artifact.isValidJumpDest_index 2630 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3479 = true :=
  Artifact.isValidJumpDest_index 2641 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3480 = true :=
  Artifact.isValidJumpDest_index 2642 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3497 = true :=
  Artifact.isValidJumpDest_index 2649 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3524 = true :=
  Artifact.isValidJumpDest_index 2663 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3529 = true :=
  Artifact.isValidJumpDest_index 2666 (by rfl)

/-- Actual bypass target around the protected word-path island. -/
theorem jumpBridge3423 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3423 = true :=
  Artifact.isValidJumpDest_index 2608 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
