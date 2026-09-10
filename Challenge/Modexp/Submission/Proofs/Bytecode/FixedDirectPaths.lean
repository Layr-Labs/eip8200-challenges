import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..3779 and instruction indices2572..2308.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2630 ≤ i) (hii : i ≤ 2663) :
    Artifact.submissionArtifact.instructionPC i =
      ([3618,3619,3620,3622,3623,3626,3627,3628,3630,3631,3634,3635,3638,3639,3640,3641,3642,3644,3645,3648,3649,3651,3654,3655,3656,3659,3660,3661,3663,3664,3668,3669,3672,3673] : List Nat)[i - 2630]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2664 ≤ i) (hii : i ≤ 2696) :
    Artifact.submissionArtifact.instructionPC i =
      ([3675,3676,3677,3680,3683,3686,3689,3692,3693,3694,3696,3697,3698,3699,3702,3703,3704,3707,3710,3713,3716,3719,3720,3721,3724,3725,3726,3727,3730,3733,3734,3735,3738] : List Nat)[i - 2664]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2630 .JUMPDEST,
   opAt 2631 (.Dup ⟨3, by decide⟩),
   pushAt 2632 1 3,
   opAt 2633 .EQ,
   pushAt 2634 2 3655,
   opAt 2635 .JUMPI]

def oneWidth : List Located :=
  [opAt 2636 (.Dup ⟨3, by decide⟩),
   pushAt 2637 1 1,
   opAt 2638 .XOR,
   pushAt 2639 2 3725,
   opAt 2640 .JUMPI]

def checkThree : List Located :=
  [pushAt 2641 2 9472,
   opAt 2642 .MLOAD,
   opAt 2643 .CALLDATALOAD,
   pushAt 2644 0 0,
   opAt 2645 .BYTE,
   pushAt 2646 1 3,
   opAt 2647 .XOR,
   pushAt 2648 2 3725,
   opAt 2649 .JUMPI]

def threeHit : List Located :=
  [pushAt 2650 1 1,
   pushAt 2651 2 3675,
   opAt 2652 .JUMP]

def check65537 : List Located :=
  [opAt 2653 .JUMPDEST,
   pushAt 2654 2 9472,
   opAt 2655 .MLOAD,
   opAt 2656 .CALLDATALOAD,
   pushAt 2657 1 232,
   opAt 2658 .SHR,
   pushAt 2659 3 65537,
   opAt 2660 .XOR,
   pushAt 2661 2 3725,
   opAt 2662 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2663 1 16]

def start : List Located :=
  [opAt 2664 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2665 .JUMPDEST,
   pushAt 2666 2 3693,
   pushAt 2667 2 2048,
   pushAt 2668 2 2048,
   pushAt 2669 2 2048,
   pushAt 2670 2 4428,
   opAt 2671 .JUMP]

def squareReturn : List Located :=
  [opAt 2672 .JUMPDEST,
   pushAt 2673 1 1,
   opAt 2674 (.Swap ⟨0, by decide⟩),
   opAt 2675 .SUB,
   opAt 2676 (.Dup ⟨0, by decide⟩),
   pushAt 2677 2 3676,
   opAt 2678 .JUMPI]

def product : List Located :=
  [opAt 2679 .POP,
   pushAt 2680 2 3720,
   pushAt 2681 2 1024,
   pushAt 2682 2 1024,
   pushAt 2683 2 2048,
   pushAt 2684 2 4428,
   opAt 2685 .JUMP]

def finish : List Located :=
  [opAt 2686 .JUMPDEST,
   pushAt 2687 2 1857,
   opAt 2688 .JUMP]

def fallback : List Located :=
  [opAt 2689 .JUMPDEST,
   opAt 2690 (.Dup ⟨0, by decide⟩),
   pushAt 2691 2 4096,
   pushAt 2692 2 1024,
   opAt 2693 .MCOPY,
   pushAt 2694 0 0,
   pushAt 2695 2 1751,
   opAt 2696 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3618 = true :=
  Artifact.isValidJumpDest_index 2630 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3655 = true :=
  Artifact.isValidJumpDest_index 2653 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3675 = true :=
  Artifact.isValidJumpDest_index 2664 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3676 = true :=
  Artifact.isValidJumpDest_index 2665 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3693 = true :=
  Artifact.isValidJumpDest_index 2672 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3720 = true :=
  Artifact.isValidJumpDest_index 2686 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3725 = true :=
  Artifact.isValidJumpDest_index 2689 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
