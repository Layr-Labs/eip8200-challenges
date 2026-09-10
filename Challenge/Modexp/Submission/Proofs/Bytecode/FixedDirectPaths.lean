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
    (hi : 2650 ≤ i) (hii : i ≤ 2686) :
    Artifact.submissionArtifact.instructionPC i =
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2650]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2687 ≤ i) (hii : i ≤ 2719) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2687]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2650 .JUMPDEST, opAt 2651 (.Dup ⟨3, by decide⟩),
   pushAt 2652 1 3, opAt 2653 .EQ, pushAt 2654 2 3690,
   opAt 2655 .JUMPI]

def oneWidth : List Located :=
  [opAt 2656 (.Dup ⟨3, by decide⟩), pushAt 2657 1 1,
   opAt 2658 .XOR, opAt 2659 .JUMPDEST, pushAt 2660 2 3761,
   opAt 2661 .JUMPI]

def checkThree : List Located :=
  [pushAt 2662 2 9472, opAt 2663 .MLOAD, opAt 2664 .CALLDATALOAD,
   pushAt 2665 0 0, opAt 2666 .BYTE, pushAt 2667 1 3,
   opAt 2668 .XOR, opAt 2669 .JUMPDEST, pushAt 2670 2 3761,
   opAt 2671 .JUMPI]

def threeHit : List Located :=
  [pushAt 2672 1 1, pushAt 2673 2 3711, opAt 2674 .JUMP]

def check65537 : List Located :=
  [opAt 2675 .JUMPDEST, pushAt 2676 2 9472, opAt 2677 .MLOAD,
   opAt 2678 .CALLDATALOAD, pushAt 2679 1 232, opAt 2680 .SHR,
   pushAt 2681 3 65537, opAt 2682 .XOR, opAt 2683 .JUMPDEST,
   pushAt 2684 2 3761, opAt 2685 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2686 1 16]

def start : List Located :=
  [opAt 2687 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2688 .JUMPDEST, pushAt 2689 2 3729, pushAt 2690 2 2048,
   pushAt 2691 2 2048, pushAt 2692 2 2048, pushAt 2693 2 4465,
   opAt 2694 .JUMP]

def squareReturn : List Located :=
  [opAt 2695 .JUMPDEST, pushAt 2696 1 1,
   opAt 2697 (.Swap ⟨0, by decide⟩), opAt 2698 .SUB,
   opAt 2699 (.Dup ⟨0, by decide⟩), pushAt 2700 2 3712,
   opAt 2701 .JUMPI]

def product : List Located :=
  [opAt 2702 .POP, pushAt 2703 2 3756, pushAt 2704 2 1024,
   pushAt 2705 2 1024, pushAt 2706 2 2048, pushAt 2707 2 4465,
   opAt 2708 .JUMP]

def finish : List Located :=
  [opAt 2709 .JUMPDEST, pushAt 2710 2 1876, opAt 2711 .JUMP]

def fallback : List Located :=
  [opAt 2712 .JUMPDEST, opAt 2713 (.Dup ⟨0, by decide⟩),
   pushAt 2714 2 4096, pushAt 2715 2 1024, opAt 2716 .MCOPY,
   pushAt 2717 0 0, pushAt 2718 2 1769, opAt 2719 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2650 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2675 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2687 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2688 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2709 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2712 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
