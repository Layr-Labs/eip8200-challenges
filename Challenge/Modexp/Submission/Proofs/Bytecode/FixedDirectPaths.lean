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
    (hi : 2658 ≤ i) (hii : i ≤ 2694) :
    Artifact.submissionArtifact.instructionPC i =
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2658]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2695 ≤ i) (hii : i ≤ 2727) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2695]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2658 .JUMPDEST, opAt 2659 (.Dup ⟨3, by decide⟩),
   pushAt 2660 1 3, opAt 2661 .EQ, pushAt 2662 2 3690,
   opAt 2663 .JUMPI]

def oneWidth : List Located :=
  [opAt 2664 (.Dup ⟨3, by decide⟩), pushAt 2665 1 1,
   opAt 2666 .EQ, opAt 2667 .ISZERO, pushAt 2668 2 3761,
   opAt 2669 .JUMPI]

def checkThree : List Located :=
  [pushAt 2670 2 9472, opAt 2671 .MLOAD, opAt 2672 .CALLDATALOAD,
   pushAt 2673 0 0, opAt 2674 .BYTE, pushAt 2675 1 3,
   opAt 2676 .EQ, opAt 2677 .ISZERO, pushAt 2678 2 3761,
   opAt 2679 .JUMPI]

def threeHit : List Located :=
  [pushAt 2680 1 1, pushAt 2681 2 3711, opAt 2682 .JUMP]

def check65537 : List Located :=
  [opAt 2683 .JUMPDEST, pushAt 2684 2 9472, opAt 2685 .MLOAD,
   opAt 2686 .CALLDATALOAD, pushAt 2687 1 232, opAt 2688 .SHR,
   pushAt 2689 3 65537, opAt 2690 .EQ, opAt 2691 .ISZERO,
   pushAt 2692 2 3761, opAt 2693 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2694 1 16]

def start : List Located :=
  [opAt 2695 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2696 .JUMPDEST, pushAt 2697 2 3729, pushAt 2698 2 2048,
   pushAt 2699 2 2048, pushAt 2700 2 2048, pushAt 2701 2 4458,
   opAt 2702 .JUMP]

def squareReturn : List Located :=
  [opAt 2703 .JUMPDEST, pushAt 2704 1 1,
   opAt 2705 (.Swap ⟨0, by decide⟩), opAt 2706 .SUB,
   opAt 2707 (.Dup ⟨0, by decide⟩), pushAt 2708 2 3712,
   opAt 2709 .JUMPI]

def product : List Located :=
  [opAt 2710 .POP, pushAt 2711 2 3756, pushAt 2712 2 1024,
   pushAt 2713 2 1024, pushAt 2714 2 2048, pushAt 2715 2 4458,
   opAt 2716 .JUMP]

def finish : List Located :=
  [opAt 2717 .JUMPDEST, pushAt 2718 2 1876, opAt 2719 .JUMP]

def fallback : List Located :=
  [opAt 2720 .JUMPDEST, opAt 2721 (.Dup ⟨0, by decide⟩),
   pushAt 2722 2 4096, pushAt 2723 2 1024, opAt 2724 .MCOPY,
   pushAt 2725 0 0, pushAt 2726 2 1769, opAt 2727 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2658 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2683 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2696 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2703 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2717 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2720 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
