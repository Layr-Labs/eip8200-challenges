import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The existing dispatcher occupies pc3615..3738. The exponent-five check is
the appended block at pc5325, with its hit returning to pc3675.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2669 ≤ i) (hii : i ≤ 2705) :
    Artifact.submissionArtifact.instructionPC i =
      ([3615,3616,3617,3619,3620,3623,3624,3625,3627,3628,3629,3632,3633,
       3636,3637,3638,3639,3640,3642,3643,3644,3647,3648,3650,
       3653,3654,3655,3658,3659,3660,3662,3663,3667,3668,3669,
       3672,3673] : List Nat)[i - 2669]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2706 ≤ i) (hii : i ≤ 2738) :
    Artifact.submissionArtifact.instructionPC i =
      ([3675,3676,3677,3680,3683,3686,3689,3692,3693,3694,3696,3697,3698,
       3699,3702,3703,3704,3707,3710,3713,3716,3719,3720,3721,
       3724,3725,3726,3727,3730,3733,3734,3735,3738] : List Nat)[i - 2706]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2669 .JUMPDEST, opAt 2670 (.Dup ⟨3, by decide⟩),
   pushAt 2671 1 3, opAt 2672 .EQ, pushAt 2673 2 3654,
   opAt 2674 .JUMPI]

def oneWidth : List Located :=
  [opAt 2675 (.Dup ⟨3, by decide⟩), pushAt 2676 1 1,
   opAt 2677 .EQ, opAt 2678 .ISZERO, pushAt 2679 2 3725,
   opAt 2680 .JUMPI]

def checkThree : List Located :=
  [pushAt 2681 2 9472, opAt 2682 .MLOAD, opAt 2683 .CALLDATALOAD,
   pushAt 2684 0 0, opAt 2685 .BYTE, pushAt 2686 1 3,
   opAt 2687 .EQ, opAt 2688 .ISZERO, pushAt 2689 2 5325,
   opAt 2690 .JUMPI]

def threeHit : List Located :=
  [pushAt 2691 1 1, pushAt 2692 2 3675, opAt 2693 .JUMP]

def checkFive : List Located :=
  [opAt 3866 .JUMPDEST, pushAt 3867 2 9472, opAt 3868 .MLOAD,
   opAt 3869 .CALLDATALOAD, pushAt 3870 0 0, opAt 3871 .BYTE,
   pushAt 3872 1 5, opAt 3873 .EQ, opAt 3874 .ISZERO,
   pushAt 3875 2 3725, opAt 3876 .JUMPI]

def fiveHit : List Located :=
  [pushAt 3877 1 2, pushAt 3878 2 3675, opAt 3879 .JUMP]

def check65537 : List Located :=
  [opAt 2694 .JUMPDEST, pushAt 2695 2 9472, opAt 2696 .MLOAD,
   opAt 2697 .CALLDATALOAD, pushAt 2698 1 232, opAt 2699 .SHR,
   pushAt 2700 3 65537, opAt 2701 .EQ, opAt 2702 .ISZERO,
   pushAt 2703 2 3725, opAt 2704 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2705 1 16]

def start : List Located :=
  [opAt 2706 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2707 .JUMPDEST, pushAt 2708 2 3693, pushAt 2709 2 2048,
   pushAt 2710 2 2048, pushAt 2711 2 2048, pushAt 2712 2 4424,
   opAt 2713 .JUMP]

def squareReturn : List Located :=
  [opAt 2714 .JUMPDEST, pushAt 2715 1 1,
   opAt 2716 (.Swap ⟨0, by decide⟩), opAt 2717 .SUB,
   opAt 2718 (.Dup ⟨0, by decide⟩), pushAt 2719 2 3676,
   opAt 2720 .JUMPI]

def product : List Located :=
  [opAt 2721 .POP, pushAt 2722 2 3720, pushAt 2723 2 1024,
   pushAt 2724 2 1024, pushAt 2725 2 2048, pushAt 2726 2 4424,
   opAt 2727 .JUMP]

def finish : List Located :=
  [opAt 2728 .JUMPDEST, pushAt 2729 2 1867, opAt 2730 .JUMP]

def fallback : List Located :=
  [opAt 2731 .JUMPDEST, opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 2 4096, pushAt 2734 2 1024, opAt 2735 .MCOPY,
   pushAt 2736 0 0, pushAt 2737 2 1760, opAt 2738 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3615 = true :=
  Artifact.isValidJumpDest_index 2669 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3654 = true :=
  Artifact.isValidJumpDest_index 2694 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3675 = true :=
  Artifact.isValidJumpDest_index 2706 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3676 = true :=
  Artifact.isValidJumpDest_index 2707 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3693 = true :=
  Artifact.isValidJumpDest_index 2714 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3720 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3725 = true :=
  Artifact.isValidJumpDest_index 2731 (by rfl)

theorem jumpDest5325 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 5325 = true :=
  Artifact.isValidJumpDest_index 3866 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
