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
    (hi : 2678 ≤ i) (hii : i ≤ 2714) :
    Artifact.submissionArtifact.instructionPC i =
      ([3636,3637,3638,3640,3641,3644,3645,3646,3648,3649,3650,3653,3654,3657,3658,3659,3660,3661,3663,3664,3665,3668,3669,3671,3674,3675,3676,3679,3680,3681,3683,3684,3688,3689,3690,3693,3694] : List Nat)[i - 2678]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2715 ≤ i) (hii : i ≤ 2747) :
    Artifact.submissionArtifact.instructionPC i =
      ([3696,3697,3698,3701,3704,3707,3710,3713,3714,3715,3717,3718,3719,3720,3723,3724,3725,3728,3731,3734,3737,3740,3741,3742,3745,3746,3747,3748,3751,3754,3755,3756,3759] : List Nat)[i - 2715]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2678 .JUMPDEST, opAt 2679 (.Dup ⟨3, by decide⟩),
   pushAt 2680 1 3, opAt 2681 .EQ, pushAt 2682 2 3675,
   opAt 2683 .JUMPI]

def oneWidth : List Located :=
  [opAt 2684 (.Dup ⟨3, by decide⟩), pushAt 2685 1 1,
   opAt 2686 .EQ, opAt 2687 .ISZERO, pushAt 2688 2 3746,
   opAt 2689 .JUMPI]

def checkThree : List Located :=
  [pushAt 2690 2 9472, opAt 2691 .MLOAD, opAt 2692 .CALLDATALOAD,
   pushAt 2693 0 0, opAt 2694 .BYTE, pushAt 2695 1 3,
   opAt 2696 .EQ, opAt 2697 .ISZERO, pushAt 2698 2 3746,
   opAt 2699 .JUMPI]

def threeHit : List Located :=
  [pushAt 2700 1 1, pushAt 2701 2 3696, opAt 2702 .JUMP]

def check65537 : List Located :=
  [opAt 2703 .JUMPDEST, pushAt 2704 2 9472, opAt 2705 .MLOAD,
   opAt 2706 .CALLDATALOAD, pushAt 2707 1 232, opAt 2708 .SHR,
   pushAt 2709 3 65537, opAt 2710 .EQ, opAt 2711 .ISZERO,
   pushAt 2712 2 3746, opAt 2713 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2714 1 16]

def start : List Located :=
  [opAt 2715 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2716 .JUMPDEST, pushAt 2717 2 3714, pushAt 2718 2 2048,
   pushAt 2719 2 2048, pushAt 2720 2 2048, pushAt 2721 2 4458,
   opAt 2722 .JUMP]

def squareReturn : List Located :=
  [opAt 2723 .JUMPDEST, pushAt 2724 1 1,
   opAt 2725 (.Swap ⟨0, by decide⟩), opAt 2726 .SUB,
   opAt 2727 (.Dup ⟨0, by decide⟩), pushAt 2728 2 3697,
   opAt 2729 .JUMPI]

def product : List Located :=
  [opAt 2730 .POP, pushAt 2731 2 3741, pushAt 2732 2 1024,
   pushAt 2733 2 1024, pushAt 2734 2 2048, pushAt 2735 2 4458,
   opAt 2736 .JUMP]

def finish : List Located :=
  [opAt 2737 .JUMPDEST, pushAt 2738 2 1876, opAt 2739 .JUMP]

def fallback : List Located :=
  [opAt 2740 .JUMPDEST, opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 2 4096, pushAt 2743 2 1024, opAt 2744 .MCOPY,
   pushAt 2745 0 0, pushAt 2746 2 1769, opAt 2747 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3636 = true :=
  Artifact.isValidJumpDest_index 2678 (by rfl)

theorem jumpDest3916 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3675 = true :=
  Artifact.isValidJumpDest_index 2703 (by rfl)

theorem jumpDest3937 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3696 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)

theorem jumpDest3938 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3697 = true :=
  Artifact.isValidJumpDest_index 2716 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3714 = true :=
  Artifact.isValidJumpDest_index 2723 (by rfl)

theorem jumpDest3982 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3741 = true :=
  Artifact.isValidJumpDest_index 2737 (by rfl)

theorem jumpDest3987 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3746 = true :=
  Artifact.isValidJumpDest_index 2740 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
