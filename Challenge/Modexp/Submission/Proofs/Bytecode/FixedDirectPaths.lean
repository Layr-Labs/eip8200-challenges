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
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2678]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2715 ≤ i) (hii : i ≤ 2747) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2715]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2678 .JUMPDEST, opAt 2679 (.Dup ⟨3, by decide⟩),
   pushAt 2680 1 3, opAt 2681 .EQ, pushAt 2682 2 3690,
   opAt 2683 .JUMPI]

def oneWidth : List Located :=
  [opAt 2684 (.Dup ⟨3, by decide⟩), pushAt 2685 1 1,
   opAt 2686 .XOR, opAt 2687 .JUMPDEST, pushAt 2688 2 3761,
   opAt 2689 .JUMPI]

def checkThree : List Located :=
  [pushAt 2690 2 9472, opAt 2691 .MLOAD, opAt 2692 .CALLDATALOAD,
   pushAt 2693 0 0, opAt 2694 .BYTE, pushAt 2695 1 3,
   opAt 2696 .XOR, opAt 2697 .JUMPDEST, pushAt 2698 2 3761,
   opAt 2699 .JUMPI]

def threeHit : List Located :=
  [pushAt 2700 1 1, pushAt 2701 2 3711, opAt 2702 .JUMP]

def check65537 : List Located :=
  [opAt 2703 .JUMPDEST, pushAt 2704 2 9472, opAt 2705 .MLOAD,
   opAt 2706 .CALLDATALOAD, pushAt 2707 1 232, opAt 2708 .SHR,
   pushAt 2709 3 65537, opAt 2710 .XOR, opAt 2711 .JUMPDEST,
   pushAt 2712 2 3761, opAt 2713 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2714 1 16]

def start : List Located :=
  [opAt 2715 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2716 .JUMPDEST, pushAt 2717 2 3729, pushAt 2718 2 2048,
   pushAt 2719 2 2048, pushAt 2720 2 2048, pushAt 2721 2 4458,
   opAt 2722 .JUMP]

def squareReturn : List Located :=
  [opAt 2723 .JUMPDEST, pushAt 2724 1 1,
   opAt 2725 (.Swap ⟨0, by decide⟩), opAt 2726 .SUB,
   opAt 2727 (.Dup ⟨0, by decide⟩), pushAt 2728 2 3712,
   opAt 2729 .JUMPI]

def product : List Located :=
  [opAt 2730 .POP, pushAt 2731 2 3756, pushAt 2732 2 1024,
   pushAt 2733 2 1024, pushAt 2734 2 2048, pushAt 2735 2 4458,
   opAt 2736 .JUMP]

def finish : List Located :=
  [opAt 2737 .JUMPDEST, pushAt 2738 2 1876, opAt 2739 .JUMP]

def fallback : List Located :=
  [opAt 2740 .JUMPDEST, opAt 2741 (.Dup ⟨0, by decide⟩),
   pushAt 2742 2 4096, pushAt 2743 2 1024, opAt 2744 .MCOPY,
   pushAt 2745 0 0, pushAt 2746 2 1769, opAt 2747 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2678 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2703 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2716 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2723 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2737 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2740 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
