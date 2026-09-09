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
    (hi : 2671 ≤ i) (hii : i ≤ 2707) :
    Artifact.submissionArtifact.instructionPC i =
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2671]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2708 ≤ i) (hii : i ≤ 2740) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2708]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2671 .JUMPDEST, opAt 2672 (.Dup ⟨3, by decide⟩),
   pushAt 2673 1 3, opAt 2674 .EQ, pushAt 2675 2 3690,
   opAt 2676 .JUMPI]

def oneWidth : List Located :=
  [opAt 2677 (.Dup ⟨3, by decide⟩), pushAt 2678 1 1,
   opAt 2679 .EQ, opAt 2680 .ISZERO, pushAt 2681 2 3761,
   opAt 2682 .JUMPI]

def checkThree : List Located :=
  [pushAt 2683 2 9472, opAt 2684 .MLOAD, opAt 2685 .CALLDATALOAD,
   pushAt 2686 0 0, opAt 2687 .BYTE, pushAt 2688 1 3,
   opAt 2689 .EQ, opAt 2690 .ISZERO, pushAt 2691 2 3761,
   opAt 2692 .JUMPI]

def threeHit : List Located :=
  [pushAt 2693 1 1, pushAt 2694 2 3711, opAt 2695 .JUMP]

def check65537 : List Located :=
  [opAt 2696 .JUMPDEST, pushAt 2697 2 9472, opAt 2698 .MLOAD,
   opAt 2699 .CALLDATALOAD, pushAt 2700 1 232, opAt 2701 .SHR,
   pushAt 2702 3 65537, opAt 2703 .EQ, opAt 2704 .ISZERO,
   pushAt 2705 2 3761, opAt 2706 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2707 1 16]

def start : List Located :=
  [opAt 2708 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2709 .JUMPDEST, pushAt 2710 2 3729, pushAt 2711 2 2048,
   pushAt 2712 2 2048, pushAt 2713 2 2048, pushAt 2714 2 4458,
   opAt 2715 .JUMP]

def squareReturn : List Located :=
  [opAt 2716 .JUMPDEST, pushAt 2717 1 1,
   opAt 2718 (.Swap ⟨0, by decide⟩), opAt 2719 .SUB,
   opAt 2720 (.Dup ⟨0, by decide⟩), pushAt 2721 2 3712,
   opAt 2722 .JUMPI]

def product : List Located :=
  [opAt 2723 .POP, pushAt 2724 2 3756, pushAt 2725 2 1024,
   pushAt 2726 2 1024, pushAt 2727 2 2048, pushAt 2728 2 4458,
   opAt 2729 .JUMP]

def finish : List Located :=
  [opAt 2730 .JUMPDEST, pushAt 2731 2 1876, opAt 2732 .JUMP]

def fallback : List Located :=
  [opAt 2733 .JUMPDEST, opAt 2734 (.Dup ⟨0, by decide⟩),
   pushAt 2735 2 4096, pushAt 2736 2 1024, opAt 2737 .MCOPY,
   pushAt 2738 0 0, pushAt 2739 2 1769, opAt 2740 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2671 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2696 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2708 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2709 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2716 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2730 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2733 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
