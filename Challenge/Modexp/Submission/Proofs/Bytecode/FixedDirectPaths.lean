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
    (hi : 2670 ≤ i) (hii : i ≤ 2706) :
    Artifact.submissionArtifact.instructionPC i =
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2670]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2707 ≤ i) (hii : i ≤ 2739) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2707]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2670 .JUMPDEST, opAt 2671 (.Dup ⟨3, by decide⟩),
   pushAt 2672 1 3, opAt 2673 .EQ, pushAt 2674 2 3690,
   opAt 2675 .JUMPI]

def oneWidth : List Located :=
  [opAt 2676 (.Dup ⟨3, by decide⟩), pushAt 2677 1 1,
   opAt 2678 .EQ, opAt 2679 .ISZERO, pushAt 2680 2 3761,
   opAt 2681 .JUMPI]

def checkThree : List Located :=
  [pushAt 2682 2 9472, opAt 2683 .MLOAD, opAt 2684 .CALLDATALOAD,
   pushAt 2685 0 0, opAt 2686 .BYTE, pushAt 2687 1 3,
   opAt 2688 .EQ, opAt 2689 .ISZERO, pushAt 2690 2 3761,
   opAt 2691 .JUMPI]

def threeHit : List Located :=
  [pushAt 2692 1 1, pushAt 2693 2 3711, opAt 2694 .JUMP]

def check65537 : List Located :=
  [opAt 2695 .JUMPDEST, pushAt 2696 2 9472, opAt 2697 .MLOAD,
   opAt 2698 .CALLDATALOAD, pushAt 2699 1 232, opAt 2700 .SHR,
   pushAt 2701 3 65537, opAt 2702 .EQ, opAt 2703 .ISZERO,
   pushAt 2704 2 3761, opAt 2705 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2706 1 16]

def start : List Located :=
  [opAt 2707 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2708 .JUMPDEST, pushAt 2709 2 3729, pushAt 2710 2 2048,
   pushAt 2711 2 2048, pushAt 2712 2 2048, pushAt 2713 2 4465,
   opAt 2714 .JUMP]

def squareReturn : List Located :=
  [opAt 2715 .JUMPDEST, pushAt 2716 1 1,
   opAt 2717 (.Swap ⟨0, by decide⟩), opAt 2718 .SUB,
   opAt 2719 (.Dup ⟨0, by decide⟩), pushAt 2720 2 3712,
   opAt 2721 .JUMPI]

def product : List Located :=
  [opAt 2722 .POP, pushAt 2723 2 3756, pushAt 2724 2 1024,
   pushAt 2725 2 1024, pushAt 2726 2 2048, pushAt 2727 2 4465,
   opAt 2728 .JUMP]

def finish : List Located :=
  [opAt 2729 .JUMPDEST, pushAt 2730 2 1876, opAt 2731 .JUMP]

def fallback : List Located :=
  [opAt 2732 .JUMPDEST, opAt 2733 (.Dup ⟨0, by decide⟩),
   pushAt 2734 2 4096, pushAt 2735 2 1024, opAt 2736 .MCOPY,
   pushAt 2737 0 0, pushAt 2738 2 1769, opAt 2739 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2670 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2707 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2708 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2732 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
