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
    (hi : 2669 ≤ i) (hii : i ≤ 2705) :
    Artifact.submissionArtifact.instructionPC i =
      ([3651,3652,3653,3655,3656,3659,3660,3661,3663,3664,3665,3668,3669,3672,3673,3674,3675,3676,3678,3679,3680,3683,3684,3686,3689,3690,3691,3694,3695,3696,3698,3699,3703,3704,3705,3708,3709] : List Nat)[i - 2669]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2706 ≤ i) (hii : i ≤ 2738) :
    Artifact.submissionArtifact.instructionPC i =
      ([3711,3712,3713,3716,3719,3722,3725,3728,3729,3730,3732,3733,3734,3735,3738,3739,3740,3743,3746,3749,3752,3755,3756,3757,3760,3761,3762,3763,3766,3769,3770,3771,3774] : List Nat)[i - 2706]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2669 .JUMPDEST, opAt 2670 (.Dup ⟨3, by decide⟩),
   pushAt 2671 1 3, opAt 2672 .EQ, pushAt 2673 2 3690,
   opAt 2674 .JUMPI]

def oneWidth : List Located :=
  [opAt 2675 (.Dup ⟨3, by decide⟩), pushAt 2676 1 1,
   opAt 2677 .EQ, opAt 2678 .ISZERO, pushAt 2679 2 3761,
   opAt 2680 .JUMPI]

def checkThree : List Located :=
  [pushAt 2681 2 9472, opAt 2682 .MLOAD, opAt 2683 .CALLDATALOAD,
   pushAt 2684 0 0, opAt 2685 .BYTE, pushAt 2686 1 3,
   opAt 2687 .EQ, opAt 2688 .ISZERO, pushAt 2689 2 3761,
   opAt 2690 .JUMPI]

def threeHit : List Located :=
  [pushAt 2691 1 1, pushAt 2692 2 3711, opAt 2693 .JUMP]

def check65537 : List Located :=
  [opAt 2694 .JUMPDEST, pushAt 2695 2 9472, opAt 2696 .MLOAD,
   opAt 2697 .CALLDATALOAD, pushAt 2698 1 232, opAt 2699 .SHR,
   pushAt 2700 3 65537, opAt 2701 .EQ, opAt 2702 .ISZERO,
   pushAt 2703 2 3761, opAt 2704 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2705 1 16]

def start : List Located :=
  [opAt 2706 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2707 .JUMPDEST, pushAt 2708 2 3729, pushAt 2709 2 2048,
   pushAt 2710 2 2048, pushAt 2711 2 2048, pushAt 2712 2 4458,
   opAt 2713 .JUMP]

def squareReturn : List Located :=
  [opAt 2714 .JUMPDEST, pushAt 2715 1 1,
   opAt 2716 (.Swap ⟨0, by decide⟩), opAt 2717 .SUB,
   opAt 2718 (.Dup ⟨0, by decide⟩), pushAt 2719 2 3712,
   opAt 2720 .JUMPI]

def product : List Located :=
  [opAt 2721 .POP, pushAt 2722 2 3756, pushAt 2723 2 1024,
   pushAt 2724 2 1024, pushAt 2725 2 2048, pushAt 2726 2 4458,
   opAt 2727 .JUMP]

def finish : List Located :=
  [opAt 2728 .JUMPDEST, pushAt 2729 2 1876, opAt 2730 .JUMP]

def fallback : List Located :=
  [opAt 2731 .JUMPDEST, opAt 2732 (.Dup ⟨0, by decide⟩),
   pushAt 2733 2 4096, pushAt 2734 2 1024, opAt 2735 .MCOPY,
   pushAt 2736 0 0, pushAt 2737 2 1769, opAt 2738 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3651 = true :=
  Artifact.isValidJumpDest_index 2669 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2694 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3711 = true :=
  Artifact.isValidJumpDest_index 2706 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2707 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3729 = true :=
  Artifact.isValidJumpDest_index 2714 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3756 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3761 = true :=
  Artifact.isValidJumpDest_index 2731 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
