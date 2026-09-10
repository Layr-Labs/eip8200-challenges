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
      ([3635,3636,3638,3639,3642,3643,3644,3646,3647,3648,3651,3652,3655,3656,3657,3658,3659,3661,3662,3663,3666,3667,3669,3672,3673,3674,3677,3678,3679,3681,3682,3686,3687,3688,3691,3692,3694] : List Nat)[i - 2678]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2715 ≤ i) (hii : i ≤ 2747) :
    Artifact.submissionArtifact.instructionPC i =
      ([3695,3696,3699,3702,3705,3708,3711,3712,3713,3715,3716,3717,3718,3721,3722,3723,3726,3729,3732,3735,3738,3739,3740,3743,3744,3745,3746,3749,3752,3753,3754,3757,3758] : List Nat)[i - 2715]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2677 .JUMPDEST, opAt 2678 (.Dup ⟨3, by decide⟩),
   pushAt 2679 1 3, opAt 2680 .EQ, pushAt 2681 2 3673,
   opAt 2682 .JUMPI]

def oneWidth : List Located :=
  [opAt 2683 (.Dup ⟨3, by decide⟩), pushAt 2684 1 1,
   opAt 2685 .EQ, opAt 2686 .ISZERO, pushAt 2687 2 3744,
   opAt 2688 .JUMPI]

def checkThree : List Located :=
  [pushAt 2689 2 9472, opAt 2690 .MLOAD, opAt 2691 .CALLDATALOAD,
   pushAt 2692 0 0, opAt 2693 .BYTE, pushAt 2694 1 3,
   opAt 2695 .EQ, opAt 2696 .ISZERO, pushAt 2697 2 3744,
   opAt 2698 .JUMPI]

def threeHit : List Located :=
  [pushAt 2699 1 1, pushAt 2700 2 3694, opAt 2701 .JUMP]

def check65537 : List Located :=
  [opAt 2702 .JUMPDEST, pushAt 2703 2 9472, opAt 2704 .MLOAD,
   opAt 2705 .CALLDATALOAD, pushAt 2706 1 232, opAt 2707 .SHR,
   pushAt 2708 3 65537, opAt 2709 .EQ, opAt 2710 .ISZERO,
   pushAt 2711 2 3744, opAt 2712 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2713 1 16]

def start : List Located :=
  [opAt 2714 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2715 .JUMPDEST, pushAt 2716 2 3712, pushAt 2717 2 2048,
   pushAt 2718 2 2048, pushAt 2719 2 2048, pushAt 2720 2 4440,
   opAt 2721 .JUMP]

def squareReturn : List Located :=
  [opAt 2722 .JUMPDEST, pushAt 2723 1 1,
   opAt 2724 (.Swap ⟨0, by decide⟩), opAt 2725 .SUB,
   opAt 2726 (.Dup ⟨0, by decide⟩), pushAt 2727 2 3695,
   opAt 2728 .JUMPI]

def product : List Located :=
  [opAt 2729 .POP, pushAt 2730 2 3739, pushAt 2731 2 1024,
   pushAt 2732 2 1024, pushAt 2733 2 2048, pushAt 2734 2 4440,
   opAt 2735 .JUMP]

def finish : List Located :=
  [opAt 2736 .JUMPDEST, pushAt 2737 2 1853, opAt 2738 .JUMP]

def fallback : List Located :=
  [opAt 2739 .JUMPDEST, opAt 2740 (.Dup ⟨0, by decide⟩),
   pushAt 2741 2 4096, pushAt 2742 2 1024, opAt 2743 .MCOPY,
   pushAt 2744 0 0, pushAt 2745 2 1746, opAt 2746 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3634 = true :=
  Artifact.isValidJumpDest_index 2677 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3673 = true :=
  Artifact.isValidJumpDest_index 2702 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3694 = true :=
  Artifact.isValidJumpDest_index 2714 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3695 = true :=
  Artifact.isValidJumpDest_index 2715 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3712 = true :=
  Artifact.isValidJumpDest_index 2722 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3739 = true :=
  Artifact.isValidJumpDest_index 2736 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3744 = true :=
  Artifact.isValidJumpDest_index 2739 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
