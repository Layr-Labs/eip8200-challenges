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
    (hi : 2667 ≤ i) (hii : i ≤ 2703) :
    Artifact.submissionArtifact.instructionPC i =
      ([3615,3616,3617,3619,3620,3623,3624,3625,3627,3628,3629,3632,3633,3636,3637,3638,3639,3640,3642,3643,3644,3647,3648,3650,3653,3654,3655,3658,3659,3660,3662,3663,3667,3668,3669,3672,3673] : List Nat)[i - 2667]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2704 ≤ i) (hii : i ≤ 2736) :
    Artifact.submissionArtifact.instructionPC i =
      ([3675,3676,3677,3680,3683,3686,3689,3692,3693,3694,3696,3697,3698,3699,3702,3703,3704,3707,3710,3713,3716,3719,3720,3721,3724,3725,3726,3727,3730,3733,3734,3735,3738] : List Nat)[i - 2704]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2667 .JUMPDEST, opAt 2668 (.Dup ⟨3, by decide⟩),
   pushAt 2669 1 3, opAt 2670 .EQ, pushAt 2671 2 3654,
   opAt 2672 .JUMPI]

def oneWidth : List Located :=
  [opAt 2673 (.Dup ⟨3, by decide⟩), pushAt 2674 1 1,
   opAt 2675 .XOR, opAt 2676 .JUMPDEST, pushAt 2677 2 3725,
   opAt 2678 .JUMPI]

def checkThree : List Located :=
  [pushAt 2679 2 9472, opAt 2680 .MLOAD, opAt 2681 .CALLDATALOAD,
   pushAt 2682 0 0, opAt 2683 .BYTE, pushAt 2684 1 3,
   opAt 2685 .XOR, opAt 2686 .JUMPDEST, pushAt 2687 2 3725,
   opAt 2688 .JUMPI]

def threeHit : List Located :=
  [pushAt 2689 1 1, pushAt 2690 2 3675, opAt 2691 .JUMP]

def check65537 : List Located :=
  [opAt 2692 .JUMPDEST, pushAt 2693 2 9472, opAt 2694 .MLOAD,
   opAt 2695 .CALLDATALOAD, pushAt 2696 1 232, opAt 2697 .SHR,
   pushAt 2698 3 65537, opAt 2699 .XOR, opAt 2700 .JUMPDEST,
   pushAt 2701 2 3725, opAt 2702 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2703 1 16]

def start : List Located :=
  [opAt 2704 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2705 .JUMPDEST, pushAt 2706 2 3693, pushAt 2707 2 2048,
   pushAt 2708 2 2048, pushAt 2709 2 2048, pushAt 2710 2 4424,
   opAt 2711 .JUMP]

def squareReturn : List Located :=
  [opAt 2712 .JUMPDEST, pushAt 2713 1 1,
   opAt 2714 (.Swap ⟨0, by decide⟩), opAt 2715 .SUB,
   opAt 2716 (.Dup ⟨0, by decide⟩), pushAt 2717 2 3676,
   opAt 2718 .JUMPI]

def product : List Located :=
  [opAt 2719 .POP, pushAt 2720 2 3720, pushAt 2721 2 1024,
   pushAt 2722 2 1024, pushAt 2723 2 2048, pushAt 2724 2 4424,
   opAt 2725 .JUMP]

def finish : List Located :=
  [opAt 2726 .JUMPDEST, pushAt 2727 2 1867, opAt 2728 .JUMP]

def fallback : List Located :=
  [opAt 2729 .JUMPDEST, opAt 2730 (.Dup ⟨0, by decide⟩),
   pushAt 2731 2 4096, pushAt 2732 2 1024, opAt 2733 .MCOPY,
   pushAt 2734 0 0, pushAt 2735 2 1760, opAt 2736 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3615 = true :=
  Artifact.isValidJumpDest_index 2667 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3654 = true :=
  Artifact.isValidJumpDest_index 2692 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3675 = true :=
  Artifact.isValidJumpDest_index 2704 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3676 = true :=
  Artifact.isValidJumpDest_index 2705 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3693 = true :=
  Artifact.isValidJumpDest_index 2712 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3720 = true :=
  Artifact.isValidJumpDest_index 2726 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3725 = true :=
  Artifact.isValidJumpDest_index 2729 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
