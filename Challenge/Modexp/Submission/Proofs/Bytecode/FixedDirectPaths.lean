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
    (hi : 2662 ≤ i) (hii : i ≤ 2695) :
    Artifact.submissionArtifact.instructionPC i =
      ([3683,3684,3685,3687,3688,3691,3692,3693,3695,3696,3699,3700,3703,3704,3705,3706,3707,3709,3710,3713,3714,3716,3719,3720,3721,3724,3725,3726,3728,3729,3733,3734,3737,3738] : List Nat)[i - 2662]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2696 ≤ i) (hii : i ≤ 2728) :
    Artifact.submissionArtifact.instructionPC i =
      ([3740,3741,3742,3745,3748,3751,3754,3757,3758,3759,3761,3762,3763,3764,3767,3768,3769,3772,3775,3778,3781,3784,3785,3786,3789,3790,3791,3792,3795,3798,3799,3800,3803] : List Nat)[i - 2696]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2662 .JUMPDEST,
   opAt 2663 (.Dup ⟨3, by decide⟩),
   pushAt 2664 1 3,
   opAt 2665 .EQ,
   pushAt 2666 2 3720,
   opAt 2667 .JUMPI]

def oneWidth : List Located :=
  [opAt 2668 (.Dup ⟨3, by decide⟩),
   pushAt 2669 1 1,
   opAt 2670 .XOR,
   pushAt 2671 2 3790,
   opAt 2672 .JUMPI]

def checkThree : List Located :=
  [pushAt 2673 2 9472,
   opAt 2674 .MLOAD,
   opAt 2675 .CALLDATALOAD,
   pushAt 2676 0 0,
   opAt 2677 .BYTE,
   pushAt 2678 1 3,
   opAt 2679 .XOR,
   pushAt 2680 2 3790,
   opAt 2681 .JUMPI]

def threeHit : List Located :=
  [pushAt 2682 1 1,
   pushAt 2683 2 3740,
   opAt 2684 .JUMP]

def check65537 : List Located :=
  [opAt 2685 .JUMPDEST,
   pushAt 2686 2 9472,
   opAt 2687 .MLOAD,
   opAt 2688 .CALLDATALOAD,
   pushAt 2689 1 232,
   opAt 2690 .SHR,
   pushAt 2691 3 65537,
   opAt 2692 .XOR,
   pushAt 2693 2 3790,
   opAt 2694 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2695 1 16]

def start : List Located :=
  [opAt 2696 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2697 .JUMPDEST,
   pushAt 2698 2 3758,
   pushAt 2699 2 2048,
   pushAt 2700 2 2048,
   pushAt 2701 2 2048,
   pushAt 2702 2 4493,
   opAt 2703 .JUMP]

def squareReturn : List Located :=
  [opAt 2704 .JUMPDEST,
   pushAt 2705 1 1,
   opAt 2706 (.Swap ⟨0, by decide⟩),
   opAt 2707 .SUB,
   opAt 2708 (.Dup ⟨0, by decide⟩),
   pushAt 2709 2 3741,
   opAt 2710 .JUMPI]

def product : List Located :=
  [opAt 2711 .POP,
   pushAt 2712 2 3785,
   pushAt 2713 2 1024,
   pushAt 2714 2 1024,
   pushAt 2715 2 2048,
   pushAt 2716 2 4493,
   opAt 2717 .JUMP]

def finish : List Located :=
  [opAt 2718 .JUMPDEST,
   pushAt 2719 2 1807,
   opAt 2720 .JUMP]

def fallback : List Located :=
  [opAt 2721 .JUMPDEST,
   opAt 2722 (.Dup ⟨0, by decide⟩),
   pushAt 2723 2 4096,
   pushAt 2724 2 1024,
   opAt 2725 .MCOPY,
   pushAt 2726 0 0,
   pushAt 2727 2 1701,
   opAt 2728 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3683 = true :=
  Artifact.isValidJumpDest_index 2662 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3720 = true :=
  Artifact.isValidJumpDest_index 2685 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3740 = true :=
  Artifact.isValidJumpDest_index 2696 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3741 = true :=
  Artifact.isValidJumpDest_index 2697 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3758 = true :=
  Artifact.isValidJumpDest_index 2704 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3785 = true :=
  Artifact.isValidJumpDest_index 2718 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3790 = true :=
  Artifact.isValidJumpDest_index 2721 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
