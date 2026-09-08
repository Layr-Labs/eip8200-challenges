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
    (hi : 2657 ≤ i) (hii : i ≤ 2693) :
    Artifact.submissionArtifact.instructionPC i =
      [3630,3631,3632,3634,3635,3638,3639,3640,3642,3643,3644,3647,3648,3651,3652,3653,3654,3655,3657,3658,3659,3662,3663,3665,3668,3669,3670,3673,3674,3675,3677,3678,3682,3683,3684,3687,3688][i - 2657]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2694 ≤ i) (hii : i ≤ 2726) :
    Artifact.submissionArtifact.instructionPC i =
      [3690,3691,3692,3695,3698,3701,3704,3707,3708,3709,3711,3712,3713,3714,3717,3718,3719,3722,3725,3728,3731,3734,3735,3736,3739,3740,3741,3742,3745,3748,3749,3750,3753][i - 2694]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2657 .JUMPDEST, opAt 2658 (.Dup ⟨3, by decide⟩),
   pushAt 2659 1 3, opAt 2660 .EQ, pushAt 2661 2 3669,
   opAt 2662 .JUMPI]

def oneWidth : List Located :=
  [opAt 2663 (.Dup ⟨3, by decide⟩), pushAt 2664 1 1,
   opAt 2665 .EQ, opAt 2666 .ISZERO, pushAt 2667 2 3740,
   opAt 2668 .JUMPI]

def checkThree : List Located :=
  [pushAt 2669 2 9472, opAt 2670 .MLOAD, opAt 2671 .CALLDATALOAD,
   pushAt 2672 0 0, opAt 2673 .BYTE, pushAt 2674 1 3,
   opAt 2675 .EQ, opAt 2676 .ISZERO, pushAt 2677 2 3740,
   opAt 2678 .JUMPI]

def threeHit : List Located :=
  [pushAt 2679 1 1, pushAt 2680 2 3690, opAt 2681 .JUMP]

def check65537 : List Located :=
  [opAt 2682 .JUMPDEST, pushAt 2683 2 9472, opAt 2684 .MLOAD,
   opAt 2685 .CALLDATALOAD, pushAt 2686 1 232, opAt 2687 .SHR,
   pushAt 2688 3 65537, opAt 2689 .EQ, opAt 2690 .ISZERO,
   pushAt 2691 2 3740, opAt 2692 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2693 1 16]

def start : List Located :=
  [opAt 2694 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2695 .JUMPDEST, pushAt 2696 2 3708, pushAt 2697 2 2048,
   pushAt 2698 2 2048, pushAt 2699 2 2048, pushAt 2700 2 4432,
   opAt 2701 .JUMP]

def squareReturn : List Located :=
  [opAt 2702 .JUMPDEST, pushAt 2703 1 1,
   opAt 2704 (.Swap ⟨0, by decide⟩), opAt 2705 .SUB,
   opAt 2706 (.Dup ⟨0, by decide⟩), pushAt 2707 2 3691,
   opAt 2708 .JUMPI]

def product : List Located :=
  [opAt 2709 .POP, pushAt 2710 2 3735, pushAt 2711 2 1024,
   pushAt 2712 2 1024, pushAt 2713 2 2048, pushAt 2714 2 4432,
   opAt 2715 .JUMP]

def finish : List Located :=
  [opAt 2716 .JUMPDEST, pushAt 2717 2 1867, opAt 2718 .JUMP]

def fallback : List Located :=
  [opAt 2719 .JUMPDEST, opAt 2720 (.Dup ⟨0, by decide⟩),
   pushAt 2721 2 4096, pushAt 2722 2 1024, opAt 2723 .MCOPY,
   pushAt 2724 0 0, pushAt 2725 2 1761, opAt 2726 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3630 = true :=
  Artifact.isValidJumpDest_index 2657 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3669 = true :=
  Artifact.isValidJumpDest_index 2682 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3690 = true :=
  Artifact.isValidJumpDest_index 2694 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3691 = true :=
  Artifact.isValidJumpDest_index 2695 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3708 = true :=
  Artifact.isValidJumpDest_index 2702 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3735 = true :=
  Artifact.isValidJumpDest_index 2716 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3740 = true :=
  Artifact.isValidJumpDest_index 2719 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
