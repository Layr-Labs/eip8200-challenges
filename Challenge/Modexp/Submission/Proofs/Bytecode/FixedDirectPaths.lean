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
    (hi : 2666 ≤ i) (hii : i ≤ 2702) :
    Artifact.submissionArtifact.instructionPC i =
      ([3644,3645,3646,3648,3649,3652,3653,3654,3656,3657,3658,3661,3662,3665,3666,3667,3668,3669,3671,3672,3673,3676,3677,3679,3682,3683,3684,3687,3688,3689,3691,3692,3696,3697,3698,3701,3702] : List Nat)[i - 2666]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2703 ≤ i) (hii : i ≤ 2735) :
    Artifact.submissionArtifact.instructionPC i =
      ([3704,3705,3706,3709,3712,3715,3718,3721,3722,3723,3725,3726,3727,3728,3731,3732,3733,3736,3739,3742,3745,3748,3749,3750,3753,3754,3755,3756,3759,3762,3763,3764,3767] : List Nat)[i - 2703]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2666 .JUMPDEST, opAt 2667 (.Dup ⟨3, by decide⟩),
   pushAt 2668 1 3, opAt 2669 .EQ, pushAt 2670 2 3683,
   opAt 2671 .JUMPI]

def oneWidth : List Located :=
  [opAt 2672 (.Dup ⟨3, by decide⟩), pushAt 2673 1 1,
   opAt 2674 .XOR, opAt 2675 .JUMPDEST, pushAt 2676 2 3754,
   opAt 2677 .JUMPI]

def checkThree : List Located :=
  [pushAt 2678 2 9472, opAt 2679 .MLOAD, opAt 2680 .CALLDATALOAD,
   pushAt 2681 0 0, opAt 2682 .BYTE, pushAt 2683 1 3,
   opAt 2684 .XOR, opAt 2685 .JUMPDEST, pushAt 2686 2 3754,
   opAt 2687 .JUMPI]

def threeHit : List Located :=
  [pushAt 2688 1 1, pushAt 2689 2 3704, opAt 2690 .JUMP]

def check65537 : List Located :=
  [opAt 2691 .JUMPDEST, pushAt 2692 2 9472, opAt 2693 .MLOAD,
   opAt 2694 .CALLDATALOAD, pushAt 2695 1 232, opAt 2696 .SHR,
   pushAt 2697 3 65537, opAt 2698 .XOR, opAt 2699 .JUMPDEST,
   pushAt 2700 2 3754, opAt 2701 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2702 1 16]

def start : List Located :=
  [opAt 2703 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2704 .JUMPDEST, pushAt 2705 2 3722, pushAt 2706 2 2048,
   pushAt 2707 2 2048, pushAt 2708 2 2048, pushAt 2709 2 4453,
   opAt 2710 .JUMP]

def squareReturn : List Located :=
  [opAt 2711 .JUMPDEST, pushAt 2712 1 1,
   opAt 2713 (.Swap ⟨0, by decide⟩), opAt 2714 .SUB,
   opAt 2715 (.Dup ⟨0, by decide⟩), pushAt 2716 2 3705,
   opAt 2717 .JUMPI]

def product : List Located :=
  [opAt 2718 .POP, pushAt 2719 2 3749, pushAt 2720 2 1024,
   pushAt 2721 2 1024, pushAt 2722 2 2048, pushAt 2723 2 4453,
   opAt 2724 .JUMP]

def finish : List Located :=
  [opAt 2725 .JUMPDEST, pushAt 2726 2 1867, opAt 2727 .JUMP]

def fallback : List Located :=
  [opAt 2728 .JUMPDEST, opAt 2729 (.Dup ⟨0, by decide⟩),
   pushAt 2730 2 4096, pushAt 2731 2 1024, opAt 2732 .MCOPY,
   pushAt 2733 0 0, pushAt 2734 2 1760, opAt 2735 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3644 = true :=
  Artifact.isValidJumpDest_index 2666 (by rfl)

theorem jumpDest3895 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3683 = true :=
  Artifact.isValidJumpDest_index 2691 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3704 = true :=
  Artifact.isValidJumpDest_index 2703 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3705 = true :=
  Artifact.isValidJumpDest_index 2704 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3722 = true :=
  Artifact.isValidJumpDest_index 2711 (by rfl)

theorem jumpDest3954 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3749 = true :=
  Artifact.isValidJumpDest_index 2725 (by rfl)

theorem jumpDest3959 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3754 = true :=
  Artifact.isValidJumpDest_index 2728 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
