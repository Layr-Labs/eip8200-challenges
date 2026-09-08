import Challenge.Modexp.Submission.Proofs.Bytecode.Artifact
import Challenge.Modexp.Submission.Proofs.Fast.Defs

set_option warningAsError true
set_option maxRecDepth 40000
set_option maxHeartbeats 4000000

/-!
# Exact located blocks for the direct fixed-exponent handler

The appended handler occupies pc3892..4015 and instruction indices2572..2641.
This file is the generated-Artifact boundary for its concrete trace proofs.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths

open EvmSemantics
open EvmSemantics.EVM
open Challenge.Modexp.Submission.Proofs.Fast

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

@[simp] theorem directPC0 (i : Nat)
    (hi : 2706 ≤ i) (hii : i ≤ 2742) :
    Artifact.submissionArtifact.instructionPC i =
      ([3905,3906,3907,3909,3910,3913,3914,3915,3917,3918,3919,3922,3923,3926,3927,3928,3929,3930,3932,3933,3934,3937,3938,3940,3943,3944,3945,3948,3949,3950,3952,3953,3957,3958,3959,3962,3963] : List Nat)[i - 2706]! := by
  interval_cases i <;> decide

@[simp] theorem directPC1 (i : Nat)
    (hi : 2743 ≤ i) (hii : i ≤ 2775) :
    Artifact.submissionArtifact.instructionPC i =
      ([3965,3966,3967,3970,3973,3976,3979,3982,3983,3984,3986,3987,3988,3989,3992,3993,3994,3997,4000,4003,4006,4009,4010,4011,4014,4015,4016,4017,4020,4023,4024,4025,4028] : List Nat)[i - 2743]! := by
  interval_cases i <;> decide

def entryPrefix : List Located :=
  [opAt 2706 .JUMPDEST, opAt 2707 (.Dup ⟨3, by decide⟩),
   pushAt 2708 1 3, opAt 2709 .EQ, pushAt 2710 2 3944,
   opAt 2711 .JUMPI]

def oneWidth : List Located :=
  [opAt 2712 (.Dup ⟨3, by decide⟩), pushAt 2713 1 1,
   opAt 2714 .EQ, opAt 2715 .ISZERO, pushAt 2716 2 4015,
   opAt 2717 .JUMPI]

def checkThree : List Located :=
  [pushAt 2718 2 9472, opAt 2719 .MLOAD, opAt 2720 .CALLDATALOAD,
   pushAt 2721 0 0, opAt 2722 .BYTE, pushAt 2723 1 3,
   opAt 2724 .EQ, opAt 2725 .ISZERO, pushAt 2726 2 4015,
   opAt 2727 .JUMPI]

def threeHit : List Located :=
  [pushAt 2728 1 1, pushAt 2729 2 3965, opAt 2730 .JUMP]

def check65537 : List Located :=
  [opAt 2731 .JUMPDEST, pushAt 2732 2 9472, opAt 2733 .MLOAD,
   opAt 2734 .CALLDATALOAD, pushAt 2735 1 232, opAt 2736 .SHR,
   pushAt 2737 3 65537, opAt 2738 .EQ, opAt 2739 .ISZERO,
   pushAt 2740 2 4015, opAt 2741 .JUMPI]

def fermatHit : List Located :=
  [pushAt 2742 1 16]

def start : List Located :=
  [opAt 2743 .JUMPDEST]

def squareCall : List Located :=
  [opAt 2744 .JUMPDEST, pushAt 2745 2 3983, pushAt 2746 2 2048,
   pushAt 2747 2 2048, pushAt 2748 2 2048, pushAt 2749 2 1939,
   opAt 2750 .JUMP]

def squareReturn : List Located :=
  [opAt 2751 .JUMPDEST, pushAt 2752 1 1,
   opAt 2753 (.Swap ⟨0, by decide⟩), opAt 2754 .SUB,
   opAt 2755 (.Dup ⟨0, by decide⟩), pushAt 2756 2 3966,
   opAt 2757 .JUMPI]

def product : List Located :=
  [opAt 2758 .POP, pushAt 2759 2 4010, pushAt 2760 2 1024,
   pushAt 2761 2 1024, pushAt 2762 2 2048, pushAt 2763 2 1939,
   opAt 2764 .JUMP]

def finish : List Located :=
  [opAt 2765 .JUMPDEST, pushAt 2766 2 1876, opAt 2767 .JUMP]

def fallback : List Located :=
  [opAt 2768 .JUMPDEST, opAt 2769 (.Dup ⟨0, by decide⟩),
   pushAt 2770 2 4096, pushAt 2771 2 1024, opAt 2772 .MCOPY,
   pushAt 2773 0 0, pushAt 2774 2 1769, opAt 2775 .JUMP]

theorem jumpDest3892 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3905 = true :=
  Artifact.isValidJumpDest_index 2706 (by rfl)

theorem jumpDest3931 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3944 = true :=
  Artifact.isValidJumpDest_index 2731 (by rfl)

theorem jumpDest3952 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3965 = true :=
  Artifact.isValidJumpDest_index 2743 (by rfl)

theorem jumpDest3953 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3966 = true :=
  Artifact.isValidJumpDest_index 2744 (by rfl)

theorem jumpDest3970 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 3983 = true :=
  Artifact.isValidJumpDest_index 2751 (by rfl)

theorem jumpDest3997 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4010 = true :=
  Artifact.isValidJumpDest_index 2765 (by rfl)

theorem jumpDest4002 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 4015 = true :=
  Artifact.isValidJumpDest_index 2768 (by rfl)

end Challenge.Modexp.Submission.Proofs.Bytecode.FixedDirectPaths
