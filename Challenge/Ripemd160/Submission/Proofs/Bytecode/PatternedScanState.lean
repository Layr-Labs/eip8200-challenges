import Batteries.Tactic.OpenPrivate
import Challenge.Ripemd160.Submission.Proofs.Bytecode.ArtifactSegment
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedSwar
import Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedGuardSpec
import Challenge.EvmProof.Stepper
import Challenge.Ripemd160.ProofSupport.InitialState
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

set_option warningAsError true
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-!
# States and paths of the scalar-SWAR patterned-1000 guard

The guard carries the expected word forward instead of storing thirty-two of
them, so the scan is one loop: `wordPath` derives the word and routes the four
straddling offsets to `straddlePath`, and `comparePath` folds the difference
into the accumulator and advances the offset and the scalar.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan

open Challenge.Ripemd160 Challenge.EvmProof EvmSemantics EvmSemantics.EVM
open PatternedInputData PatternedDigest PatternedGuardSpec PatternedSwar


open private
  submissionInstructionsChunk0
  submissionInstructionsChunk1
  submissionInstructionsChunk2
  submissionInstructionsChunk3
  submissionInstructionsChunk4
  submissionInstructionsChunk5
  submissionInstructionsChunk6
  submissionInstructionsChunk7
  submissionInstructionsChunk8
  submissionInstructionsChunk9
  submissionInstructionsChunk10
  submissionInstructionsChunk11
  submissionInstructionsChunk12
  submissionInstructionsChunk13
  submissionInstructionsChunk14
  submissionInstructionsChunk15
  submissionInstructionsChunk16
  submissionInstructionsChunk17
  submissionInstructionsChunk0_length
  submissionInstructionsChunk1_length
  submissionInstructionsChunk2_length
  submissionInstructionsChunk3_length
  submissionInstructionsChunk4_length
  submissionInstructionsChunk5_length
  submissionInstructionsChunk6_length
  submissionInstructionsChunk7_length
  submissionInstructionsChunk8_length
  submissionInstructionsChunk9_length
  submissionInstructionsChunk10_length
  submissionInstructionsChunk11_length
  submissionInstructionsChunk12_length
  submissionInstructionsChunk13_length
  submissionInstructionsChunk14_length
  submissionInstructionsChunk15_length
  submissionInstructionsChunk16_length
  submissionInstructionsChunk17_length
  from Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact

private def scanPrefix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk0 ++
    submissionInstructionsChunk1 ++
    submissionInstructionsChunk2 ++
    submissionInstructionsChunk3 ++
    submissionInstructionsChunk4 ++
    submissionInstructionsChunk5 ++
    submissionInstructionsChunk6 ++
    submissionInstructionsChunk7 ++
    submissionInstructionsChunk8 ++
    submissionInstructionsChunk9 ++
    submissionInstructionsChunk10 ++
    submissionInstructionsChunk11 ++
    submissionInstructionsChunk12 ++
    submissionInstructionsChunk13 ++
    submissionInstructionsChunk14 ++
    submissionInstructionsChunk15 ++
    submissionInstructionsChunk16

private def scanBefore : List YulEvmCompiler.Instr :=
  scanPrefix ++ submissionInstructionsChunk17.take 32

private def scanSuffix : List YulEvmCompiler.Instr :=
  submissionInstructionsChunk17.drop 32

private theorem scanBefore_length : scanBefore.length = 3657 := by
  simp [scanBefore, scanPrefix]

private theorem scanSuffix_length : scanSuffix.length = 127 := by
  simp [scanSuffix]

private theorem artifact_scan_split :
    Artifact.submissionArtifact.instructions = scanBefore ++ scanSuffix ++ [] := by
  change Artifact.submissionInstructions = _
  have hprefix : Artifact.submissionInstructions =
      scanPrefix ++ submissionInstructionsChunk17 := by
    simp only [Artifact.submissionInstructions, scanPrefix, List.append_assoc]
  have hchunk : submissionInstructionsChunk17 =
      submissionInstructionsChunk17.take 32 ++ submissionInstructionsChunk17.drop 32 := by
    exact (List.take_append_drop 32 submissionInstructionsChunk17).symm
  rw [hprefix]
  conv_lhs => rw [hchunk]
  simp only [scanBefore, scanSuffix, List.append_assoc, List.append_nil]

private theorem scanBefore_pc :
    (YulEvmCompiler.assembleBytes scanBefore).length = 5139 := by rfl

private theorem artifact_instruction_projection :
    Artifact.submissionArtifact.instructions = Artifact.submissionInstructions := by rfl

private theorem scan_instruction_at (index : Nat)
    (hlo : 3657 ≤ index) (hhi : index < 3784) :
    Artifact.submissionInstructions[index]? = scanSuffix[index - 3657]? := by
  have hi : index - 3657 < scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.getElem?_segment Artifact.submissionArtifact
    scanBefore scanSuffix [] artifact_scan_split (index - 3657) hi
  simpa only [artifact_instruction_projection, scanBefore_length,
    Nat.add_sub_of_le hlo] using h

private theorem scan_instruction_pc (index : Nat)
    (hlo : 3657 ≤ index) (hhi : index ≤ 3784) :
    Artifact.submissionArtifact.instructionPC index =
      5139 + (YulEvmCompiler.assembleBytes (scanSuffix.take (index - 3657))).length := by
  have hi : index - 3657 ≤ scanSuffix.length := by
    rw [scanSuffix_length]
    omega
  have h := ArtifactSegment.instructionPC_segment_of_bounds Artifact.submissionArtifact
    scanBefore scanSuffix [] 3657 5139 artifact_scan_split scanBefore_length
    scanBefore_pc (index - 3657) hi
  simpa only [Nat.add_sub_of_le hlo] using h

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

abbrev Located := Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by
      first
      | rw [scan_instruction_at] <;> first | rfl | decide
      | rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) : Located :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by
      first
      | rw [scan_instruction_at] <;> first | rfl | decide
      | rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) : Located :=
  ⟨index, .push width value, hget, hwf⟩

abbrev run := Challenge.EvmProof.Stepper.runLocatedBlock
  (artifact := Artifact.submissionArtifact) (fork := .Osaka)

/-- Push the five constants and start the scan. -/
def setupPath : List Located :=
  [opAt 3657 .JUMPDEST,
   pushAt 3658 1 255,
   pushAt 3659 0 0,
   opAt 3660 .NOT,
   opAt 3661 .DIV,
   pushAt 3662 32 3244493450063667868678674439968361782956185527883176199882357678282131398018,
   opAt 3663 (.Dup ⟨1, by decide⟩),
   pushAt 3664 1 7,
   opAt 3665 .SHL,
   opAt 3666 (.Dup ⟨0, by decide⟩),
   opAt 3667 .NOT,
   opAt 3668 (.Swap ⟨0, by decide⟩),
   opAt 3669 (.Swap ⟨2, by decide⟩),
   opAt 3670 (.Dup ⟨2, by decide⟩),
   opAt 3671 (.Dup ⟨2, by decide⟩),
   opAt 3672 .AND,
   pushAt 3673 0 0,
   pushAt 3674 0 0,
   pushAt 3675 0 0]

/-- Derive the expected word and test for a straddler. -/
def wordPath : List Located :=
  [opAt 3676 .JUMPDEST, opAt 3677 (.Dup ⟨0, by decide⟩),
   opAt 3678 (.Dup ⟨5, by decide⟩), opAt 3679 .MUL,
   opAt 3680 (.Dup ⟨0, by decide⟩), opAt 3681 (.Dup ⟨7, by decide⟩),
   opAt 3682 .AND, opAt 3683 (.Dup ⟨5, by decide⟩), opAt 3684 .ADD,
   opAt 3685 (.Dup ⟨1, by decide⟩), opAt 3686 (.Dup ⟨9, by decide⟩),
   opAt 3687 .XOR, opAt 3688 (.Dup ⟨10, by decide⟩), opAt 3689 .AND,
   opAt 3690 .XOR, opAt 3691 (.Dup ⟨3, by decide⟩), pushAt 3692 1 255,
   opAt 3693 .AND, pushAt 3694 1 224, opAt 3695 .EQ, pushAt 3696 2 5312,
   opAt 3697 .JUMPI]

/-- Fold one word into the accumulator and advance. -/
def comparePath : List Located :=
  [opAt 3698 .JUMPDEST, opAt 3699 (.Dup ⟨3, by decide⟩),
   opAt 3700 .CALLDATALOAD, opAt 3701 .XOR, opAt 3702 (.Dup ⟨4, by decide⟩),
   opAt 3703 .OR, opAt 3704 (.Swap ⟨3, by decide⟩), opAt 3705 .POP,
   opAt 3706 .POP, opAt 3707 .JUMPDEST, pushAt 3708 1 160,
   opAt 3709 .ADD, pushAt 3710 1 255, opAt 3711 .AND,
   opAt 3712 .JUMPDEST, opAt 3713 .JUMPDEST,
   opAt 3714 (.Swap ⟨0, by decide⟩), pushAt 3715 1 32, opAt 3716 .ADD,
   opAt 3717 (.Swap ⟨0, by decide⟩), opAt 3718 .JUMPDEST,
   opAt 3719 (.Dup ⟨1, by decide⟩), pushAt 3720 2 992, opAt 3721 .GT,
   pushAt 3722 2 5192, opAt 3723 .JUMPI]

/-- The padded tail word, the cleanup and the miss test. -/
def tailPath : List Located :=
  [pushAt 3724 2 992, opAt 3725 .CALLDATALOAD,
   pushAt 3726 8 9848759918901945995, pushAt 3727 1 192, opAt 3728 .SHL,
   opAt 3729 .XOR, opAt 3730 (.Dup ⟨3, by decide⟩), opAt 3731 .OR,
   opAt 3732 (.Swap ⟨2, by decide⟩), opAt 3733 .POP,
   opAt 3734 (.Swap ⟨1, by decide⟩), opAt 3735 (.Swap ⟨6, by decide⟩),
   opAt 3736 .POP, opAt 3737 .POP, opAt 3738 .POP, opAt 3739 .POP,
   opAt 3740 .POP, opAt 3741 .POP, opAt 3742 .POP, pushAt 3743 2 972,
   opAt 3744 .JUMPI]

/-- Store and return the stored digest. -/
def returnPath : List Located :=
  [pushAt 3745 20 766350606435067737561421097975693824639675460820,
   pushAt 3746 0 0, opAt 3747 .MSTORE, pushAt 3748 1 32, pushAt 3749 0 0,
   opAt 3750 .RETURN]

/-- Shift the correction constant out of `M`. -/
def straddleCorrPath : List Located :=
  [opAt 3751 .JUMPDEST, opAt 3752 (.Dup ⟨6, by decide⟩),
   opAt 3753 (.Dup ⟨4, by decide⟩), pushAt 3754 1 8, opAt 3755 .SHR,
   pushAt 3756 1 5, opAt 3757 .MUL, pushAt 3758 1 27, opAt 3759 .SUB,
   pushAt 3760 1 8, opAt 3761 .MUL, opAt 3762 .SHR, pushAt 3763 1 11,
   opAt 3764 .MUL]

/-- Apply the correction to the expected word. -/
def straddleAddPath : List Located :=
  [opAt 3765 (.Dup ⟨1, by decide⟩), opAt 3766 (.Dup ⟨9, by decide⟩),
   opAt 3767 .AND, opAt 3768 (.Dup ⟨1, by decide⟩), opAt 3769 .ADD,
   opAt 3770 (.Dup ⟨2, by decide⟩), opAt 3771 (.Dup ⟨12, by decide⟩),
   opAt 3772 .AND, opAt 3773 .XOR, opAt 3774 (.Swap ⟨1, by decide⟩),
   opAt 3775 .POP, opAt 3776 .POP]

/-- Bump the scalar and rejoin the scan. -/
def straddleBackPath : List Located :=
  [opAt 3777 (.Dup ⟨2, by decide⟩), pushAt 3778 1 11, opAt 3779 .ADD,
   opAt 3780 (.Swap ⟨2, by decide⟩), opAt 3781 .POP, pushAt 3782 2 5218,
   opAt 3783 .JUMP]


@[simp] theorem pc2903 : Artifact.submissionArtifact.instructionPC 3657 = 0x1413 :=
  by rw [scan_instruction_pc 3657 (by decide) (by decide)]; rfl
@[simp] theorem pc2904 : Artifact.submissionArtifact.instructionPC 3658 = 0x1414 :=
  by rw [scan_instruction_pc 3658 (by decide) (by decide)]; rfl
@[simp] theorem pc2905 : Artifact.submissionArtifact.instructionPC 3662 = 0x1419 :=
  by rw [scan_instruction_pc 3662 (by decide) (by decide)]; rfl
@[simp] theorem pc2906 : Artifact.submissionArtifact.instructionPC 3667 = 0x143f :=
  by rw [scan_instruction_pc 3667 (by decide) (by decide)]; rfl
@[simp] theorem pc2907 : Artifact.submissionArtifact.instructionPC 3669 = 0x1441 :=
  by rw [scan_instruction_pc 3669 (by decide) (by decide)]; rfl
@[simp] theorem pc2908 : Artifact.submissionArtifact.instructionPC 3670 = 0x1442 :=
  by rw [scan_instruction_pc 3670 (by decide) (by decide)]; rfl
@[simp] theorem pc2909 : Artifact.submissionArtifact.instructionPC 3671 = 0x1443 :=
  by rw [scan_instruction_pc 3671 (by decide) (by decide)]; rfl
@[simp] theorem pc2910 : Artifact.submissionArtifact.instructionPC 3672 = 0x1444 :=
  by rw [scan_instruction_pc 3672 (by decide) (by decide)]; rfl
@[simp] theorem pc2911 : Artifact.submissionArtifact.instructionPC 3673 = 0x1445 :=
  by rw [scan_instruction_pc 3673 (by decide) (by decide)]; rfl
@[simp] theorem pc2912 : Artifact.submissionArtifact.instructionPC 3674 = 0x1446 :=
  by rw [scan_instruction_pc 3674 (by decide) (by decide)]; rfl
@[simp] theorem pc2913 : Artifact.submissionArtifact.instructionPC 3675 = 0x1447 :=
  by rw [scan_instruction_pc 3675 (by decide) (by decide)]; rfl
@[simp] theorem pc2914 : Artifact.submissionArtifact.instructionPC 3676 = 0x1448 :=
  by rw [scan_instruction_pc 3676 (by decide) (by decide)]; rfl
@[simp] theorem pc2915 : Artifact.submissionArtifact.instructionPC 3677 = 0x1449 :=
  by rw [scan_instruction_pc 3677 (by decide) (by decide)]; rfl
@[simp] theorem pc2916 : Artifact.submissionArtifact.instructionPC 3678 = 0x144a :=
  by rw [scan_instruction_pc 3678 (by decide) (by decide)]; rfl
@[simp] theorem pc2917 : Artifact.submissionArtifact.instructionPC 3679 = 0x144b :=
  by rw [scan_instruction_pc 3679 (by decide) (by decide)]; rfl
@[simp] theorem pc2918 : Artifact.submissionArtifact.instructionPC 3680 = 0x144c :=
  by rw [scan_instruction_pc 3680 (by decide) (by decide)]; rfl
@[simp] theorem pc2919 : Artifact.submissionArtifact.instructionPC 3681 = 0x144d :=
  by rw [scan_instruction_pc 3681 (by decide) (by decide)]; rfl
@[simp] theorem pc2920 : Artifact.submissionArtifact.instructionPC 3682 = 0x144e :=
  by rw [scan_instruction_pc 3682 (by decide) (by decide)]; rfl
@[simp] theorem pc2921 : Artifact.submissionArtifact.instructionPC 3683 = 0x144f :=
  by rw [scan_instruction_pc 3683 (by decide) (by decide)]; rfl
@[simp] theorem pc2922 : Artifact.submissionArtifact.instructionPC 3684 = 0x1450 :=
  by rw [scan_instruction_pc 3684 (by decide) (by decide)]; rfl
@[simp] theorem pc2923 : Artifact.submissionArtifact.instructionPC 3685 = 0x1451 :=
  by rw [scan_instruction_pc 3685 (by decide) (by decide)]; rfl
@[simp] theorem pc2924 : Artifact.submissionArtifact.instructionPC 3686 = 0x1452 :=
  by rw [scan_instruction_pc 3686 (by decide) (by decide)]; rfl
@[simp] theorem pc2925 : Artifact.submissionArtifact.instructionPC 3687 = 0x1453 :=
  by rw [scan_instruction_pc 3687 (by decide) (by decide)]; rfl
@[simp] theorem pc2926 : Artifact.submissionArtifact.instructionPC 3688 = 0x1454 :=
  by rw [scan_instruction_pc 3688 (by decide) (by decide)]; rfl
@[simp] theorem pc2927 : Artifact.submissionArtifact.instructionPC 3689 = 0x1455 :=
  by rw [scan_instruction_pc 3689 (by decide) (by decide)]; rfl
@[simp] theorem pc2928 : Artifact.submissionArtifact.instructionPC 3690 = 0x1456 :=
  by rw [scan_instruction_pc 3690 (by decide) (by decide)]; rfl
@[simp] theorem pc2929 : Artifact.submissionArtifact.instructionPC 3691 = 0x1457 :=
  by rw [scan_instruction_pc 3691 (by decide) (by decide)]; rfl
@[simp] theorem pc2930 : Artifact.submissionArtifact.instructionPC 3692 = 0x1458 :=
  by rw [scan_instruction_pc 3692 (by decide) (by decide)]; rfl
@[simp] theorem pc2931 : Artifact.submissionArtifact.instructionPC 3693 = 0x145a :=
  by rw [scan_instruction_pc 3693 (by decide) (by decide)]; rfl
@[simp] theorem pc2932 : Artifact.submissionArtifact.instructionPC 3694 = 0x145b :=
  by rw [scan_instruction_pc 3694 (by decide) (by decide)]; rfl
@[simp] theorem pc2933 : Artifact.submissionArtifact.instructionPC 3695 = 0x145d :=
  by rw [scan_instruction_pc 3695 (by decide) (by decide)]; rfl
@[simp] theorem pc2934 : Artifact.submissionArtifact.instructionPC 3696 = 0x145e :=
  by rw [scan_instruction_pc 3696 (by decide) (by decide)]; rfl
@[simp] theorem pc2935 : Artifact.submissionArtifact.instructionPC 3697 = 0x1461 :=
  by rw [scan_instruction_pc 3697 (by decide) (by decide)]; rfl
@[simp] theorem pc2936 : Artifact.submissionArtifact.instructionPC 3698 = 0x1462 :=
  by rw [scan_instruction_pc 3698 (by decide) (by decide)]; rfl
@[simp] theorem pc2937 : Artifact.submissionArtifact.instructionPC 3699 = 0x1463 :=
  by rw [scan_instruction_pc 3699 (by decide) (by decide)]; rfl
@[simp] theorem pc2938 : Artifact.submissionArtifact.instructionPC 3700 = 0x1464 :=
  by rw [scan_instruction_pc 3700 (by decide) (by decide)]; rfl
@[simp] theorem pc2939 : Artifact.submissionArtifact.instructionPC 3701 = 0x1465 :=
  by rw [scan_instruction_pc 3701 (by decide) (by decide)]; rfl
@[simp] theorem pc2940 : Artifact.submissionArtifact.instructionPC 3702 = 0x1466 :=
  by rw [scan_instruction_pc 3702 (by decide) (by decide)]; rfl
@[simp] theorem pc2941 : Artifact.submissionArtifact.instructionPC 3703 = 0x1467 :=
  by rw [scan_instruction_pc 3703 (by decide) (by decide)]; rfl
@[simp] theorem pc2942 : Artifact.submissionArtifact.instructionPC 3704 = 0x1468 :=
  by rw [scan_instruction_pc 3704 (by decide) (by decide)]; rfl
@[simp] theorem pc2943 : Artifact.submissionArtifact.instructionPC 3705 = 0x1469 :=
  by rw [scan_instruction_pc 3705 (by decide) (by decide)]; rfl
@[simp] theorem pc2944 : Artifact.submissionArtifact.instructionPC 3706 = 0x146a :=
  by rw [scan_instruction_pc 3706 (by decide) (by decide)]; rfl
@[simp] theorem pc2945 : Artifact.submissionArtifact.instructionPC 3707 = 0x146b :=
  by rw [scan_instruction_pc 3707 (by decide) (by decide)]; rfl
@[simp] theorem pc2946 : Artifact.submissionArtifact.instructionPC 3708 = 0x146c :=
  by rw [scan_instruction_pc 3708 (by decide) (by decide)]; rfl
@[simp] theorem pc2947 : Artifact.submissionArtifact.instructionPC 3709 = 0x146e :=
  by rw [scan_instruction_pc 3709 (by decide) (by decide)]; rfl
@[simp] theorem pc2948 : Artifact.submissionArtifact.instructionPC 3710 = 0x146f :=
  by rw [scan_instruction_pc 3710 (by decide) (by decide)]; rfl
@[simp] theorem pc2949 : Artifact.submissionArtifact.instructionPC 3711 = 0x1471 :=
  by rw [scan_instruction_pc 3711 (by decide) (by decide)]; rfl
@[simp] theorem pc2950 : Artifact.submissionArtifact.instructionPC 3712 = 0x1472 :=
  by rw [scan_instruction_pc 3712 (by decide) (by decide)]; rfl
@[simp] theorem pc2951 : Artifact.submissionArtifact.instructionPC 3713 = 0x1473 :=
  by rw [scan_instruction_pc 3713 (by decide) (by decide)]; rfl
@[simp] theorem pc2952 : Artifact.submissionArtifact.instructionPC 3714 = 0x1474 :=
  by rw [scan_instruction_pc 3714 (by decide) (by decide)]; rfl
@[simp] theorem pc2953 : Artifact.submissionArtifact.instructionPC 3715 = 0x1475 :=
  by rw [scan_instruction_pc 3715 (by decide) (by decide)]; rfl
@[simp] theorem pc2954 : Artifact.submissionArtifact.instructionPC 3716 = 0x1477 :=
  by rw [scan_instruction_pc 3716 (by decide) (by decide)]; rfl
@[simp] theorem pc2955 : Artifact.submissionArtifact.instructionPC 3717 = 0x1478 :=
  by rw [scan_instruction_pc 3717 (by decide) (by decide)]; rfl
@[simp] theorem pc2956 : Artifact.submissionArtifact.instructionPC 3718 = 0x1479 :=
  by rw [scan_instruction_pc 3718 (by decide) (by decide)]; rfl
@[simp] theorem pc2957 : Artifact.submissionArtifact.instructionPC 3719 = 0x147a :=
  by rw [scan_instruction_pc 3719 (by decide) (by decide)]; rfl
@[simp] theorem pc2958 : Artifact.submissionArtifact.instructionPC 3720 = 0x147b :=
  by rw [scan_instruction_pc 3720 (by decide) (by decide)]; rfl
@[simp] theorem pc2959 : Artifact.submissionArtifact.instructionPC 3721 = 0x147e :=
  by rw [scan_instruction_pc 3721 (by decide) (by decide)]; rfl
@[simp] theorem pc2960 : Artifact.submissionArtifact.instructionPC 3722 = 0x147f :=
  by rw [scan_instruction_pc 3722 (by decide) (by decide)]; rfl
@[simp] theorem pc2961 : Artifact.submissionArtifact.instructionPC 3723 = 0x1482 :=
  by rw [scan_instruction_pc 3723 (by decide) (by decide)]; rfl
@[simp] theorem pc2962 : Artifact.submissionArtifact.instructionPC 3724 = 0x1483 :=
  by rw [scan_instruction_pc 3724 (by decide) (by decide)]; rfl
@[simp] theorem pc2963 : Artifact.submissionArtifact.instructionPC 3725 = 0x1486 :=
  by rw [scan_instruction_pc 3725 (by decide) (by decide)]; rfl
@[simp] theorem pc2964 : Artifact.submissionArtifact.instructionPC 3726 = 0x1487 :=
  by rw [scan_instruction_pc 3726 (by decide) (by decide)]; rfl
@[simp] theorem pc2965 : Artifact.submissionArtifact.instructionPC 3727 = 0x1490 :=
  by rw [scan_instruction_pc 3727 (by decide) (by decide)]; rfl
@[simp] theorem pc2966 : Artifact.submissionArtifact.instructionPC 3728 = 0x1492 :=
  by rw [scan_instruction_pc 3728 (by decide) (by decide)]; rfl
@[simp] theorem pc2967 : Artifact.submissionArtifact.instructionPC 3729 = 0x1493 :=
  by rw [scan_instruction_pc 3729 (by decide) (by decide)]; rfl
@[simp] theorem pc2968 : Artifact.submissionArtifact.instructionPC 3730 = 0x1494 :=
  by rw [scan_instruction_pc 3730 (by decide) (by decide)]; rfl
@[simp] theorem pc2969 : Artifact.submissionArtifact.instructionPC 3731 = 0x1495 :=
  by rw [scan_instruction_pc 3731 (by decide) (by decide)]; rfl
@[simp] theorem pc2970 : Artifact.submissionArtifact.instructionPC 3732 = 0x1496 :=
  by rw [scan_instruction_pc 3732 (by decide) (by decide)]; rfl
@[simp] theorem pc2971 : Artifact.submissionArtifact.instructionPC 3733 = 0x1497 :=
  by rw [scan_instruction_pc 3733 (by decide) (by decide)]; rfl
@[simp] theorem pc2972 : Artifact.submissionArtifact.instructionPC 3734 = 0x1498 :=
  by rw [scan_instruction_pc 3734 (by decide) (by decide)]; rfl
@[simp] theorem pc2973 : Artifact.submissionArtifact.instructionPC 3735 = 0x1499 :=
  by rw [scan_instruction_pc 3735 (by decide) (by decide)]; rfl
@[simp] theorem pc2974 : Artifact.submissionArtifact.instructionPC 3736 = 0x149a :=
  by rw [scan_instruction_pc 3736 (by decide) (by decide)]; rfl
@[simp] theorem pc2975 : Artifact.submissionArtifact.instructionPC 3737 = 0x149b :=
  by rw [scan_instruction_pc 3737 (by decide) (by decide)]; rfl
@[simp] theorem pc2976 : Artifact.submissionArtifact.instructionPC 3738 = 0x149c :=
  by rw [scan_instruction_pc 3738 (by decide) (by decide)]; rfl
@[simp] theorem pc2977 : Artifact.submissionArtifact.instructionPC 3739 = 0x149d :=
  by rw [scan_instruction_pc 3739 (by decide) (by decide)]; rfl
@[simp] theorem pc2978 : Artifact.submissionArtifact.instructionPC 3740 = 0x149e :=
  by rw [scan_instruction_pc 3740 (by decide) (by decide)]; rfl
@[simp] theorem pc2979 : Artifact.submissionArtifact.instructionPC 3741 = 0x149f :=
  by rw [scan_instruction_pc 3741 (by decide) (by decide)]; rfl
@[simp] theorem pc2980 : Artifact.submissionArtifact.instructionPC 3742 = 0x14a0 :=
  by rw [scan_instruction_pc 3742 (by decide) (by decide)]; rfl
@[simp] theorem pc2981 : Artifact.submissionArtifact.instructionPC 3743 = 0x14a1 :=
  by rw [scan_instruction_pc 3743 (by decide) (by decide)]; rfl
@[simp] theorem pc2982 : Artifact.submissionArtifact.instructionPC 3744 = 0x14a4 :=
  by rw [scan_instruction_pc 3744 (by decide) (by decide)]; rfl
@[simp] theorem pc2983 : Artifact.submissionArtifact.instructionPC 3745 = 0x14a5 :=
  by rw [scan_instruction_pc 3745 (by decide) (by decide)]; rfl
@[simp] theorem pc2984 : Artifact.submissionArtifact.instructionPC 3746 = 0x14ba :=
  by rw [scan_instruction_pc 3746 (by decide) (by decide)]; rfl
@[simp] theorem pc2985 : Artifact.submissionArtifact.instructionPC 3747 = 0x14bb :=
  by rw [scan_instruction_pc 3747 (by decide) (by decide)]; rfl
@[simp] theorem pc2986 : Artifact.submissionArtifact.instructionPC 3748 = 0x14bc :=
  by rw [scan_instruction_pc 3748 (by decide) (by decide)]; rfl
@[simp] theorem pc2987 : Artifact.submissionArtifact.instructionPC 3749 = 0x14be :=
  by rw [scan_instruction_pc 3749 (by decide) (by decide)]; rfl
@[simp] theorem pc2988 : Artifact.submissionArtifact.instructionPC 3750 = 0x14bf :=
  by rw [scan_instruction_pc 3750 (by decide) (by decide)]; rfl
@[simp] theorem pc2989 : Artifact.submissionArtifact.instructionPC 3751 = 0x14c0 :=
  by rw [scan_instruction_pc 3751 (by decide) (by decide)]; rfl
@[simp] theorem pc2990 : Artifact.submissionArtifact.instructionPC 3752 = 0x14c1 :=
  by rw [scan_instruction_pc 3752 (by decide) (by decide)]; rfl
@[simp] theorem pc2991 : Artifact.submissionArtifact.instructionPC 3753 = 0x14c2 :=
  by rw [scan_instruction_pc 3753 (by decide) (by decide)]; rfl
@[simp] theorem pc2992 : Artifact.submissionArtifact.instructionPC 3754 = 0x14c3 :=
  by rw [scan_instruction_pc 3754 (by decide) (by decide)]; rfl
@[simp] theorem pc2993 : Artifact.submissionArtifact.instructionPC 3755 = 0x14c5 :=
  by rw [scan_instruction_pc 3755 (by decide) (by decide)]; rfl
@[simp] theorem pc2994 : Artifact.submissionArtifact.instructionPC 3756 = 0x14c6 :=
  by rw [scan_instruction_pc 3756 (by decide) (by decide)]; rfl
@[simp] theorem pc2995 : Artifact.submissionArtifact.instructionPC 3757 = 0x14c8 :=
  by rw [scan_instruction_pc 3757 (by decide) (by decide)]; rfl
@[simp] theorem pc2996 : Artifact.submissionArtifact.instructionPC 3758 = 0x14c9 :=
  by rw [scan_instruction_pc 3758 (by decide) (by decide)]; rfl
@[simp] theorem pc2997 : Artifact.submissionArtifact.instructionPC 3759 = 0x14cb :=
  by rw [scan_instruction_pc 3759 (by decide) (by decide)]; rfl
@[simp] theorem pc2998 : Artifact.submissionArtifact.instructionPC 3760 = 0x14cc :=
  by rw [scan_instruction_pc 3760 (by decide) (by decide)]; rfl
@[simp] theorem pc2999 : Artifact.submissionArtifact.instructionPC 3761 = 0x14ce :=
  by rw [scan_instruction_pc 3761 (by decide) (by decide)]; rfl
@[simp] theorem pc3000 : Artifact.submissionArtifact.instructionPC 3762 = 0x14cf :=
  by rw [scan_instruction_pc 3762 (by decide) (by decide)]; rfl
@[simp] theorem pc3001 : Artifact.submissionArtifact.instructionPC 3763 = 0x14d0 :=
  by rw [scan_instruction_pc 3763 (by decide) (by decide)]; rfl
@[simp] theorem pc3002 : Artifact.submissionArtifact.instructionPC 3764 = 0x14d2 :=
  by rw [scan_instruction_pc 3764 (by decide) (by decide)]; rfl
@[simp] theorem pc3003 : Artifact.submissionArtifact.instructionPC 3765 = 0x14d3 :=
  by rw [scan_instruction_pc 3765 (by decide) (by decide)]; rfl
@[simp] theorem pc3004 : Artifact.submissionArtifact.instructionPC 3766 = 0x14d4 :=
  by rw [scan_instruction_pc 3766 (by decide) (by decide)]; rfl
@[simp] theorem pc3005 : Artifact.submissionArtifact.instructionPC 3767 = 0x14d5 :=
  by rw [scan_instruction_pc 3767 (by decide) (by decide)]; rfl
@[simp] theorem pc3006 : Artifact.submissionArtifact.instructionPC 3768 = 0x14d6 :=
  by rw [scan_instruction_pc 3768 (by decide) (by decide)]; rfl
@[simp] theorem pc3007 : Artifact.submissionArtifact.instructionPC 3769 = 0x14d7 :=
  by rw [scan_instruction_pc 3769 (by decide) (by decide)]; rfl
@[simp] theorem pc3008 : Artifact.submissionArtifact.instructionPC 3770 = 0x14d8 :=
  by rw [scan_instruction_pc 3770 (by decide) (by decide)]; rfl
@[simp] theorem pc3009 : Artifact.submissionArtifact.instructionPC 3771 = 0x14d9 :=
  by rw [scan_instruction_pc 3771 (by decide) (by decide)]; rfl
@[simp] theorem pc3010 : Artifact.submissionArtifact.instructionPC 3772 = 0x14da :=
  by rw [scan_instruction_pc 3772 (by decide) (by decide)]; rfl
@[simp] theorem pc3011 : Artifact.submissionArtifact.instructionPC 3773 = 0x14db :=
  by rw [scan_instruction_pc 3773 (by decide) (by decide)]; rfl
@[simp] theorem pc3012 : Artifact.submissionArtifact.instructionPC 3774 = 0x14dc :=
  by rw [scan_instruction_pc 3774 (by decide) (by decide)]; rfl
@[simp] theorem pc3013 : Artifact.submissionArtifact.instructionPC 3775 = 0x14dd :=
  by rw [scan_instruction_pc 3775 (by decide) (by decide)]; rfl
@[simp] theorem pc3014 : Artifact.submissionArtifact.instructionPC 3776 = 0x14de :=
  by rw [scan_instruction_pc 3776 (by decide) (by decide)]; rfl
@[simp] theorem pc3015 : Artifact.submissionArtifact.instructionPC 3777 = 0x14df :=
  by rw [scan_instruction_pc 3777 (by decide) (by decide)]; rfl
@[simp] theorem pc3016 : Artifact.submissionArtifact.instructionPC 3778 = 0x14e0 :=
  by rw [scan_instruction_pc 3778 (by decide) (by decide)]; rfl
@[simp] theorem pc3017 : Artifact.submissionArtifact.instructionPC 3779 = 0x14e2 :=
  by rw [scan_instruction_pc 3779 (by decide) (by decide)]; rfl
@[simp] theorem pc3018 : Artifact.submissionArtifact.instructionPC 3780 = 0x14e3 :=
  by rw [scan_instruction_pc 3780 (by decide) (by decide)]; rfl
@[simp] theorem pc3019 : Artifact.submissionArtifact.instructionPC 3781 = 0x14e4 :=
  by rw [scan_instruction_pc 3781 (by decide) (by decide)]; rfl
@[simp] theorem pc3020 : Artifact.submissionArtifact.instructionPC 3782 = 0x14e5 :=
  by rw [scan_instruction_pc 3782 (by decide) (by decide)]; rfl
@[simp] theorem pc3021 : Artifact.submissionArtifact.instructionPC 3783 = 0x14e8 :=
  by rw [scan_instruction_pc 3783 (by decide) (by decide)]; rfl
#print axioms scan_instruction_at
#print axioms scan_instruction_pc
#print axioms setupPath
#print axioms wordPath
#print axioms comparePath
#print axioms tailPath
#print axioms returnPath
#print axioms straddleCorrPath
#print axioms straddleAddPath
#print axioms straddleBackPath
#print axioms pc2903
#print axioms pc3021

end Challenge.Ripemd160.Submission.Proofs.Bytecode.PatternedScan
