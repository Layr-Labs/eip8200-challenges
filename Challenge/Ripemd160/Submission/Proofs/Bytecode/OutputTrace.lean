import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.EvmProof.Memory
import Challenge.EvmProof.Word
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

/-!
# Certified instruction traces for RIPEMD-160 output

The output tail zeroes the first word, loops over the five chaining words,
loads each `H[i]`, writes its four bytes in little-endian order, and returns
memory `[0, 32)`. These paths mention only instruction positions in the frozen
artifact and can therefore be composed by both the functional and gas proofs.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputTrace

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def preludePath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨747, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨748, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨749, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨750, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨751, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨752, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩]

def outerTestPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨753, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨754, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨755, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨756, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨757, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨758, .push ⟨2, by decide⟩ (UInt256.ofNat 0x474), by rfl, by decide⟩,
   ⟨759, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def hAtCallPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨760, .push ⟨2, by decide⟩ (UInt256.ofNat 0x469), by rfl, by decide⟩,
   ⟨761, .push ⟨2, by decide⟩ (UInt256.ofNat 0x45d), by rfl, by decide⟩,
   ⟨762, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨763, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨764, .push ⟨2, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨765, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def hAtPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨23, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨24, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨25, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨26, .push ⟨1, by decide⟩ (UInt256.ofNat 0x20), by rfl, by decide⟩,
   ⟨27, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨28, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨29, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨30, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨31, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def writeCallPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨766, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨767, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨768, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨769, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨770, .push ⟨1, by decide⟩ (UInt256.ofNat 12), by rfl, by decide⟩,
   ⟨771, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨772, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c6), by rfl, by decide⟩,
   ⟨773, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def writeInitPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨672, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨673, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩]

def writeTestPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨674, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨675, .push ⟨1, by decide⟩ (UInt256.ofNat 4), by rfl, by decide⟩,
   ⟨676, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨677, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨678, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨679, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3e9), by rfl, by decide⟩,
   ⟨680, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def writeBodyPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨681, .push ⟨1, by decide⟩ (UInt256.ofNat 0xff), by rfl, by decide⟩,
   ⟨682, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨683, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨684, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨685, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨686, .op .SHR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨687, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨688, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨689, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨690, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨691, .op .MSTORE8, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨692, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨693, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨694, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨695, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨696, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨697, .push ⟨2, by decide⟩ (UInt256.ofNat 0x3c8), by rfl, by decide⟩,
   ⟨698, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def writeExitPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨699, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨700, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨701, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨702, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨703, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def outerNextPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨774, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨775, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨776, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨777, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨778, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨779, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨780, .push ⟨2, by decide⟩ (UInt256.ofNat 0x447), by rfl, by decide⟩,
   ⟨781, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def finishPath : List
    (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [⟨782, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨783, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨784, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨785, .push ⟨0, by decide⟩ ⟨0⟩, by rfl, by decide⟩,
   ⟨786, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem pc23 : Artifact.submissionArtifact.instructionPC 23 = 0x30 := by rfl
@[simp] private theorem pc24 : Artifact.submissionArtifact.instructionPC 24 = 0x31 := by rfl
@[simp] private theorem pc25 : Artifact.submissionArtifact.instructionPC 25 = 0x32 := by rfl
@[simp] private theorem pc26 : Artifact.submissionArtifact.instructionPC 26 = 0x33 := by rfl
@[simp] private theorem pc27 : Artifact.submissionArtifact.instructionPC 27 = 0x34 := by rfl
@[simp] private theorem pc28 : Artifact.submissionArtifact.instructionPC 28 = 0x35 := by rfl
@[simp] private theorem pc29 : Artifact.submissionArtifact.instructionPC 29 = 0x38 := by rfl
@[simp] private theorem pc30 : Artifact.submissionArtifact.instructionPC 30 = 0x39 := by rfl
@[simp] private theorem pc31 : Artifact.submissionArtifact.instructionPC 31 = 0x3b := by rfl
@[simp] private theorem pc32 : Artifact.submissionArtifact.instructionPC 32 = 0x3c := by rfl
@[simp] private theorem pc33 : Artifact.submissionArtifact.instructionPC 33 = 0x3f := by rfl
@[simp] private theorem pc34 : Artifact.submissionArtifact.instructionPC 34 = 0x40 := by rfl

@[simp] private theorem pc650 : Artifact.submissionArtifact.instructionPC 672 = 0x3f9 := by rfl
@[simp] private theorem pc651 : Artifact.submissionArtifact.instructionPC 673 = 0x3fa := by rfl
@[simp] private theorem pc652 : Artifact.submissionArtifact.instructionPC 674 = 0x3fb := by rfl
@[simp] private theorem pc653 : Artifact.submissionArtifact.instructionPC 675 = 0x3fc := by rfl
@[simp] private theorem pc654 : Artifact.submissionArtifact.instructionPC 676 = 0x3fd := by rfl
@[simp] private theorem pc655 : Artifact.submissionArtifact.instructionPC 677 = 0x3fe := by rfl
@[simp] private theorem pc656 : Artifact.submissionArtifact.instructionPC 678 = 0x3ff := by rfl
@[simp] private theorem pc657 : Artifact.submissionArtifact.instructionPC 679 = 0x400 := by rfl
@[simp] private theorem pc658 : Artifact.submissionArtifact.instructionPC 680 = 0x401 := by rfl
@[simp] private theorem pc659 : Artifact.submissionArtifact.instructionPC 681 = 0x402 := by rfl
@[simp] private theorem pc660 : Artifact.submissionArtifact.instructionPC 682 = 0x403 := by rfl
@[simp] private theorem pc661 : Artifact.submissionArtifact.instructionPC 683 = 0x404 := by rfl
@[simp] private theorem pc662 : Artifact.submissionArtifact.instructionPC 684 = 0x405 := by rfl
@[simp] private theorem pc663 : Artifact.submissionArtifact.instructionPC 685 = 0x406 := by rfl
@[simp] private theorem pc664 : Artifact.submissionArtifact.instructionPC 686 = 0x407 := by rfl
@[simp] private theorem pc665 : Artifact.submissionArtifact.instructionPC 687 = 0x40a := by rfl
@[simp] private theorem pc666 : Artifact.submissionArtifact.instructionPC 688 = 0x40b := by rfl
@[simp] private theorem pc667 : Artifact.submissionArtifact.instructionPC 689 = 0x40e := by rfl
@[simp] private theorem pc668 : Artifact.submissionArtifact.instructionPC 690 = 0x40f := by rfl
@[simp] private theorem pc669 : Artifact.submissionArtifact.instructionPC 691 = 0x410 := by rfl
@[simp] private theorem pc670 : Artifact.submissionArtifact.instructionPC 692 = 0x411 := by rfl
@[simp] private theorem pc671 : Artifact.submissionArtifact.instructionPC 693 = 0x412 := by rfl
@[simp] private theorem pc672 : Artifact.submissionArtifact.instructionPC 694 = 0x413 := by rfl
@[simp] private theorem pc673 : Artifact.submissionArtifact.instructionPC 695 = 0x414 := by rfl
@[simp] private theorem pc674 : Artifact.submissionArtifact.instructionPC 696 = 0x415 := by rfl
@[simp] private theorem pc675 : Artifact.submissionArtifact.instructionPC 697 = 0x416 := by rfl
@[simp] private theorem pc676 : Artifact.submissionArtifact.instructionPC 698 = 0x417 := by rfl
@[simp] private theorem pc677 : Artifact.submissionArtifact.instructionPC 699 = 0x418 := by rfl
@[simp] private theorem pc678 : Artifact.submissionArtifact.instructionPC 700 = 0x41a := by rfl
@[simp] private theorem pc679 : Artifact.submissionArtifact.instructionPC 701 = 0x41b := by rfl
@[simp] private theorem pc680 : Artifact.submissionArtifact.instructionPC 702 = 0x41c := by rfl
@[simp] private theorem pc681 : Artifact.submissionArtifact.instructionPC 703 = 0x41d := by rfl

@[simp] private theorem pc791 : Artifact.submissionArtifact.instructionPC 747 = 0x450 := by rfl
@[simp] private theorem pc792 : Artifact.submissionArtifact.instructionPC 748 = 0x451 := by rfl
@[simp] private theorem pc793 : Artifact.submissionArtifact.instructionPC 749 = 0x453 := by rfl
@[simp] private theorem pc794 : Artifact.submissionArtifact.instructionPC 750 = 0x454 := by rfl
@[simp] private theorem pc795 : Artifact.submissionArtifact.instructionPC 751 = 0x455 := by rfl
@[simp] private theorem pc796 : Artifact.submissionArtifact.instructionPC 752 = 0x456 := by rfl
@[simp] private theorem pc797 : Artifact.submissionArtifact.instructionPC 753 = 0x457 := by rfl
@[simp] private theorem pc798 : Artifact.submissionArtifact.instructionPC 754 = 0x458 := by rfl
@[simp] private theorem pc799 : Artifact.submissionArtifact.instructionPC 755 = 0x459 := by rfl
@[simp] private theorem pc800 : Artifact.submissionArtifact.instructionPC 756 = 0x45a := by rfl
@[simp] private theorem pc801 : Artifact.submissionArtifact.instructionPC 757 = 0x45b := by rfl
@[simp] private theorem pc802 : Artifact.submissionArtifact.instructionPC 758 = 0x45d := by rfl
@[simp] private theorem pc803 : Artifact.submissionArtifact.instructionPC 759 = 0x45e := by rfl
@[simp] private theorem pc804 : Artifact.submissionArtifact.instructionPC 760 = 0x45f := by rfl
@[simp] private theorem pc805 : Artifact.submissionArtifact.instructionPC 761 = 0x460 := by rfl
@[simp] private theorem pc806 : Artifact.submissionArtifact.instructionPC 762 = 0x461 := by rfl
@[simp] private theorem pc807 : Artifact.submissionArtifact.instructionPC 763 = 0x462 := by rfl
@[simp] private theorem pc808 : Artifact.submissionArtifact.instructionPC 764 = 0x463 := by rfl
@[simp] private theorem pc809 : Artifact.submissionArtifact.instructionPC 765 = 0x464 := by rfl
@[simp] private theorem pc810 : Artifact.submissionArtifact.instructionPC 766 = 0x465 := by rfl
@[simp] private theorem pc811 : Artifact.submissionArtifact.instructionPC 767 = 0x466 := by rfl
@[simp] private theorem pc812 : Artifact.submissionArtifact.instructionPC 768 = 0x467 := by rfl
@[simp] private theorem pc813 : Artifact.submissionArtifact.instructionPC 769 = 0x468 := by rfl
@[simp] private theorem pc814 : Artifact.submissionArtifact.instructionPC 770 = 0x469 := by rfl
@[simp] private theorem pc815 : Artifact.submissionArtifact.instructionPC 771 = 0x46a := by rfl
@[simp] private theorem pc816 : Artifact.submissionArtifact.instructionPC 772 = 0x46b := by rfl
@[simp] private theorem pc817 : Artifact.submissionArtifact.instructionPC 773 = 0x46c := by rfl
@[simp] private theorem pc818 : Artifact.submissionArtifact.instructionPC 774 = 0x46d := by rfl
@[simp] private theorem pc819 : Artifact.submissionArtifact.instructionPC 775 = 0x470 := by rfl
@[simp] private theorem pc820 : Artifact.submissionArtifact.instructionPC 776 = 0x471 := by rfl
@[simp] private theorem pc821 : Artifact.submissionArtifact.instructionPC 777 = 0x474 := by rfl
@[simp] private theorem pc822 : Artifact.submissionArtifact.instructionPC 778 = 0x475 := by rfl
@[simp] private theorem pc823 : Artifact.submissionArtifact.instructionPC 779 = 0x476 := by rfl
@[simp] private theorem pc824 : Artifact.submissionArtifact.instructionPC 780 = 0x477 := by rfl
@[simp] private theorem pc825 : Artifact.submissionArtifact.instructionPC 781 = 0x478 := by rfl
@[simp] private theorem pc826 : Artifact.submissionArtifact.instructionPC 782 = 0x479 := by rfl
@[simp] private theorem pc827 : Artifact.submissionArtifact.instructionPC 783 = 0x47a := by rfl
@[simp] private theorem pc828 : Artifact.submissionArtifact.instructionPC 784 = 0x47b := by rfl
@[simp] private theorem pc829 : Artifact.submissionArtifact.instructionPC 785 = 0x47c := by rfl
@[simp] private theorem pc830 : Artifact.submissionArtifact.instructionPC 786 = 0x47d := by rfl

def hOffset (i : Nat) : Nat := 0x20 + 32 * i

def hWord (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory (hOffset i)

def wordByte (word : UInt256) (j : Nat) : UInt8 :=
  UInt8.ofNat
    ((UInt256.land (UInt256.shiftRight word (UInt256.ofNat (8 * j)))
      (UInt256.ofNat 0xff)).toNat % 256)

def writeByte (s : State) (offset : Nat) (word : UInt256) (j : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory (ByteArray.mk #[wordByte word j]) (offset + j)
    activeWords := s.activeWordsAfterUInt256 (offset + j) 1 }

def zeroOutput (s : State) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) 0
    activeWords := s.activeWordsAfterUInt256 0 32 }

private theorem valid20 : Decode.isValidJumpDest submissionBytecode 0x20 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 23 (by rfl)
private theorem valid3c6 : Decode.isValidJumpDest submissionBytecode 0x3c6 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 672 (by rfl)
private theorem valid3c8 : Decode.isValidJumpDest submissionBytecode 0x3c8 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 674 (by rfl)
private theorem valid3e9 : Decode.isValidJumpDest submissionBytecode 0x3e9 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 699 (by rfl)
private theorem valid654 : Decode.isValidJumpDest submissionBytecode 0x447 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 753 (by rfl)
private theorem valid66a : Decode.isValidJumpDest submissionBytecode 0x45d = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 766 (by rfl)
private theorem valid676 : Decode.isValidJumpDest submissionBytecode 0x469 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 774 (by rfl)
private theorem valid681 : Decode.isValidJumpDest submissionBytecode 0x474 = true :=
  Artifact.submissionArtifact.isValidJumpDest_index 782 (by rfl)

theorem run_prelude (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1022) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock preludePath
      { s with pc := UInt256.ofNat 0x441, stack := offset :: rest } =
    some { zeroOutput s with pc := UInt256.ofNat 0x447, stack := ⟨0⟩ :: rest } := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc0 : rest.length < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [preludePath, zeroOutput, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc0, hc1, hc2, hrun, hzeroNat, State.activeWordsAfterUInt256]

theorem run_outerTest_continue (s : State) (i : Nat) (rest : List UInt256)
    (hi : i < 5) (hcap : rest.length < 1021) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerTestPath
      { s with pc := UInt256.ofNat 0x447, stack := UInt256.ofNat i :: rest } =
    some { s with pc := UInt256.ofNat 0x451, stack := UInt256.ofNat i :: rest } := by
  have hi256 : i < 2 ^ 256 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [outerTestPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hrun, hi, hi256,
    Challenge.EvmProof.Word.word_toNat_ofNat, hlt, hzero, hfalse]

theorem run_outerTest_exit (s : State) (rest : List UInt256)
    (hcap : rest.length < 1021) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerTestPath
      { s with pc := UInt256.ofNat 0x447, stack := UInt256.ofNat 5 :: rest } =
    some { s with pc := UInt256.ofNat 0x474, stack := UInt256.ofNat 5 :: rest } := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 5) (UInt256.ofNat 5) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (1 : UInt256) = 1 := by decide
  simp [outerTestPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hrun, hcode, valid681, hlt, hzero, htrue, honeNat,
    UInt256.isTrue]

theorem run_hAtCall (s : State) (i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1018) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock hAtCallPath
      { s with pc := UInt256.ofNat 0x451, stack := UInt256.ofNat i :: rest } =
    some { s with
      pc := UInt256.ofNat 0x20
      stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x45d,
        UInt256.ofNat 0x469, UInt256.ofNat i] ++ rest } := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  simp [hAtCallPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hc4, hc5, hc6, hrun, hcode, valid20]

theorem run_hAt (s : State) (i : Nat) (rest : List UInt256)
    (hi : i < 5) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock hAtPath
      { s with
        pc := UInt256.ofNat 0x20
        stack := [UInt256.ofNat i, ⟨0⟩, UInt256.ofNat 0x45d] ++ rest } =
    some { s with
      pc := UInt256.ofNat 0x45d
      stack := hWord s i :: rest
      activeWords := s.activeWordsAfterUInt256 (hOffset i) 32 } := by
  have hi256 : i < 2 ^ 256 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hoff : (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
      UInt256.ofNat 0x20).toNat = hOffset i := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat hi256 (by omega) (by omega),
      Challenge.EvmProof.Word.ofNat_add_ofNat (by omega),
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp [hOffset]
    omega
  have hoff' : (UInt256.ofNat 0x20 +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat = hOffset i := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hoff
  simp [hAtPath, Challenge.EvmProof.Word.ofNat_add_mod, hWord, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc2, hc3, hc4, hc5, hrun, hcode, valid66a, hoff, hoff', List.exchange,
    State.activeWordsAfterUInt256]
  exact Word.add_zero _

theorem run_writeCall (s : State) (i : Nat) (word : UInt256)
    (rest : List UInt256) (hi : i < 5) (hcap : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeCallPath
      { s with
        pc := UInt256.ofNat 0x45d
        stack := word :: UInt256.ofNat 0x469 :: UInt256.ofNat i :: rest } =
    some { s with
      pc := UInt256.ofNat 0x3c6
      stack := UInt256.ofNat (12 + 4 * i) :: word :: UInt256.ofNat 0x469 ::
        UInt256.ofNat i :: rest } := by
  have hi256 : i < 2 ^ 256 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) =
      UInt256.ofNat (4 * i) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat hi256 (by omega) (by omega)]
    congr 1
    omega
  have hoff : UInt256.ofNat 12 + UInt256.ofNat (4 * i) =
      UInt256.ofNat (12 + 4 * i) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  simp [writeCallPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc3, hc4, hc5, hrun, hcode, valid3c6, hi, hi256, hshift, hoff,
    Challenge.EvmProof.Word.word_toNat_ofNat]

theorem run_writeInit (s : State) (offset word ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1020) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeInitPath
      { s with pc := UInt256.ofNat 0x3c6, stack := offset :: word :: ret :: rest } =
    some { s with
      pc := UInt256.ofNat 0x3c8
      stack := ⟨0⟩ :: offset :: word :: ret :: rest } := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [writeInitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc3, hc4, hrun]

theorem run_writeTest_continue (s : State) (j : Nat) (tail : List UInt256)
    (hj : j < 4) (hcap : tail.length < 1021) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeTestPath
      { s with pc := UInt256.ofNat 0x3c8, stack := UInt256.ofNat j :: tail } =
    some { s with pc := UInt256.ofNat 0x3d2, stack := UInt256.ofNat j :: tail } := by
  have hj256 : j < 2 ^ 256 := by omega
  have hc1 : tail.length + 1 < 1024 := by omega
  have hc2 : tail.length + 2 < 1024 := by omega
  have hc3 : tail.length + 3 < 1024 := by omega
  have hjWord : (UInt256.ofNat j).toNat = j := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hj256]
  have hlt : UInt256.lt (UInt256.ofNat j) (UInt256.ofNat 4) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hjWord, Challenge.EvmProof.Word.word_toNat_ofNat, hj]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [writeTestPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hrun, hj, hj256,
    Challenge.EvmProof.Word.word_toNat_ofNat, hlt, hzero, hfalse]

theorem run_writeTest_exit (s : State) (tail : List UInt256)
    (hcap : tail.length < 1021) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeTestPath
      { s with pc := UInt256.ofNat 0x3c8, stack := UInt256.ofNat 4 :: tail } =
    some { s with pc := UInt256.ofNat 0x3e9, stack := UInt256.ofNat 4 :: tail } := by
  have hc1 : tail.length + 1 < 1024 := by omega
  have hc2 : tail.length + 2 < 1024 := by omega
  have hc3 : tail.length + 3 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 4) (UInt256.ofNat 4) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) := by decide
  have honeNat : UInt256.toNat (1 : UInt256) = 1 := by decide
  simp [writeTestPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hrun, hcode, valid3e9, hlt, hzero, htrue, honeNat,
    UInt256.isTrue]

theorem run_writeBody (s : State) (offset : Nat) (word : UInt256) (j : Nat)
    (ret : UInt256) (rest : List UInt256) (hj : j < 4)
    (hoff256 : offset + j < 2 ^ 256)
    (hcap : rest.length < 1016) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeBodyPath
      { s with
        pc := UInt256.ofNat 0x3d2
        stack := UInt256.ofNat j :: UInt256.ofNat offset :: word :: ret :: rest } =
    some { writeByte s offset word j with
      pc := UInt256.ofNat 0x3c8
      stack := UInt256.ofNat (j + 1) :: UInt256.ofNat offset :: word :: ret :: rest } := by
  have hj256 : j < 2 ^ 256 := by omega
  have hoffWord : UInt256.ofNat offset + UInt256.ofNat j =
      UInt256.ofNat (offset + j) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hoff256
  have hoffWord' : UInt256.ofNat j + UInt256.ofNat offset =
      UInt256.ofNat (offset + j) := by
    rw [Challenge.EvmProof.Word.word_add_comm]
    exact hoffWord
  have hshift : UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 3) =
      UInt256.ofNat (8 * j) := by
    rw [Challenge.EvmProof.Word.shiftLeft_ofNat hj256 (by omega) (by omega)]
    congr 1
    omega
  have hnext : UInt256.ofNat j + UInt256.ofNat 1 = UInt256.ofNat (j + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hmod : (offset + j) % UInt256.size = offset + j := by
    apply Nat.mod_eq_of_lt
    exact hoff256
  simp only [UInt256.size] at hmod
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  simp [writeBodyPath, writeByte, wordByte,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc4, hc5, hc6, hc7, hc8, hrun, hcode, valid3c8, hj, hj256, hoff256,
    hoffWord, hoffWord', hshift, hnext,
    Challenge.EvmProof.Word.word_toNat_ofNat, hmod,
    List.exchange, State.activeWordsAfterUInt256]

theorem run_writeExit (s : State) (offset word : UInt256) (ret : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1020)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running)
    (hvalid : Decode.isValidJumpDest submissionBytecode ret.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock writeExitPath
      { s with
        pc := UInt256.ofNat 0x3e9
        stack := UInt256.ofNat 4 :: offset :: word :: ret :: rest } =
    some { s with pc := ret, stack := rest } := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [writeExitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hc4, hrun, hcode, hvalid]

theorem run_outerNext (s : State) (i : Nat) (rest : List UInt256)
    (hi : i < 5) (hcap : rest.length < 1021)
    (hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerNextPath
      { s with pc := UInt256.ofNat 0x469, stack := UInt256.ofNat i :: rest } =
    some { s with
      pc := UInt256.ofNat 0x447
      stack := UInt256.ofNat (i + 1) :: rest } := by
  have hi256 : i + 1 < 2 ^ 256 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hnext : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat hi256
  simp [outerNextPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc1, hc2, hc3, hrun, hcode, valid654, hi, hi256,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, hnext]

theorem run_finish (s : State) (rest : List UInt256)
    (hcap : rest.length < 1022) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath
      { s with pc := UInt256.ofNat 0x474, stack := UInt256.ofNat 5 :: rest } =
    some { s with
      pc := UInt256.ofNat 0x479
      stack := rest
      halt := .Returned
      hReturn := MachineState.readPadded s.memory 0 32
      activeWords := s.activeWordsAfterUInt256 0 32 } := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc0 : rest.length < 1024 := by omega
  have hzeroNat : (⟨0⟩ : UInt256).toNat = 0 := rfl
  simp [finishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    hcap, hc0, hc1, hc2, hrun, hzeroNat, State.activeWordsAfterUInt256]

end Challenge.Ripemd160.Submission.Proofs.Bytecode.OutputTrace
