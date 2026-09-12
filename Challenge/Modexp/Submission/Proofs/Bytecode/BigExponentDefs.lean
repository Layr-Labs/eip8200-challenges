import Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseLoop
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentPCa
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentPCb
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentPCc
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentPCd
import Challenge.Modexp.Submission.Proofs.Bytecode.BigExponentJmp
import Challenge.Modexp.Submission.Proofs.Bytecode.BigMulGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified multi-limb exponentiation path -/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open BigBase
open BigBaseLoop

def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startExponentPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 678 .JUMPDEST, pushAt 679 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 680 .JUMPDEST, opAt 681 (.Dup ⟨4, by decide⟩),
   opAt 682 (.Dup ⟨1, by decide⟩), opAt 683 .LT, opAt 684 .ISZERO,
   pushAt 685 2 1038, opAt 686 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 687 (.Dup ⟨0, by decide⟩), opAt 688 (.Dup ⟨8, by decide⟩),
   opAt 689 .ADD, opAt 690 (.Dup ⟨0, by decide⟩),
   opAt 691 .CALLDATALOAD, pushAt 692 0 0, opAt 693 .BYTE,
   pushAt 694 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 695 .JUMPDEST, pushAt 696 1 8, opAt 697 (.Dup ⟨1, by decide⟩),
   opAt 698 .LT, opAt 699 .ISZERO, pushAt 700 2 1024,
   opAt 701 .JUMPI]

def innerToSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 702 1 1, opAt 703 (.Dup ⟨2, by decide⟩),
   opAt 704 (.Dup ⟨2, by decide⟩), pushAt 705 1 7,
   opAt 706 .SUB, opAt 707 .SHR, opAt 708 .AND,
   pushAt 709 2 921, opAt 710 (.Dup ⟨7, by decide⟩),
   pushAt 711 0 0, pushAt 712 2 3072, pushAt 713 2 2048,
   opAt 714 (.Dup ⟨0, by decide⟩), pushAt 715 2 334, opAt 716 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 717 .JUMPDEST, pushAt 718 2 935,
   opAt 719 (.Dup ⟨7, by decide⟩), pushAt 720 2 3072,
   pushAt 721 2 2048, pushAt 722 1 97, opAt 723 .JUMP]

def copyToProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 724 .JUMPDEST, pushAt 725 2 954,
   opAt 726 (.Dup ⟨7, by decide⟩), pushAt 727 0 0,
   pushAt 728 2 3072, pushAt 729 2 1024, pushAt 730 2 2048,
   pushAt 731 2 334, opAt 732 .JUMP]

def productToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 733 .JUMPDEST, opAt 734 (.Dup ⟨0, by decide⟩),
   pushAt 735 0 0, opAt 736 .SUB, pushAt 737 0 0]

def selectGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 738 .JUMPDEST, opAt 739 (.Dup ⟨8, by decide⟩),
   opAt 740 (.Dup ⟨1, by decide⟩), opAt 741 .LT, opAt 742 .ISZERO,
   pushAt 743 2 1010, opAt 744 .JUMPI]

def selectBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 745 (.Dup ⟨0, by decide⟩), pushAt 746 1 5, opAt 747 .SHL,
   opAt 748 (.Dup ⟨0, by decide⟩), pushAt 749 2 2048, opAt 750 .ADD,
   opAt 751 .MLOAD, opAt 752 (.Dup ⟨1, by decide⟩),
   pushAt 753 2 3072, opAt 754 .ADD, opAt 755 .MLOAD,
   opAt 756 (.Dup ⟨4, by decide⟩), opAt 757 (.Dup ⟨1, by decide⟩),
   opAt 758 (.Dup ⟨3, by decide⟩), opAt 759 .XOR, opAt 760 .AND,
   opAt 761 (.Dup ⟨2, by decide⟩), opAt 762 .XOR,
   opAt 763 (.Dup ⟨3, by decide⟩), pushAt 764 2 2048,
   opAt 765 .ADD, opAt 766 .MSTORE, opAt 767 .POP, opAt 768 .POP,
   opAt 769 .POP, pushAt 770 1 1, opAt 771 (.Dup ⟨1, by decide⟩),
   opAt 772 .ADD, opAt 773 (.Swap ⟨0, by decide⟩), opAt 774 .POP,
   pushAt 775 2 959, opAt 776 .JUMP]

def selectFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 777 .JUMPDEST, opAt 778 .POP, opAt 779 .POP, opAt 780 .POP,
   pushAt 781 1 1, opAt 782 (.Dup ⟨1, by decide⟩), opAt 783 .ADD,
   opAt 784 (.Swap ⟨0, by decide⟩), opAt 785 .POP,
   pushAt 786 2 886, opAt 787 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 788 .JUMPDEST, opAt 789 .POP, opAt 790 .POP, opAt 791 .POP,
   pushAt 792 1 1, opAt 793 (.Dup ⟨1, by decide⟩), opAt 794 .ADD,
   opAt 795 (.Swap ⟨0, by decide⟩), opAt 796 .POP,
   pushAt 797 2 869, opAt 798 .JUMP]

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 867
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 869
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 878 }

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 886
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j with
      pc := UInt256.ofNat 896 }

def exponentBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

def bitFrame (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte bit : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [bit, UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
    UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest

def squareEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigMul.mulEntry
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 921
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def mulResult (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let copied := BigMul.mulAfterCopy s a b out modulus count returnDest rest
  let progress := BigMul.mulOuterProgress copied a b out modulus count
    returnDest rest count
  BigMul.mulReturned progress returnDest rest

@[simp] theorem mulResult_pc (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).pc = returnDest := by
  simp [mulResult, BigMul.mulReturned]

@[simp] theorem mulResult_stack (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).stack = rest := by
  simp [mulResult, BigMul.mulReturned]

@[simp] theorem mulResult_halt (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).halt = s.halt := by
  simp [mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

@[simp] theorem mulResult_executionEnv (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulResult s a b out modulus count returnDest rest).executionEnv =
      s.executionEnv := by
  simp [mulResult, BigMul.mulReturned, BigMul.mulAfterCopy,
    BigMul.mulAfterClear]

def squareReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  mulResult
    (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j)
    2048 2048 3072 0 count 921
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def copiedSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyReturned
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 3072 count 935
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_pc (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).pc = UInt256.ofNat 921 := by
  have h1000 : (921 : UInt256) = UInt256.ofNat 921 := by decide
  simpa [squareReturned] using h1000

@[simp] theorem squareReturned_stack (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).stack =
        bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest := by
  simp [squareReturned]

def productReturned (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  mulResult
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 1024 3072 0 count 954
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [squareReturned, innerBody, innerLoop]

@[simp] theorem squareReturned_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [squareReturned, innerBody, innerLoop]

@[simp] theorem copiedSquare_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [copiedSquare, BigHelpers.copyReturned]

@[simp] theorem copiedSquare_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (copiedSquare s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [copiedSquare, BigHelpers.copyReturned]

@[simp] theorem productReturned_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (productReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).halt = s.halt := by
  simp [productReturned]

@[simp] theorem productReturned_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (productReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).executionEnv = s.executionEnv := by
  simp [productReturned]

def selectMask (byte : UInt256) (j : Nat) : UInt256 :=
  0 - exponentBit byte j

def selectOffset (k : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat k) (UInt256.ofNat 5)

def selectedWord (memory : ByteArray) (mask : UInt256) (k : Nat) : UInt256 :=
  let offset := selectOffset k
  let square := MachineState.readWord memory (2048 + offset).toNat
  let product := MachineState.readWord memory (3072 + offset).toNat
  UInt256.xor square (UInt256.land (UInt256.xor square product) mask)

def selectMemory (memory : ByteArray) (mask : UInt256) : Nat → ByteArray
  | 0 => memory
  | k + 1 =>
      let before := selectMemory memory mask k
      MachineState.writeBytes before
        (Data.Bytes.natToBytesPadded (selectedWord before mask k).toNat 32)
        (2048 + selectOffset k).toNat

def selectWords (active : UInt256) : Nat → UInt256
  | 0 => active
  | k + 1 =>
      let before := selectWords active k
      let square := UInt256.ofNat (MachineState.activeWordsAfter before.toNat
        (2048 + selectOffset k).toNat 32)
      let product := UInt256.ofNat (MachineState.activeWordsAfter square.toNat
        (3072 + selectOffset k).toNat 32)
      UInt256.ofNat (MachineState.activeWordsAfter product.toNat
        (2048 + selectOffset k).toNat 32)

def selectProgress (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (k : Nat) : State :=
  let returned := productReturned s accumulatorWord count b e m baseOff expOff
    i j offset byte rest
  { returned with
    memory := selectMemory returned.memory (selectMask byte j) k
    activeWords := selectWords returned.activeWords k }

@[simp] theorem selectProgress_zero (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    selectProgress s accumulatorWord count b e m baseOff expOff i j offset
        byte rest 0 =
      productReturned s accumulatorWord count b e m baseOff expOff i j offset
        byte rest := by
  unfold selectProgress
  generalize productReturned s accumulatorWord count b e m baseOff expOff i j
    offset byte rest = returned
  cases returned
  rfl

@[simp] theorem selectProgress_halt (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest k).halt = s.halt := by
  simp [selectProgress]

@[simp] theorem selectProgress_executionEnv (s : State)
    (accumulatorWord : UInt256) (count b e m baseOff expOff i j k : Nat)
    (offset byte : UInt256) (rest : List UInt256) :
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest k).executionEnv = s.executionEnv := by
  simp [selectProgress]

def selectLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectProgress s accumulatorWord count b e m baseOff expOff i j
      offset byte rest k with
    pc := UInt256.ofNat 959
    stack := [UInt256.ofNat k, selectMask byte j, exponentBit byte j,
      UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
      UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def selectBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j k offset byte
      rest with pc := UInt256.ofNat 968 }

def selectExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
      byte rest with pc := UInt256.ofNat 1010 }

def afterSelectedBit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  innerLoop
    (selectProgress s accumulatorWord count b e m baseOff expOff i j offset
      byte rest count)
    accumulatorWord count b e m baseOff expOff i offset byte rest (j + 1)

def innerExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest 8
      with pc := UInt256.ofNat 1024 }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
