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
  [opAt 673 .JUMPDEST, pushAt 674 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 675 .JUMPDEST, opAt 676 (.Dup ⟨4, by decide⟩),
   opAt 677 (.Dup ⟨1, by decide⟩), opAt 678 .LT, opAt 679 .ISZERO,
   pushAt 680 2 1031, opAt 681 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 682 (.Dup ⟨0, by decide⟩), opAt 683 (.Dup ⟨8, by decide⟩),
   opAt 684 .ADD, opAt 685 (.Dup ⟨0, by decide⟩),
   opAt 686 .CALLDATALOAD, pushAt 687 0 0, opAt 688 .BYTE,
   pushAt 689 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 690 .JUMPDEST, pushAt 691 1 8, opAt 692 (.Dup ⟨1, by decide⟩),
   opAt 693 .LT, opAt 694 .ISZERO, pushAt 695 2 1017,
   opAt 696 .JUMPI]

def innerToSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 697 1 1, opAt 698 (.Dup ⟨2, by decide⟩),
   opAt 699 (.Dup ⟨2, by decide⟩), pushAt 700 1 7,
   opAt 701 .SUB, opAt 702 .SHR, opAt 703 .AND,
   pushAt 704 2 914, opAt 705 (.Dup ⟨7, by decide⟩),
   pushAt 706 0 0, pushAt 707 2 3072, pushAt 708 2 2048,
   opAt 709 (.Dup ⟨0, by decide⟩), pushAt 710 2 327, opAt 711 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 712 .JUMPDEST, pushAt 713 2 928,
   opAt 714 (.Dup ⟨7, by decide⟩), pushAt 715 2 3072,
   pushAt 716 2 2048, pushAt 717 1 90, opAt 718 .JUMP]

def copyToProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 719 .JUMPDEST, pushAt 720 2 947,
   opAt 721 (.Dup ⟨7, by decide⟩), pushAt 722 0 0,
   pushAt 723 2 3072, pushAt 724 2 1024, pushAt 725 2 2048,
   pushAt 726 2 327, opAt 727 .JUMP]

def productToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 728 .JUMPDEST, opAt 729 (.Dup ⟨0, by decide⟩),
   pushAt 730 0 0, opAt 731 .SUB, pushAt 732 0 0]

def selectGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 733 .JUMPDEST, opAt 734 (.Dup ⟨8, by decide⟩),
   opAt 735 (.Dup ⟨1, by decide⟩), opAt 736 .LT, opAt 737 .ISZERO,
   pushAt 738 2 1003, opAt 739 .JUMPI]

def selectBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 740 (.Dup ⟨0, by decide⟩), pushAt 741 1 5, opAt 742 .SHL,
   opAt 743 (.Dup ⟨0, by decide⟩), pushAt 744 2 2048, opAt 745 .ADD,
   opAt 746 .MLOAD, opAt 747 (.Dup ⟨1, by decide⟩),
   pushAt 748 2 3072, opAt 749 .ADD, opAt 750 .MLOAD,
   opAt 751 (.Dup ⟨4, by decide⟩), opAt 752 (.Dup ⟨1, by decide⟩),
   opAt 753 (.Dup ⟨3, by decide⟩), opAt 754 .XOR, opAt 755 .AND,
   opAt 756 (.Dup ⟨2, by decide⟩), opAt 757 .XOR,
   opAt 758 (.Dup ⟨3, by decide⟩), pushAt 759 2 2048,
   opAt 760 .ADD, opAt 761 .MSTORE, opAt 762 .POP, opAt 763 .POP,
   opAt 764 .POP, pushAt 765 1 1, opAt 766 (.Dup ⟨1, by decide⟩),
   opAt 767 .ADD, opAt 768 (.Swap ⟨0, by decide⟩), opAt 769 .POP,
   pushAt 770 2 952, opAt 771 .JUMP]

def selectFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 772 .JUMPDEST, opAt 773 .POP, opAt 774 .POP, opAt 775 .POP,
   pushAt 776 1 1, opAt 777 (.Dup ⟨1, by decide⟩), opAt 778 .ADD,
   opAt 779 (.Swap ⟨0, by decide⟩), opAt 780 .POP,
   pushAt 781 2 879, opAt 782 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 783 .JUMPDEST, opAt 784 .POP, opAt 785 .POP, opAt 786 .POP,
   pushAt 787 1 1, opAt 788 (.Dup ⟨1, by decide⟩), opAt 789 .ADD,
   opAt 790 (.Swap ⟨0, by decide⟩), opAt 791 .POP,
   pushAt 792 2 862, opAt 793 .JUMP]

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 860
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 862
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 871 }

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 879
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j with
      pc := UInt256.ofNat 889 }

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
    2048 2048 3072 0 count 868
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
    2048 2048 3072 0 count 868
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def copiedSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyReturned
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 3072 count 882
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_pc (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).pc = UInt256.ofNat 914 := by
  have h1000 : (914 : UInt256) = UInt256.ofNat 914 := by decide
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
    2048 1024 3072 0 count 901
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
    pc := UInt256.ofNat 952
    stack := [UInt256.ofNat k, selectMask byte j, exponentBit byte j,
      UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
      UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def selectBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j k offset byte
      rest with pc := UInt256.ofNat 961 }

def selectExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
      byte rest with pc := UInt256.ofNat 1003 }

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
      with pc := UInt256.ofNat 1017 }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
