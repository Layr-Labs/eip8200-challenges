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
  [opAt 640 .JUMPDEST, pushAt 641 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 642 .JUMPDEST, opAt 643 (.Dup ⟨4, by decide⟩),
   opAt 644 (.Dup ⟨1, by decide⟩), opAt 645 .LT, opAt 646 .ISZERO,
   pushAt 647 2 985, opAt 648 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 649 (.Dup ⟨0, by decide⟩), opAt 650 (.Dup ⟨8, by decide⟩),
   opAt 651 .ADD, opAt 652 (.Dup ⟨0, by decide⟩),
   opAt 653 .CALLDATALOAD, pushAt 654 0 0, opAt 655 .BYTE,
   pushAt 656 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 657 .JUMPDEST, pushAt 658 1 8, opAt 659 (.Dup ⟨1, by decide⟩),
   opAt 660 .LT, opAt 661 .ISZERO, pushAt 662 2 971,
   opAt 663 .JUMPI]

def innerToSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 664 1 1, opAt 665 (.Dup ⟨2, by decide⟩),
   opAt 666 (.Dup ⟨2, by decide⟩), pushAt 667 1 7,
   opAt 668 .SUB, opAt 669 .SHR, opAt 670 .AND,
   pushAt 671 2 868, opAt 672 (.Dup ⟨7, by decide⟩),
   pushAt 673 0 0, pushAt 674 2 3072, pushAt 675 2 2048,
   opAt 676 (.Dup ⟨0, by decide⟩), pushAt 677 2 281, opAt 678 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 679 .JUMPDEST, pushAt 680 2 882,
   opAt 681 (.Dup ⟨7, by decide⟩), pushAt 682 2 3072,
   pushAt 683 2 2048, pushAt 684 1 46, opAt 685 .JUMP]

def copyToProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 686 .JUMPDEST, pushAt 687 2 901,
   opAt 688 (.Dup ⟨7, by decide⟩), pushAt 689 0 0,
   pushAt 690 2 3072, pushAt 691 2 1024, pushAt 692 2 2048,
   pushAt 693 2 281, opAt 694 .JUMP]

def productToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 695 .JUMPDEST, opAt 696 (.Dup ⟨0, by decide⟩),
   pushAt 697 0 0, opAt 698 .SUB, pushAt 699 0 0]

def selectGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 700 .JUMPDEST, opAt 701 (.Dup ⟨8, by decide⟩),
   opAt 702 (.Dup ⟨1, by decide⟩), opAt 703 .LT, opAt 704 .ISZERO,
   pushAt 705 2 957, opAt 706 .JUMPI]

def selectBodyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 707 (.Dup ⟨0, by decide⟩), pushAt 708 1 5, opAt 709 .SHL,
   opAt 710 (.Dup ⟨0, by decide⟩), pushAt 711 2 2048, opAt 712 .ADD,
   opAt 713 .MLOAD, opAt 714 (.Dup ⟨1, by decide⟩),
   pushAt 715 2 3072, opAt 716 .ADD, opAt 717 .MLOAD,
   opAt 718 (.Dup ⟨4, by decide⟩), opAt 719 (.Dup ⟨1, by decide⟩),
   opAt 720 (.Dup ⟨3, by decide⟩), opAt 721 .XOR, opAt 722 .AND,
   opAt 723 (.Dup ⟨2, by decide⟩), opAt 724 .XOR,
   opAt 725 (.Dup ⟨3, by decide⟩), pushAt 726 2 2048,
   opAt 727 .ADD, opAt 728 .MSTORE, opAt 729 .POP, opAt 730 .POP,
   opAt 731 .POP, pushAt 732 1 1, opAt 733 (.Dup ⟨1, by decide⟩),
   opAt 734 .ADD, opAt 735 (.Swap ⟨0, by decide⟩), opAt 736 .POP,
   pushAt 737 2 906, opAt 738 .JUMP]

def selectFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 739 .JUMPDEST, opAt 740 .POP, opAt 741 .POP, opAt 742 .POP,
   pushAt 743 1 1, opAt 744 (.Dup ⟨1, by decide⟩), opAt 745 .ADD,
   opAt 746 (.Swap ⟨0, by decide⟩), opAt 747 .POP,
   pushAt 748 2 833, opAt 749 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 750 .JUMPDEST, opAt 751 .POP, opAt 752 .POP, opAt 753 .POP,
   pushAt 754 1 1, opAt 755 (.Dup ⟨1, by decide⟩), opAt 756 .ADD,
   opAt 757 (.Swap ⟨0, by decide⟩), opAt 758 .POP,
   pushAt 759 2 816, opAt 760 .JUMP]

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 814
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 816
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 825 }

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 833
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j with
      pc := UInt256.ofNat 843 }

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
      offset byte rest).pc = UInt256.ofNat 868 := by
  have h1000 : (868 : UInt256) = UInt256.ofNat 868 := by decide
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
    pc := UInt256.ofNat 906
    stack := [UInt256.ofNat k, selectMask byte j, exponentBit byte j,
      UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
      UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def selectBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j k offset byte
      rest with pc := UInt256.ofNat 915 }

def selectExit (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { selectLoop s accumulatorWord count b e m baseOff expOff i j count offset
      byte rest with pc := UInt256.ofNat 957 }

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
      with pc := UInt256.ofNat 971 }

end Challenge.Modexp.Submission.Proofs.Bytecode.BigExponent
