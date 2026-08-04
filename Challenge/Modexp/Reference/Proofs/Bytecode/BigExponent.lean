import Challenge.Modexp.Reference.Proofs.Bytecode.BigBaseLoop
import Challenge.Modexp.Reference.Proofs.Bytecode.BigMulGas
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-! # Certified multi-limb exponentiation path -/

namespace Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open BigBase
open BigBaseLoop

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.referenceInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.referenceInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def startExponentPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 717 .JUMPDEST, pushAt 718 0 0]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 719 .JUMPDEST, opAt 720 (.Dup ⟨4, by decide⟩),
   opAt 721 (.Dup ⟨1, by decide⟩), opAt 722 .LT, opAt 723 .ISZERO,
   pushAt 724 2 1118, opAt 725 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 726 (.Dup ⟨0, by decide⟩), opAt 727 (.Dup ⟨8, by decide⟩),
   opAt 728 .ADD, opAt 729 (.Dup ⟨0, by decide⟩),
   opAt 730 .CALLDATALOAD, pushAt 731 0 0, opAt 732 .BYTE,
   pushAt 733 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 734 .JUMPDEST, pushAt 735 1 8, opAt 736 (.Dup ⟨1, by decide⟩),
   opAt 737 .LT, opAt 738 .ISZERO, pushAt 739 2 1104,
   opAt 740 .JUMPI]

def innerToSquarePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [pushAt 741 1 1, opAt 742 (.Dup ⟨2, by decide⟩),
   opAt 743 (.Dup ⟨2, by decide⟩), pushAt 744 1 7,
   opAt 745 .SUB, opAt 746 .SHR, opAt 747 .AND,
   pushAt 748 2 1000, opAt 749 (.Dup ⟨7, by decide⟩),
   pushAt 750 0 0, pushAt 751 2 3072, pushAt 752 2 2048,
   pushAt 753 2 2048, pushAt 754 2 310, opAt 755 .JUMP]

def squareToCopyPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 756 .JUMPDEST, pushAt 757 2 1015,
   opAt 758 (.Dup ⟨7, by decide⟩), pushAt 759 2 3072,
   pushAt 760 2 2048, pushAt 761 2 58, opAt 762 .JUMP]

def copyToProductPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 763 .JUMPDEST, pushAt 764 2 1034,
   opAt 765 (.Dup ⟨7, by decide⟩), pushAt 766 0 0,
   pushAt 767 2 3072, pushAt 768 2 1024, pushAt 769 2 2048,
   pushAt 770 2 310, opAt 771 .JUMP]

def productToSelectPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [opAt 772 .JUMPDEST, opAt 773 (.Dup ⟨0, by decide⟩),
   pushAt 774 0 0, opAt 775 .SUB, pushAt 776 0 0]

def exponentEntry (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 944
           stack := [accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def outerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 946
           stack := [UInt256.ofNat i, accumulatorWord, UInt256.ofNat count,
             UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
             UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

def outerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulatorWord count b e m baseOff expOff rest i with
      pc := UInt256.ofNat 955 }

def loadedExponentByte (s : State) (expOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (expOff + i))

def innerLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { s with pc := UInt256.ofNat 963
           stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i,
             accumulatorWord, UInt256.ofNat count, UInt256.ofNat b,
             UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff,
             UInt256.ofNat expOff] ++ rest }

def innerBody (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (offset byte : UInt256)
    (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j with
      pc := UInt256.ofNat 973 }

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
    2048 2048 3072 0 count 1000
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
    2048 2048 3072 0 count 1000
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

def copiedSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyReturned
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest)
    2048 3072 count 1015
    (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
      (exponentBit byte j) rest)

@[simp] theorem squareReturned_pc (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) :
    (squareReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest).pc = UInt256.ofNat 1000 := by
  have h1000 : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
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
    2048 1024 3072 0 count 1034
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

def selectLoop (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j k : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  { productReturned s accumulatorWord count b e m baseOff expOff i j
      offset byte rest with
    pc := UInt256.ofNat 1039
    stack := [UInt256.ofNat k, selectMask byte j, exponentBit byte j,
      UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulatorWord,
      UInt256.ofNat count, UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
      UInt256.ofNat baseOff, UInt256.ofNat expOff] ++ rest }

@[simp] private theorem exponentPCs (i : Nat) (hi : 717 ≤ i) (hii : i ≤ 755) :
    Artifact.referenceArtifact.instructionPC i =
      ([944,945,946,947,948,949,950,951,954,955,956,957,958,959,960,961,
        962,963,964,966,967,968,969,972,973,975,976,977,979,980,981,982,
        985,986,987,990,993,996,999])[i - 717]! := by
  interval_cases i <;> decide

private theorem jump310 :
    Decode.isValidJumpDest referenceBytecode 310 = true :=
  Artifact.isValidJumpDest_index 262 (by rfl)

@[simp] private theorem exponentMidPCs (i : Nat) (hi : 756 ≤ i)
    (hii : i ≤ 776) :
    Artifact.referenceArtifact.instructionPC i =
      ([1000,1001,1004,1005,1008,1011,1014,1015,1016,1019,1020,1021,
        1024,1027,1030,1033,1034,1035,1036,1037,1038])[i - 756]! := by
  interval_cases i <;> decide

private theorem jump58 :
    Decode.isValidJumpDest referenceBytecode 58 = true :=
  Artifact.isValidJumpDest_index 43 (by rfl)

set_option linter.unusedSimpArgs false in
theorem run_startExponent (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1017) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startExponentPath
      (exponentEntry s accumulatorWord count b e m baseOff expOff rest) =
      some (outerLoop s accumulatorWord count b e m baseOff expOff rest 0) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp [startExponentPath, opAt, pushAt, wfOp, exponentEntry, outerLoop,
    exponentPCs, hrun, hzero, hc7,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1014) (he : e < 2 ^ 256) (hi : i < e)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulatorWord count b e m baseOff expOff rest i) =
      some (outerBody s accumulatorWord count b e m baseOff expOff rest i) := by
  have hi256 : i < 2 ^ 256 := hi.trans he
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat e) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt he, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    exponentPCs, hrun, hlt, honeNat, hc8, hc9, hc10, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerToInner (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1013) (hoff : expOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerToInnerPath
      (outerBody s accumulatorWord count b e m baseOff expOff rest i) =
      some (innerLoop s accumulatorWord count b e m baseOff expOff i
        (UInt256.ofNat (expOff + i)) (loadedExponentByte s expOff i) rest 0) := by
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := expOff) (by omega)
  have hoffNat : (UInt256.ofNat (expOff + i)).toNat = expOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hoff]
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [outerToInnerPath, opAt, pushAt, wfOp, outerBody, outerLoop,
    innerLoop, loadedExponentByte, exponentPCs, hrun, hadd, hoffNat,
    hzero, h0Word, hc8, hc9, hc10, hc11,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

set_option linter.unusedSimpArgs false in
theorem run_innerGuard (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1011) (hj : j < 8)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulatorWord count b e m baseOff expOff i offset byte rest j) =
      some (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j) := by
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat j) 8 = 1 := by
    have hj256 : j < 2 ^ 256 := by omega
    have h8 : (8 : UInt256).toNat = 8 := by decide
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, h8, if_pos hj]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    exponentPCs, hrun, hlt, honeNat, hc11, hc12, hc13, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToSquare (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005) (hj : j < 8)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToSquarePath
      (innerBody s accumulatorWord count b e m baseOff expOff i offset byte rest j) =
      some (squareEntry s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) := by
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7
    (by norm_num : 7 < 2 ^ 256)
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have h310 : (310 : UInt256).toNat = 310 := by decide
  have h310Word : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  simp [innerToSquarePath, opAt, pushAt, wfOp, innerBody, innerLoop,
    squareEntry, BigMul.mulEntry, bitFrame, exponentBit, exponentPCs,
    hcode, hrun, jump310, hsub, h310, h310Word, hzero, hone, hseven,
    hc11, hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_squareToCopy (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock squareToCopyPath
      (squareReturned s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (BigHelpers.copyEntry
        (squareReturned s accumulatorWord count b e m baseOff expOff i j
          offset byte rest)
        2048 3072 count 1015
        (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h58 : (58 : UInt256).toNat = 58 := by decide
  have h58Word : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1000 : (1000 : UInt256).toNat = 1000 := by decide
  have h1000Word : (1000 : UInt256) = UInt256.ofNat 1000 := by decide
  simp [squareToCopyPath, opAt, pushAt, wfOp,
    BigHelpers.copyEntry, bitFrame, exponentMidPCs, hcode, hrun,
    jump58, h58, h58Word, h1000, h1000Word,
    hc12, hc13, hc14, hc15, hc16, hc17, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_copyToProduct (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1005)
    (hcode : s.executionEnv.code = referenceBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock copyToProductPath
      (copiedSquare s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (BigMul.mulEntry
        (copiedSquare s accumulatorWord count b e m baseOff expOff i j
          offset byte rest)
        2048 1024 3072 0 count 1034
        (bitFrame accumulatorWord count b e m baseOff expOff i j offset byte
          (exponentBit byte j) rest)) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hc15 : rest.length + 15 < 1024 := by omega
  have hc16 : rest.length + 16 < 1024 := by omega
  have hc17 : rest.length + 17 < 1024 := by omega
  have hc18 : rest.length + 18 < 1024 := by omega
  have hc19 : rest.length + 19 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h310 : (310 : UInt256).toNat = 310 := by decide
  have h310Word : (310 : UInt256) = UInt256.ofNat 310 := by decide
  have h1015 : (1015 : UInt256).toNat = 1015 := by decide
  have h1015Word : (1015 : UInt256) = UInt256.ofNat 1015 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp [copyToProductPath, opAt, pushAt, wfOp, copiedSquare,
    BigHelpers.copyReturned, BigMul.mulEntry, bitFrame, exponentMidPCs,
    hcode, hrun,
    jump310, h310, h310Word, h1015, h1015Word, hzero,
    hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_productToSelect (s : State) (accumulatorWord : UInt256)
    (count b e m baseOff expOff i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1010)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock productToSelectPath
      (productReturned s accumulatorWord count b e m baseOff expOff i j
        offset byte rest) =
      some (selectLoop s accumulatorWord count b e m baseOff expOff i j 0
        offset byte rest) := by
  have hc12 : rest.length + 12 < 1024 := by omega
  have hc13 : rest.length + 13 < 1024 := by omega
  have hc14 : rest.length + 14 < 1024 := by omega
  have hframe : (bitFrame accumulatorWord count b e m baseOff expOff i j
      offset byte (exponentBit byte j) rest).length < 1024 := by
    simp [bitFrame]
    omega
  have h1034 : (1034 : UInt256).toNat = 1034 := by decide
  have h1034Word : (1034 : UInt256) = UInt256.ofNat 1034 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [productToSelectPath, opAt, pushAt, wfOp, productReturned,
    selectLoop, selectMask, bitFrame, exponentMidPCs,
    hrun, h1034, h1034Word, hzero, h0Word, hc12, hc13, hc14, hframe,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

end Challenge.Modexp.Reference.Proofs.Bytecode.BigExponent
