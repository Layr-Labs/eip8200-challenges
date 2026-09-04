import Challenge.Modexp.Submission.Proofs.Bytecode.BigBase
import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoadCorrect
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
/-! # Certified direct base-loading path

When the base and modulus have the same byte length and the first 32-byte
base word is smaller than the first modulus word, lexicographic order proves
that the complete base is already reduced.  The appended dispatcher therefore
loads the base directly into the limb buffer instead of running the bitwise
Horner conversion.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseDirect

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? =
      some (.push width value) := by rfl)
    (hwf : Challenge.EvmProof.Stepper.WellFormed .Osaka
      (.push width value) := by decide) :
    Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def initializePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1123 .JUMPDEST, pushAt 1124 1 1, pushAt 1125 2 3072,
   opAt 1126 .MSTORE]

def sizeGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1127 (.Dup ⟨2, by decide⟩), opAt 1128 (.Dup ⟨5, by decide⟩),
   opAt 1129 .XOR, opAt 1130 .JUMPDEST, pushAt 1131 2 1561,
   opAt 1132 .JUMPI]

def headGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1133 (.Dup ⟨7, by decide⟩), opAt 1134 .CALLDATALOAD,
   opAt 1135 (.Dup ⟨6, by decide⟩), opAt 1136 .CALLDATALOAD,
   opAt 1137 .LT, opAt 1138 .ISZERO, pushAt 1139 2 1561,
   opAt 1140 .JUMPI]

def directLoadPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1141 2 1555, pushAt 1142 2 1024,
   opAt 1143 (.Dup ⟨4, by decide⟩), opAt 1144 (.Dup ⟨8, by decide⟩),
   pushAt 1145 2 439, opAt 1146 .JUMP]

def fastReturnPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1147 .JUMPDEST, pushAt 1148 0 0, pushAt 1149 2 925,
   opAt 1150 .JUMP]

def fallbackPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1151 .JUMPDEST, pushAt 1152 0 0, pushAt 1153 2 831,
   opAt 1154 .JUMP]

def outerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 707 .JUMPDEST, opAt 708 .POP, pushAt 709 2 1335,
   opAt 710 (.Dup ⟨2, by decide⟩), pushAt 711 0 0,
   pushAt 712 1 1, pushAt 713 2 3072, pushAt 714 2 2048,
   pushAt 715 2 104, opAt 716 .JUMP]

def fullRest (b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat b, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff, UInt256.ofNat expOff, UInt256.ofNat modOff,
    returnDest] ++ rest

def stack (accumulator : UInt256) (count b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  BigBase.frame accumulator count
    (fullRest b e m baseOff expOff modOff returnDest rest)

def initialized (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  let cleared := BigBase.afterClearDouble s accumulator count
    (fullRest b e m baseOff expOff modOff returnDest rest)
  { cleared with
    pc := UInt256.ofNat 1525
    memory := MachineState.writeBytes cleared.memory
      (Data.Bytes.natToBytesPadded 1 32) 3072
    activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      cleared.activeWords.toNat 3072 32) }

def sizePassed (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { initialized s accumulator count b e m baseOff expOff modOff returnDest rest
      with pc := UInt256.ofNat 1533 }

def fallbackEntry (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { initialized s accumulator count b e m baseOff expOff modOff returnDest rest
      with pc := UInt256.ofNat 1561 }

def headPassed (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { initialized s accumulator count b e m baseOff expOff modOff returnDest rest
      with pc := UInt256.ofNat 1543 }

def loaded (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  BigLoad.loadReturned
    (initialized s accumulator count b e m baseOff expOff modOff returnDest rest)
    (UInt256.ofNat baseOff) (UInt256.ofNat b) 1024 1555
    (stack accumulator count b e m baseOff expOff modOff returnDest rest)

def directOuterExit (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { loaded s accumulator count b e m baseOff expOff modOff returnDest rest with
    pc := UInt256.ofNat 925
    stack := 0 :: stack accumulator count b e m baseOff expOff modOff
      returnDest rest }

def directInitialAccumulator (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (directOuterExit s accumulator count b e m baseOff expOff modOff
      returnDest rest)
    2048 3072 1 0 count 1335
    (stack accumulator count b e m baseOff expOff modOff returnDest rest)

def headBase (s : State) (baseOff : Nat) : Nat :=
  (MachineState.readWord s.executionEnv.calldata baseOff).toNat

def headModulus (s : State) (modOff : Nat) : Nat :=
  (MachineState.readWord s.executionEnv.calldata modOff).toNat

def Eligible (s : State) (b m baseOff modOff : Nat) : Prop :=
  b = m ∧ headBase s baseOff < headModulus s modOff

@[simp] theorem afterClearDouble_executionEnv (s : State)
    (accumulator : UInt256) (count : Nat) (rest : List UInt256) :
    (BigBase.afterClearDouble s accumulator count rest).executionEnv =
      s.executionEnv := by
  simp [BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero]

@[simp] theorem afterClearDouble_halt (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) :
    (BigBase.afterClearDouble s accumulator count rest).halt = s.halt := by
  simp [BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero]

@[simp] theorem afterClearDouble_stack (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) :
    (BigBase.afterClearDouble s accumulator count rest).stack =
      BigBase.frame accumulator count rest := by
  simp [BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero]

@[simp] theorem initialized_executionEnv (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (initialized s accumulator count b e m baseOff expOff modOff returnDest
      rest).executionEnv = s.executionEnv := by
  simp [initialized]

@[simp] theorem initialized_halt (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (initialized s accumulator count b e m baseOff expOff modOff returnDest
      rest).halt = s.halt := by
  simp [initialized]

@[simp] theorem initialized_stack (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (initialized s accumulator count b e m baseOff expOff modOff returnDest
      rest).stack =
      stack accumulator count b e m baseOff expOff modOff returnDest rest := by
  simp [initialized, stack]

@[simp] theorem loaded_executionEnv (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (loaded s accumulator count b e m baseOff expOff modOff returnDest
      rest).executionEnv = s.executionEnv := by
  simp [loaded, BigLoad.loadReturned, BigLoad.loadLoop]

@[simp] theorem loaded_halt (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) :
    (loaded s accumulator count b e m baseOff expOff modOff returnDest
      rest).halt = s.halt := by
  simp [loaded, BigLoad.loadReturned, BigLoad.loadLoop]

@[simp] private theorem directPCs (i : Nat) (hi : 1123 ≤ i)
    (hii : i ≤ 1154) :
    Artifact.submissionArtifact.instructionPC i =
      [1518, 1519, 1521, 1524, 1525, 1526, 1527, 1528,
       1529, 1532, 1533, 1534, 1535, 1536, 1537, 1538,
       1539, 1542, 1543, 1546, 1549, 1550, 1551, 1554,
       1555, 1556, 1557, 1560, 1561, 1562, 1563, 1566][i - 1123]! := by
  interval_cases i <;> decide

@[simp] private theorem outerFinishPCs (i : Nat) (hi : 707 ≤ i)
    (hii : i ≤ 716) :
    Artifact.submissionArtifact.instructionPC i =
      [925, 926, 927, 930, 931, 932, 934, 937, 940, 943][i - 707]! := by
  interval_cases i <;> decide

private theorem jump104 :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

private theorem jump439 :
    Decode.isValidJumpDest submissionBytecode 439 = true :=
  Artifact.isValidJumpDest_index 353 (by rfl)

private theorem jump831 :
    Decode.isValidJumpDest submissionBytecode 831 = true :=
  Artifact.isValidJumpDest_index 643 (by rfl)

private theorem jump925 :
    Decode.isValidJumpDest submissionBytecode 925 = true :=
  Artifact.isValidJumpDest_index 707 (by rfl)

private theorem jump1335 :
    Decode.isValidJumpDest submissionBytecode 1335 = true :=
  Artifact.isValidJumpDest_index 990 (by rfl)

private theorem jump1555 :
    Decode.isValidJumpDest submissionBytecode 1555 = true :=
  Artifact.isValidJumpDest_index 1147 (by rfl)

private theorem jump1561 :
    Decode.isValidJumpDest submissionBytecode 1561 = true :=
  Artifact.isValidJumpDest_index 1151 (by rfl)

theorem run_initialize (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock initializePath
      (BigBase.afterClearDouble s accumulator count
        (fullRest b e m baseOff expOff modOff returnDest rest)) =
      some (initialized s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 11, rest.length + n < 1024 := by omega
  have h1518 : (1518 : UInt256).toNat = 1518 := by decide
  have h1518Word : (1518 : UInt256) = UInt256.ofNat 1518 := by decide
  have h1519 : (1519 : UInt256).toNat = 1519 := by decide
  have h1521 : (1521 : UInt256).toNat = 1521 := by decide
  have h1524 : (1524 : UInt256).toNat = 1524 := by decide
  have h1525Word : (1525 : UInt256) = UInt256.ofNat 1525 := by decide
  have h1Nat : (1 : UInt256).toNat = 1 := by decide
  have h3072Nat : (3072 : UInt256).toNat = 3072 := by decide
  have hpc : (UInt256.ofNat 1519 + UInt256.ofNat 2 + UInt256.ofNat 3).succ =
      UInt256.ofNat 1525 := by decide
  simp (disch := omega) [initializePath, opAt, pushAt, wfOp, initialized,
    BigBase.afterClearDouble, BigHelpers.clearReturned, BigModulus.scanNonzero,
    BigBase.frame, fullRest, hrun, directPCs, hc, h1518, h1518Word,
    h1519, h1521, h1524, h1525Word, h1Nat, h3072Nat, hpc,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_sizePassed (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (_hb : b < 2 ^ 256) (hm : m < 2 ^ 256) (heq : b = m)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sizeGuardPath
      (initialized s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (sizePassed s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have h1525 : (1525 : UInt256).toNat = 1525 := by decide
  have h1526 : (1526 : UInt256).toNat = 1526 := by decide
  have h1527 : (1527 : UInt256).toNat = 1527 := by decide
  have h1528 : (1528 : UInt256).toNat = 1528 := by decide
  have h1529 : (1529 : UInt256).toNat = 1529 := by decide
  have h1532 : (1532 : UInt256).toNat = 1532 := by decide
  have h1533Word : (1533 : UInt256) = UInt256.ofNat 1533 := by decide
  have hpc : (UInt256.ofNat 1529 + UInt256.ofNat 3).succ =
      UInt256.ofNat 1533 := by decide
  simp (disch := omega) [sizeGuardPath, opAt, pushAt, wfOp, initialized,
    sizePassed, stack, BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero, BigBase.frame, fullRest, hrun, directPCs, hc,
    h1525, h1526, h1527, h1528, h1529, h1532, h1533Word, hpc,
    UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hm, heq]

theorem run_sizeFallback (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hb : b < 2 ^ 256) (hm : m < 2 ^ 256) (hne : b ≠ m)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock sizeGuardPath
      (initialized s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (fallbackEntry s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have h1561 : (1561 : UInt256).toNat = 1561 := by decide
  have h1561Word : (1561 : UInt256) = UInt256.ofNat 1561 := by decide
  have hne' : m ≠ b := Ne.symm hne
  simp (disch := omega) [sizeGuardPath, opAt, pushAt, wfOp, initialized,
    fallbackEntry, stack, BigBase.afterClearDouble, BigHelpers.clearReturned,
    BigModulus.scanNonzero, BigBase.frame, fullRest, hrun, hcode, directPCs,
    hc, jump1561, h1561, h1561Word, UInt256.eq, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, hb, hm, hne, hne']

theorem run_headPassed (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hbaseOff : baseOff < 2 ^ 256) (hmodOff : modOff < 2 ^ 256)
    (hlt : headBase s baseOff < headModulus s modOff)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock headGuardPath
      (sizePassed s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (headPassed s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have hone : UInt256.ofNat 1 = (1 : UInt256) := by decide
  have hltWord :
      UInt256.lt (MachineState.readWord s.executionEnv.calldata baseOff)
        (MachineState.readWord s.executionEnv.calldata modOff) = 1 := by
    rw [UInt256.lt, if_pos (by simpa [headBase, headModulus] using hlt)]
    exact hone
  have hpc : (UInt256.ofNat 1539 + UInt256.ofNat 3).succ =
      UInt256.ofNat 1543 := by decide
  have honeNat : (UInt256.ofNat 1).toNat = 1 := by decide
  have honeLitNat : (1 : UInt256).toNat = 1 := by decide
  simp (disch := omega) [headGuardPath, opAt, pushAt, wfOp, sizePassed,
    initialized, headPassed, stack, BigBase.frame, fullRest,
    headBase, headModulus, hrun, directPCs, hc, hltWord, hpc, hone, honeNat,
    honeLitNat,
    UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
    hbaseOff, hmodOff]

theorem run_headFallback (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hbaseOff : baseOff < 2 ^ 256) (hmodOff : modOff < 2 ^ 256)
    (hnlt : ¬ headBase s baseOff < headModulus s modOff)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock headGuardPath
      (sizePassed s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (fallbackEntry s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have hzero : UInt256.ofNat 0 = (0 : UInt256) := by decide
  have hltWord :
      UInt256.lt (MachineState.readWord s.executionEnv.calldata baseOff)
        (MachineState.readWord s.executionEnv.calldata modOff) = 0 := by
    rw [UInt256.lt, if_neg (by simpa [headBase, headModulus] using hnlt)]
    exact hzero
  have h1561 : (1561 : UInt256).toNat = 1561 := by decide
  have h1561Word : (1561 : UInt256) = UInt256.ofNat 1561 := by decide
  have hzeroNat : (UInt256.ofNat 0).toNat = 0 := by decide
  have hzeroLitNat : (0 : UInt256).toNat = 0 := by decide
  simp (disch := omega) [headGuardPath, opAt, pushAt, wfOp, sizePassed,
    initialized, fallbackEntry, stack, BigBase.frame, fullRest,
    headBase, headModulus, hrun, hcode, directPCs, hc, hltWord,
    h1561, h1561Word, hzero, hzeroNat, hzeroLitNat, UInt256.isTrue, jump1561,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc,
    hbaseOff, hmodOff]

theorem run_directLoad (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock directLoadPath
      (headPassed s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (BigLoad.loadEntry
        (initialized s accumulator count b e m baseOff expOff modOff
          returnDest rest)
        (UInt256.ofNat baseOff) (UInt256.ofNat b) 1024 1555
        (stack accumulator count b e m baseOff expOff modOff returnDest rest)) := by
  have hc : ∀ n ≤ 15, rest.length + n < 1024 := by omega
  have h439 : (439 : UInt256).toNat = 439 := by decide
  have h439Word : (439 : UInt256) = UInt256.ofNat 439 := by decide
  have hpc1 : (UInt256.ofNat 1543 + UInt256.ofNat 3 + UInt256.ofNat 3).succ.toNat =
      1550 := by decide
  have hpc2 : (UInt256.ofNat 1543 + UInt256.ofNat 3 + UInt256.ofNat 3).succ.succ.toNat =
      1551 := by decide
  simp (disch := omega) [directLoadPath, opAt, pushAt, wfOp, headPassed,
    initialized, stack, BigBase.frame, fullRest, BigLoad.loadEntry,
    hrun, hcode, directPCs, hc, jump439, h439, h439Word, hpc1, hpc2,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_fastReturn (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fastReturnPath
      (loaded s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (directOuterExit s accumulator count b e m baseOff expOff modOff
        returnDest rest) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have h1555 : (1555 : UInt256).toNat = 1555 := by decide
  have h925 : (925 : UInt256).toNat = 925 := by decide
  have h925Word : (925 : UInt256) = UInt256.ofNat 925 := by decide
  have h1556 : (UInt256.succ 1555).toNat = 1556 := by decide
  have h1557 : (UInt256.succ 1555).succ.toNat = 1557 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp (disch := omega) [fastReturnPath, opAt, pushAt, wfOp, loaded,
    directOuterExit, BigLoad.loadReturned, BigLoad.loadLoop, stack,
    BigBase.frame, fullRest, hrun, hcode, directPCs, hc, jump925,
    h1555, h1556, h1557, h925, h925Word, hzero,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_fallback (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock fallbackPath
      (fallbackEntry s accumulator count b e m baseOff expOff modOff returnDest rest) =
      some (BigBase.baseLoopEntry s accumulator count
        (fullRest b e m baseOff expOff modOff returnDest rest)) := by
  have hc : ∀ n ≤ 13, rest.length + n < 1024 := by omega
  have h1561 : (1561 : UInt256).toNat = 1561 := by decide
  have h831 : (831 : UInt256).toNat = 831 := by decide
  have h831Word : (831 : UInt256) = UInt256.ofNat 831 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp (disch := omega) [fallbackPath, opAt, pushAt, wfOp, fallbackEntry,
    initialized, BigBase.baseLoopEntry, BigBase.afterClearDouble,
    BigHelpers.clearReturned, BigModulus.scanNonzero, BigBase.frame, fullRest,
    hrun, hcode, directPCs, hc, jump831, h1561, h831, h831Word, hzero,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

theorem run_directOuterFinish (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1006)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerFinishPath
      (directOuterExit s accumulator count b e m baseOff expOff modOff
        returnDest rest) =
      some (BigHelpers.addEntry
        (directOuterExit s accumulator count b e m baseOff expOff modOff
          returnDest rest)
        2048 3072 1 0 count 1335
        (stack accumulator count b e m baseOff expOff modOff returnDest rest)) := by
  have hc : ∀ n ≤ 18, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h925 : (925 : UInt256).toNat = 925 := by decide
  have h925Word : (925 : UInt256) = UInt256.ofNat 925 := by decide
  have h1335Word : (1335 : UInt256) = UInt256.ofNat 1335 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hpc : (UInt256.ofNat 932 + UInt256.ofNat 2 + UInt256.ofNat 3 +
      UInt256.ofNat 3 + UInt256.ofNat 3).succ = UInt256.ofNat 944 := by decide
  have hpc0 : (UInt256.ofNat 927 + UInt256.ofNat 3).succ.toNat = 931 := by decide
  have hpc1 : (UInt256.ofNat 927 + UInt256.ofNat 3).succ.succ.toNat = 932 := by decide
  simp (disch := omega) [outerFinishPath, opAt, pushAt, wfOp,
    directOuterExit,
    stack, fullRest, BigBase.frame, BigHelpers.addEntry, hcode, hrun,
    h104, h104Word, h925, h925Word, h1335Word, hzero, hc,
    outerFinishPCs, jump104, hpc, hpc0, hpc1,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

def gasSteps_eligible (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 980)
    (hcount : count < 2 ^ 256) (hb : b < 2 ^ 256)
    (hm : m < 2 ^ 256) (hbaseOff : baseOff < 2 ^ 256)
    (hmodOff : modOff < 2 ^ 256) (hoff : baseOff + b ≤ 2 ^ 256)
    (heligible : Eligible s b m baseOff modOff)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigBase.afterClearDouble s accumulator count
        (fullRest b e m baseOff expOff modOff returnDest rest))
      (directInitialAccumulator s accumulator count b e m baseOff expOff
        modOff returnDest rest) := by
  rcases heligible with ⟨heq, hhead⟩
  have hraw : rest.length < 1008 := by omega
  have hstack :
      (stack accumulator count b e m baseOff expOff modOff returnDest rest).length <
        1000 := by
    simp [stack, BigBase.frame, fullRest]
    omega
  have hinit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka initializePath
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, Artifact.submissionArtifact] using hcode)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hfork)
      (run_initialize s accumulator count b e m baseOff expOff modOff
        returnDest rest hraw hrun)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero] using hrun)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hnp)
  have hsize := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka sizeGuardPath
      (by simpa [initialized, Artifact.submissionArtifact] using hcode)
      (by simpa [initialized, State.fork] using hfork)
      (run_sizePassed s accumulator count b e m baseOff expOff modOff
        returnDest rest hraw hb hm heq hrun)
      (by simpa [initialized] using hrun)
      (by simpa [initialized, State.fork] using hnp)
  have hheadStep := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka headGuardPath
      (by simpa [sizePassed, initialized, Artifact.submissionArtifact] using hcode)
      (by simpa [sizePassed, initialized, State.fork] using hfork)
      (run_headPassed s accumulator count b e m baseOff expOff modOff
        returnDest rest hraw hbaseOff hmodOff hhead hrun)
      (by simpa [sizePassed, initialized] using hrun)
      (by simpa [sizePassed, initialized, State.fork] using hnp)
  have htoLoad := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka directLoadPath
      (by simpa [headPassed, initialized, Artifact.submissionArtifact] using hcode)
      (by simpa [headPassed, initialized, State.fork] using hfork)
      (run_directLoad s accumulator count b e m baseOff expOff modOff
        returnDest rest hraw hcode hrun)
      (by simpa [headPassed, initialized] using hrun)
      (by simpa [headPassed, initialized, State.fork] using hnp)
  have hload := BigLoad.gasSteps_loadBigEndian
    (initialized s accumulator count b e m baseOff expOff modOff returnDest rest)
    baseOff b 1024 1555
    (stack accumulator count b e m baseOff expOff modOff returnDest rest)
    hstack hbaseOff hoff hb
    (by simpa [initialized] using hcode)
    (by simpa [initialized, State.fork] using hfork)
    (by simpa [initialized] using hrun)
    (by simpa [initialized, State.fork] using hnp) jump1555
  have hfast := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fastReturnPath
      (by simpa [Artifact.submissionArtifact] using hcode)
      (by simpa [State.fork] using hfork)
      (run_fastReturn s accumulator count b e m baseOff expOff modOff
        returnDest rest hraw hcode hrun)
      (by simpa using hrun)
      (by simpa [State.fork] using hnp)
  have houter := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerFinishPath
      (by simpa [directOuterExit, Artifact.submissionArtifact] using hcode)
      (by simpa [directOuterExit, State.fork] using hfork)
      (run_directOuterFinish s accumulator count b e m baseOff expOff modOff
        returnDest rest (by omega) hcode hrun)
      (by simpa [directOuterExit] using hrun)
      (by simpa [directOuterExit, State.fork] using hnp)
  have hadd := BigHelpers.gasSteps_addMaskedMod
    (directOuterExit s accumulator count b e m baseOff expOff modOff
      returnDest rest)
    2048 3072 1 0 count 1335
    (stack accumulator count b e m baseOff expOff modOff returnDest rest)
    hstack hcount (by decide)
    (by simpa [directOuterExit] using hcode)
    (by simpa [directOuterExit, State.fork] using hfork)
    (by simpa [directOuterExit] using hrun)
    (by simpa [directOuterExit, State.fork] using hnp) jump1335
  exact hinit.trans <| hsize.trans <| hheadStep.trans <| htoLoad.trans <|
    hload.trans <| hfast.trans <| houter.trans hadd

def gasSteps_ineligible (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1008)
    (hb : b < 2 ^ 256) (hm : m < 2 ^ 256)
    (hbaseOff : baseOff < 2 ^ 256) (hmodOff : modOff < 2 ^ 256)
    (hineligible : ¬ Eligible s b m baseOff modOff)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigBase.afterClearDouble s accumulator count
        (fullRest b e m baseOff expOff modOff returnDest rest))
      (BigBase.baseLoopEntry s accumulator count
        (fullRest b e m baseOff expOff modOff returnDest rest)) := by
  have hinit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka initializePath
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, Artifact.submissionArtifact] using hcode)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hfork)
      (run_initialize s accumulator count b e m baseOff expOff modOff
        returnDest rest hcap hrun)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero] using hrun)
      (by simpa [BigBase.afterClearDouble, BigHelpers.clearReturned,
        BigModulus.scanNonzero, State.fork] using hnp)
  have hfallback := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka fallbackPath
      (by simpa [fallbackEntry, initialized, Artifact.submissionArtifact] using hcode)
      (by simpa [fallbackEntry, initialized, State.fork] using hfork)
      (run_fallback s accumulator count b e m baseOff expOff modOff returnDest
        rest hcap hcode hrun)
      (by simpa [fallbackEntry, initialized] using hrun)
      (by simpa [fallbackEntry, initialized, State.fork] using hnp)
  by_cases heq : b = m
  · have hnlt : ¬ headBase s baseOff < headModulus s modOff := by
      intro hlt
      exact hineligible ⟨heq, hlt⟩
    have hsize := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka sizeGuardPath
        (by simpa [initialized, Artifact.submissionArtifact] using hcode)
        (by simpa [initialized, State.fork] using hfork)
        (run_sizePassed s accumulator count b e m baseOff expOff modOff
          returnDest rest hcap hb hm heq hrun)
        (by simpa [initialized] using hrun)
        (by simpa [initialized, State.fork] using hnp)
    have hheadStep := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka headGuardPath
        (by simpa [sizePassed, initialized, Artifact.submissionArtifact] using hcode)
        (by simpa [sizePassed, initialized, State.fork] using hfork)
        (run_headFallback s accumulator count b e m baseOff expOff modOff
          returnDest rest hcap hbaseOff hmodOff hnlt hcode hrun)
        (by simpa [sizePassed, initialized] using hrun)
        (by simpa [sizePassed, initialized, State.fork] using hnp)
    exact hinit.trans <| hsize.trans <| hheadStep.trans hfallback
  · have hsize := Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka sizeGuardPath
        (by simpa [initialized, Artifact.submissionArtifact] using hcode)
        (by simpa [initialized, State.fork] using hfork)
        (run_sizeFallback s accumulator count b e m baseOff expOff modOff
          returnDest rest hcap hb hm heq hcode hrun)
        (by simpa [initialized] using hrun)
        (by simpa [initialized, State.fork] using hnp)
    exact hinit.trans <| hsize.trans hfallback

theorem eligible_base_lt_modulus (s : State) (b m baseOff modOff : Nat)
    (hb32 : 32 ≤ b) (heligible : Eligible s b m baseOff modOff) :
    Precompile.bytesToNatPadded s.executionEnv.calldata baseOff b <
      Precompile.bytesToNatPadded s.executionEnv.calldata modOff m := by
  rcases heligible with ⟨rfl, hhead⟩
  let calldata := s.executionEnv.calldata
  let tail := b - 32
  let q := 256 ^ tail
  have hsum : 32 + tail = b := by omega
  have hbaseSplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    calldata baseOff 32 tail
  have hmodSplit := Challenge.EvmProof.Bytes.bytesToNatPadded_add
    calldata modOff 32 tail
  rw [hsum] at hbaseSplit hmodSplit
  have htail := Challenge.EvmProof.Bytes.bytesToNatPadded_lt_pow
    calldata (baseOff + 32) tail
  have hheads :
      Precompile.bytesToNatPadded calldata baseOff 32 <
        Precompile.bytesToNatPadded calldata modOff 32 := by
    simpa [headBase, headModulus, calldata,
      Challenge.EvmProof.Bytes.readWord_toNat] using hhead
  have hfirst :
      Precompile.bytesToNatPadded calldata baseOff 32 * q +
          Precompile.bytesToNatPadded calldata (baseOff + 32) tail <
        (Precompile.bytesToNatPadded calldata baseOff 32 + 1) * q := by
    have hadd := Nat.add_lt_add_left htail
      (Precompile.bytesToNatPadded calldata baseOff 32 * q)
    simpa [q, Nat.add_mul, Nat.add_assoc] using hadd
  have hmiddle :
      (Precompile.bytesToNatPadded calldata baseOff 32 + 1) * q ≤
        Precompile.bytesToNatPadded calldata modOff 32 * q :=
    Nat.mul_le_mul_right q (Nat.succ_le_of_lt hheads)
  calc
    Precompile.bytesToNatPadded calldata baseOff b =
        Precompile.bytesToNatPadded calldata baseOff 32 * q +
          Precompile.bytesToNatPadded calldata (baseOff + 32) tail := by
            simpa [q] using hbaseSplit
    _ < (Precompile.bytesToNatPadded calldata baseOff 32 + 1) * q := hfirst
    _ ≤ Precompile.bytesToNatPadded calldata modOff 32 * q := hmiddle
    _ ≤ Precompile.bytesToNatPadded calldata modOff 32 * q +
        Precompile.bytesToNatPadded calldata (modOff + 32) tail := by omega
    _ = Precompile.bytesToNatPadded calldata modOff b := by
      simpa [q] using hmodSplit.symm

theorem loaded_represents_base (s : State) (accumulator : UInt256)
    (count b e m baseOff expOff modOff : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hbaseOff : baseOff < 2 ^ 256)
    (hb : b < 2 ^ 256)
    (hfit : 1024 + 32 * Limbs.limbCount b < 2 ^ 256)
    (hzero : Limbs.Represents
      (initialized s accumulator count b e m baseOff expOff modOff
        returnDest rest).memory 1024 (Limbs.limbCount b) 0) :
    Limbs.Represents
      (loaded s accumulator count b e m baseOff expOff modOff returnDest
        rest).memory 1024 (Limbs.limbCount b)
      (Precompile.bytesToNatPadded s.executionEnv.calldata baseOff b) := by
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  simpa [loaded, h1024] using
    BigLoadCorrect.loadReturned_represents
      (initialized s accumulator count b e m baseOff expOff modOff
        returnDest rest)
      baseOff 1024 b 1555
      (stack accumulator count b e m baseOff expOff modOff returnDest rest)
      hbaseOff hb hfit hzero

theorem directInitialAccumulator_represents (s : State)
    (accumulator : UInt256) (count b e m baseOff expOff modOff : Nat)
    (returnDest : UInt256) (rest : List UInt256) (baseValue modulusValue : Nat)
    (hcountPos : 0 < count) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue) (_hbaseReduced : baseValue < modulusValue)
    (hbase : Limbs.Represents
      (loaded s accumulator count b e m baseOff expOff modOff returnDest
        rest).memory 1024 count baseValue)
    (hone : Limbs.Represents
      (loaded s accumulator count b e m baseOff expOff modOff returnDest
        rest).memory 3072 count 1)
    (hzero2048 : Limbs.Represents
      (loaded s accumulator count b e m baseOff expOff modOff returnDest
        rest).memory 2048 count 0)
    (hmodulus : Limbs.Represents
      (loaded s accumulator count b e m baseOff expOff modOff returnDest
        rest).memory 0 count modulusValue) :
    let returned := directInitialAccumulator s accumulator count b e m baseOff
      expOff modOff returnDest rest
    Limbs.Represents returned.memory 2048 count (1 % modulusValue) ∧
      Limbs.Represents returned.memory 1024 count baseValue ∧
      Limbs.Represents returned.memory 0 count modulusValue := by
  let exit := directOuterExit s accumulator count b e m baseOff expOff modOff
    returnDest rest
  let helperRest := stack accumulator count b e m baseOff expOff modOff
    returnDest rest
  have h0 : (0 : UInt256) = UInt256.ofNat 0 := by decide
  have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1024 : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h2048 : (2048 : UInt256) = UInt256.ofNat 2048 := by decide
  have h3072 : (3072 : UInt256) = UInt256.ofNat 3072 := by decide
  have h1335 : (1335 : UInt256) = UInt256.ofNat 1335 := by decide
  have hexitBase : Limbs.Represents exit.memory 1024 count baseValue := by
    simpa [exit, directOuterExit] using hbase
  have hexitOne : Limbs.Represents exit.memory 3072 count 1 := by
    simpa [exit, directOuterExit] using hone
  have hexitZero : Limbs.Represents exit.memory 2048 count 0 := by
    simpa [exit, directOuterExit] using hzero2048
  have hexitModulus : Limbs.Represents exit.memory 0 count modulusValue := by
    simpa [exit, directOuterExit] using hmodulus
  have hacc : Limbs.Represents
      (directInitialAccumulator s accumulator count b e m baseOff expOff modOff
        returnDest rest).memory 2048 count (1 % modulusValue) := by
    simpa [directInitialAccumulator, exit, helperRest, h0, h1, h2048,
      h3072, h1335] using
      BigHelpers.addReturned_represents_mod exit 2048 3072 0 count 1 0 1
        modulusValue (UInt256.ofNat 1335) helperRest (by omega) (by omega)
        (by omega) (by omega) (by omega) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        hexitZero hexitOne hexitModulus (by omega) (by omega)
        hexitModulus.1
  have hbaseAfter : Limbs.Represents
      (directInitialAccumulator s accumulator count b e m baseOff expOff modOff
        returnDest rest).memory 1024 count baseValue := by
    simpa [directInitialAccumulator, exit, helperRest, h0, h1, h2048,
      h3072, h1335] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 1024 count
        baseValue (UInt256.ofNat 1335) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitBase
  have hmodAfter : Limbs.Represents
      (directInitialAccumulator s accumulator count b e m baseOff expOff modOff
        returnDest rest).memory 0 count modulusValue := by
    simpa [directInitialAccumulator, exit, helperRest, h0, h1, h2048,
      h3072, h1335] using
      BigHelpers.addReturned_preserves_region exit 2048 3072 1 0 0 count
        modulusValue (UInt256.ofNat 1335) helperRest (by omega) (by omega)
        (Or.inr (by omega)) (Or.inl (by omega)) hexitModulus
  exact ⟨hacc, hbaseAfter, hmodAfter⟩

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBaseDirect
