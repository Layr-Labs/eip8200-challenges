import Challenge.Sha256.Submission.Proofs.Bytecode.Accessors
import Challenge.EvmProof.Memory
set_option warningAsError true
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false
/-!
# Certified digest output for the reference SHA bytecode

The final bytecode block loads the eight chaining-state words through the
internal `hAt` helper, packs them into one big-endian 256-bit word, stores that
word at memory offset zero, and returns the resulting 32 bytes.  The summaries
in this file deliberately start from an arbitrary running state: callers only
need to establish the code/fork facts and the output-block entry stack.
-/

namespace Challenge.Sha256.Submission.Proofs.Bytecode.Output

open EvmSemantics
open EvmSemantics.EVM

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

private theorem uintZero : (0 : UInt256) = UInt256.ofNat 0 := by decide

@[simp] private theorem slot0 : Accessors.slotOffset 288 (UInt256.ofNat 0) = 288 := by decide
@[simp] private theorem slot1 : Accessors.slotOffset 288 (UInt256.ofNat 1) = 320 := by decide
@[simp] private theorem slot2 : Accessors.slotOffset 288 (UInt256.ofNat 2) = 352 := by decide
@[simp] private theorem slot3 : Accessors.slotOffset 288 (UInt256.ofNat 3) = 384 := by decide
@[simp] private theorem slot4 : Accessors.slotOffset 288 (UInt256.ofNat 4) = 416 := by decide
@[simp] private theorem slot5 : Accessors.slotOffset 288 (UInt256.ofNat 5) = 448 := by decide
@[simp] private theorem slot6 : Accessors.slotOffset 288 (UInt256.ofNat 6) = 480 := by decide
@[simp] private theorem slot7 : Accessors.slotOffset 288 (UInt256.ofNat 7) = 512 := by decide
@[simp] private theorem slotExpr0 :
    (UInt256.shiftLeft (UInt256.ofNat 0) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 288 := by decide
@[simp] private theorem slotExpr1 :
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 320 := by decide
@[simp] private theorem slotExpr2 :
    (UInt256.shiftLeft (UInt256.ofNat 2) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 352 := by decide
@[simp] private theorem slotExpr3 :
    (UInt256.shiftLeft (UInt256.ofNat 3) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 384 := by decide
@[simp] private theorem slotExpr4 :
    (UInt256.shiftLeft (UInt256.ofNat 4) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 416 := by decide
@[simp] private theorem slotExpr5 :
    (UInt256.shiftLeft (UInt256.ofNat 5) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 448 := by decide
@[simp] private theorem slotExpr6 :
    (UInt256.shiftLeft (UInt256.ofNat 6) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 480 := by decide
@[simp] private theorem slotExpr7 :
    (UInt256.shiftLeft (UInt256.ofNat 7) (UInt256.ofNat 5) + UInt256.ofNat 288).toNat = 512 := by decide

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

def startPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨755, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨756, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨757, .push ⟨8, by decide⟩ (UInt256.ofNat 512), by rfl, by decide⟩,
   ⟨758, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setup6Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨759, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨760, .push ⟨8, by decide⟩ (UInt256.ofNat 480), by rfl, by decide⟩,
   ⟨761, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setup5Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨762, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨763, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨764, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨765, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨766, .push ⟨8, by decide⟩ (UInt256.ofNat 448), by rfl, by decide⟩,
   ⟨767, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setup4Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨768, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨769, .push ⟨1, by decide⟩ (UInt256.ofNat 64), by rfl, by decide⟩,
   ⟨770, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨771, .push ⟨8, by decide⟩ (UInt256.ofNat 416), by rfl, by decide⟩,
   ⟨772, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setup3Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨773, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨774, .push ⟨1, by decide⟩ (UInt256.ofNat 96), by rfl, by decide⟩,
   ⟨775, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨776, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨777, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨778, .push ⟨8, by decide⟩ (UInt256.ofNat 384), by rfl, by decide⟩,
   ⟨779, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩]

def setup2Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨780, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨781, .push ⟨1, by decide⟩ (UInt256.ofNat 128), by rfl, by decide⟩,
   ⟨782, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨783, .push ⟨7, by decide⟩ (UInt256.ofNat 352), by rfl, by decide⟩,
   ⟨784, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨785, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def setup1Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨786, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨787, .push ⟨1, by decide⟩ (UInt256.ofNat 160), by rfl, by decide⟩,
   ⟨788, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨789, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨790, .push ⟨7, by decide⟩ (UInt256.ofNat 320), by rfl, by decide⟩,
   ⟨791, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨792, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def setup0Path :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨793, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨794, .push ⟨1, by decide⟩ (UInt256.ofNat 192), by rfl, by decide⟩,
   ⟨795, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨796, .push ⟨6, by decide⟩ (UInt256.ofNat 288), by rfl, by decide⟩,
   ⟨797, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨798, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩]

def finishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.referenceArtifact .Osaka) :=
  [⟨799, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨800, .push ⟨1, by decide⟩ (UInt256.ofNat 224), by rfl, by decide⟩,
   ⟨801, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨802, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨803, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨804, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨805, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨806, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨807, .push ⟨1, by decide⟩ (UInt256.ofNat 32), by rfl, by decide⟩,
   ⟨808, .push ⟨0, by decide⟩ (UInt256.ofNat 0), by rfl, by decide⟩,
   ⟨809, .op .RETURN, by rfl, wfOp (by decide) trivial rfl⟩]

def hWord (s : State) (i : Nat) : UInt256 :=
  MachineState.readWord s.memory
    (Accessors.slotOffset 288 (UInt256.ofNat i))

def pair67 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 6) (UInt256.ofNat 32)) (hWord s 7)

def shifted5 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 5) (UInt256.ofNat 64)

def pair45 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 4) (UInt256.ofNat 96)) (shifted5 s)

def lowHalf (s : State) : UInt256 := UInt256.lor (pair45 s) (pair67 s)

def shifted3 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 3) (UInt256.ofNat 128)

def pair23 (s : State) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft (hWord s 2) (UInt256.ofNat 160)) (shifted3 s)

def shifted1 (s : State) : UInt256 :=
  UInt256.shiftLeft (hWord s 1) (UInt256.ofNat 192)

/-- The exact 256-bit packing expression computed by opcodes 800--804. -/
def digestWord (s : State) : UInt256 :=
  UInt256.lor
    (UInt256.lor
      (UInt256.lor
        (UInt256.shiftLeft (hWord s 0) (UInt256.ofNat 224)) (shifted1 s))
      (pair23 s))
    (lowHalf s)

def outputEntry (s : State) (offset : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1401, stack := offset :: rest }

def afterH7 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned s 288 (UInt256.ofNat 7) (UInt256.ofNat 1413) rest

def afterH6 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH7 s rest) 288 (UInt256.ofNat 6)
    (UInt256.ofNat 1424) (hWord s 7 :: rest)

def afterH5 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH6 s rest) 288 (UInt256.ofNat 5)
    (UInt256.ofNat 1439) (pair67 s :: rest)

def afterH4 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH5 s rest) 288 (UInt256.ofNat 4)
    (UInt256.ofNat 1453) (shifted5 s :: pair67 s :: rest)

def afterH3 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH4 s rest) 288 (UInt256.ofNat 3)
    (UInt256.ofNat 1469) (lowHalf s :: rest)

def afterH2 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH3 s rest) 288 (UInt256.ofNat 2)
    (UInt256.ofNat 1483) (shifted3 s :: lowHalf s :: rest)

def afterH1 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH2 s rest) 288 (UInt256.ofNat 1)
    (UInt256.ofNat 1498) (pair23 s :: lowHalf s :: rest)

def afterH0 (s : State) (rest : List UInt256) : State :=
  Accessors.loadReturned (afterH1 s rest) 288 (UInt256.ofNat 0)
    (UInt256.ofNat 1511) (shifted1 s :: pair23 s :: lowHalf s :: rest)

def digestBytes (s : State) : ByteArray :=
  Data.Bytes.natToBytesPadded (digestWord s).toNat 32

def outputResult (s : State) (rest : List UInt256) : State :=
  let loaded := afterH0 s rest
  let storedMemory := MachineState.writeBytes loaded.memory (digestBytes s) 0
  let stored := { loaded with
    pc := UInt256.ofNat 1520
    stack := rest
    memory := storedMemory
    activeWords := loaded.activeWordsAfterUInt256 0 32 }
  { stored with
    pc := UInt256.ofNat 1523
    halt := .Returned
    hReturn := digestBytes s
    stack := rest
    activeWords := stored.activeWordsAfterUInt256 0 32 }

-- Instruction offsets in the final block.
@[simp] private theorem outputPC (i : Nat) (hlo : 755 ≤ i) (hhi : i ≤ 809) :
    Artifact.referenceArtifact.instructionPC i =
      [1401,1402,1403,1412,1413,1414,1423,1424,1425,1427,1428,
       1429,1438,1439,1440,1442,1443,1452,1453,1454,1456,1457,
       1458,1459,1468,1469,1470,1472,1473,1481,1482,1483,1484,
       1486,1487,1488,1496,1497,1498,1499,1501,1502,1509,1510,
       1511,1512,1514,1515,1516,1517,1518,1519,1520,1522,1523][i - 755]! := by
  interval_cases i <;> decide

theorem run_start (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1019) (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startPath (outputEntry s offset rest) =
      some (afterH7 s rest) := by
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  simp [startPath, outputEntry, afterH7, hWord, Accessors.loadReturned,
    Accessors.slotOffset, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    State.activeWordsAfterUInt256, hc0, hc1, hrun]

theorem run_setup6 (s : State) (h7 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1018) (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup6Path
      { s with pc := UInt256.ofNat 1413, stack := h7 :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 6)
        (UInt256.ofNat 1424) (h7 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [setup6Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc1, hc2, hrun]

theorem run_setup5 (s : State) (h6 h7 : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1017) (_hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup5Path
      { s with pc := UInt256.ofNat 1424, stack := h6 :: h7 :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 5)
        (UInt256.ofNat 1439)
        (UInt256.lor (UInt256.shiftLeft h6 (UInt256.ofNat 32)) h7 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [setup5Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc1, hc2, hc3, hrun]

theorem run_setup4 (s : State) (h5 packed67 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup4Path
      { s with pc := UInt256.ofNat 1439, stack := h5 :: packed67 :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 4)
        (UInt256.ofNat 1453)
        (UInt256.shiftLeft h5 (UInt256.ofNat 64) :: packed67 :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [setup4Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc2, hc3, hrun]

theorem run_setup3 (s : State) (h4 shifted5 packed67 : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup3Path
      { s with pc := UInt256.ofNat 1453, stack := h4 :: shifted5 :: packed67 :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 3)
        (UInt256.ofNat 1469)
        (UInt256.lor (UInt256.lor
          (UInt256.shiftLeft h4 (UInt256.ofNat 96)) shifted5) packed67 :: rest)) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [setup3Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc1, hc2, hc3, hc4, hrun]

theorem run_setup2 (s : State) (h3 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1017)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup2Path
      { s with pc := UInt256.ofNat 1469, stack := h3 :: packedLow :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 2)
        (UInt256.ofNat 1483)
        (UInt256.shiftLeft h3 (UInt256.ofNat 128) :: packedLow :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [setup2Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc2, hc3, hrun]

theorem run_setup1 (s : State) (h2 shifted3 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup1Path
      { s with pc := UInt256.ofNat 1483, stack := h2 :: shifted3 :: packedLow :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 1)
        (UInt256.ofNat 1498)
        (UInt256.lor (UInt256.shiftLeft h2 (UInt256.ofNat 160)) shifted3 ::
          packedLow :: rest)) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  simp [setup1Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc2, hc3, hc4, hrun]

theorem run_setup0 (s : State) (h1 packed23 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1016)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setup0Path
      { s with pc := UInt256.ofNat 1498, stack := h1 :: packed23 :: packedLow :: rest } =
      some (Accessors.loadReturned s 288 (UInt256.ofNat 0)
        (UInt256.ofNat 1511)
        (UInt256.shiftLeft h1 (UInt256.ofNat 192) :: packed23 :: packedLow :: rest)) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  simp [setup0Path, Accessors.loadReturned, Accessors.slotOffset,
    Challenge.EvmProof.Stepper.runLocatedBlock, Challenge.EvmProof.Stepper.runLocated,
    Challenge.EvmProof.Stepper.runInstr, State.activeWordsAfterUInt256,
    hc3, hc4, hc5, hrun]

theorem run_finish (s : State) (h0 shifted1 packed23 packedLow : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1019)
    (_hcode : s.executionEnv.code = submissionBytecode) (hrun : s.halt = .Running) :
    let word := UInt256.lor
      (UInt256.lor (UInt256.lor
        (UInt256.shiftLeft h0 (UInt256.ofNat 224)) shifted1) packed23)
      packedLow
    let bytes := Data.Bytes.natToBytesPadded word.toNat 32
    let storedMemory := MachineState.writeBytes s.memory bytes 0
    let stored := { s with
      pc := UInt256.ofNat 1520
      stack := rest
      memory := storedMemory
      activeWords := s.activeWordsAfterUInt256 0 32 }
    Challenge.EvmProof.Stepper.runLocatedBlock finishPath
      ({ s with
        pc := UInt256.ofNat 1511
        stack := h0 :: shifted1 :: packed23 :: packedLow :: rest }) =
      some { stored with
        pc := UInt256.ofNat 1523
        halt := .Returned
        hReturn := bytes
        stack := rest
        activeWords := stored.activeWordsAfterUInt256 0 32 } := by
  dsimp only
  have hc0 : rest.length < 1024 := by omega
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  let word := UInt256.lor
    (UInt256.lor
      (UInt256.lor (UInt256.shiftLeft h0 (UInt256.ofNat 224)) shifted1)
      packed23) packedLow
  let bytes := Data.Bytes.natToBytesPadded word.toNat 32
  have hsize : bytes.size = 32 := by
    simp [bytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  have hread := Challenge.EvmProof.Memory.readPadded_writeBytes_same s.memory bytes 0
  rw [hsize] at hread
  have hz : (⟨0⟩ : UInt256).toNat = 0 := rfl
  have h32 : (UInt256.ofNat 32).toNat = 32 := by decide
  simp [finishPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    State.activeWordsAfterUInt256, hc0, hc1, hc2, hc3, hc4, hc5,
    hrun, hread, hz, h32, word, bytes]

/-- The final output block returns exactly the 32-byte big-endian packing of
the eight words stored in H slots 0 through 7. -/
def gasSteps_output (s : State) (offset : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (outputEntry s offset rest) (outputResult s rest) := by
  let q7 := afterH7 s rest
  let q6 := afterH6 s rest
  let q5 := afterH5 s rest
  let q4 := afterH4 s rest
  let q3 := afterH3 s rest
  let q2 := afterH2 s rest
  let q1 := afterH1 s rest
  let q0 := afterH0 s rest
  have gStart : Challenge.EvmProof.GasSteps (outputEntry s offset rest) q7 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka startPath
    · simpa [outputEntry, Artifact.referenceArtifact] using hcode
    · simpa [outputEntry] using hfork
    · simpa [q7] using run_start s offset rest (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have q7code : q7.executionEnv.code = submissionBytecode := by
    simpa [q7, afterH7, Accessors.loadReturned] using hcode
  have q7fork : q7.fork = .Osaka := by simpa [q7, afterH7, Accessors.loadReturned] using hfork
  have q7run : q7.halt = .Running := by simpa [q7, afterH7, Accessors.loadReturned] using hrun
  have q7np : Precompile.isPrecompileWithConfig q7.executionEnv.precompileConfig q7.executionEnv.fork
      q7.executionEnv.codeAddr = false := by simpa [q7, afterH7, Accessors.loadReturned] using hnp
  have g6 : Challenge.EvmProof.GasSteps q7 q6 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.referenceArtifact .Osaka setup6Path q7code q7fork
    · simpa [q7, q6, afterH7, afterH6, hWord, Accessors.loadReturned] using
        run_setup6 q7 (hWord s 7) rest (by omega) q7code q7run
    · exact q7run
    · exact q7np
  have q6code : q6.executionEnv.code = submissionBytecode := by simpa [q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q6fork : q6.fork = .Osaka := by simpa [q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q6run : q6.halt = .Running := by simpa [q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q6np : Precompile.isPrecompileWithConfig q6.executionEnv.precompileConfig q6.executionEnv.fork q6.executionEnv.codeAddr = false := by simpa [q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g5 : Challenge.EvmProof.GasSteps q6 q5 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup5Path q6code q6fork
    · simpa [q6, q5, afterH6, afterH5, q7, afterH7, hWord, pair67, Accessors.loadReturned] using run_setup5 q6 (hWord s 6) (hWord s 7) rest (by omega) q6code q6run
    · exact q6run
    · exact q6np
  have q5code : q5.executionEnv.code = submissionBytecode := by simpa [q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q5fork : q5.fork = .Osaka := by simpa [q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q5run : q5.halt = .Running := by simpa [q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q5np : Precompile.isPrecompileWithConfig q5.executionEnv.precompileConfig q5.executionEnv.fork q5.executionEnv.codeAddr = false := by simpa [q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g4 : Challenge.EvmProof.GasSteps q5 q4 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup4Path q5code q5fork
    · simpa [q5, q4, afterH5, afterH4, q6, afterH6, q7, afterH7, hWord, shifted5, pair67, Accessors.loadReturned] using run_setup4 q5 (hWord s 5) (pair67 s) rest (by omega) q5code q5run
    · exact q5run
    · exact q5np
  have q4code : q4.executionEnv.code = submissionBytecode := by simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q4fork : q4.fork = .Osaka := by simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q4run : q4.halt = .Running := by simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q4np : Precompile.isPrecompileWithConfig q4.executionEnv.precompileConfig q4.executionEnv.fork q4.executionEnv.codeAddr = false := by simpa [q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g3 : Challenge.EvmProof.GasSteps q4 q3 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup3Path q4code q4fork
    · simpa [q4, q3, afterH4, afterH3, q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted5, pair67, pair45, lowHalf, Accessors.loadReturned] using run_setup3 q4 (hWord s 4) (shifted5 s) (pair67 s) rest (by omega) q4code q4run
    · exact q4run
    · exact q4np
  have q3code : q3.executionEnv.code = submissionBytecode := by simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q3fork : q3.fork = .Osaka := by simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q3run : q3.halt = .Running := by simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q3np : Precompile.isPrecompileWithConfig q3.executionEnv.precompileConfig q3.executionEnv.fork q3.executionEnv.codeAddr = false := by simpa [q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g2 : Challenge.EvmProof.GasSteps q3 q2 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup2Path q3code q3fork
    · simpa [q3, q2, afterH3, afterH2, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted3, Accessors.loadReturned] using run_setup2 q3 (hWord s 3) (lowHalf s) rest (by omega) q3code q3run
    · exact q3run
    · exact q3np
  have q2code : q2.executionEnv.code = submissionBytecode := by simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q2fork : q2.fork = .Osaka := by simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q2run : q2.halt = .Running := by simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q2np : Precompile.isPrecompileWithConfig q2.executionEnv.precompileConfig q2.executionEnv.fork q2.executionEnv.codeAddr = false := by simpa [q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g1 : Challenge.EvmProof.GasSteps q2 q1 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup1Path q2code q2fork
    · simpa [q2, q1, afterH2, afterH1, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted3, pair23, Accessors.loadReturned] using run_setup1 q2 (hWord s 2) (shifted3 s) (lowHalf s) rest (by omega) q2code q2run
    · exact q2run
    · exact q2np
  have q1code : q1.executionEnv.code = submissionBytecode := by simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q1fork : q1.fork = .Osaka := by simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q1run : q1.halt = .Running := by simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q1np : Precompile.isPrecompileWithConfig q1.executionEnv.precompileConfig q1.executionEnv.fork q1.executionEnv.codeAddr = false := by simpa [q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have g0 : Challenge.EvmProof.GasSteps q1 q0 := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka setup0Path q1code q1fork
    · simpa [q1, q0, afterH1, afterH0, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted1, Accessors.loadReturned] using run_setup0 q1 (hWord s 1) (pair23 s) (lowHalf s) rest (by omega) q1code q1run
    · exact q1run
    · exact q1np
  have q0code : q0.executionEnv.code = submissionBytecode := by simpa [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hcode
  have q0fork : q0.fork = .Osaka := by simpa [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hfork
  have q0run : q0.halt = .Running := by simpa [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hrun
  have q0np : Precompile.isPrecompileWithConfig q0.executionEnv.precompileConfig q0.executionEnv.fork q0.executionEnv.codeAddr = false := by simpa [q0, afterH0, q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, Accessors.loadReturned] using hnp
  have gFinish : Challenge.EvmProof.GasSteps q0 (outputResult s rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound Artifact.referenceArtifact .Osaka finishPath q0code q0fork
    · simpa [q0, outputResult, afterH0, q1, afterH1, q2, afterH2, q3, afterH3, q4, afterH4, q5, afterH5, q6, afterH6, q7, afterH7, hWord, shifted1, pair23, lowHalf, digestWord, digestBytes, Accessors.loadReturned] using run_finish q0 (hWord s 0) (shifted1 s) (pair23 s) (lowHalf s) rest (by omega) q0code q0run
    · exact q0run
    · exact q0np
  exact gStart.trans (g6.trans (g5.trans (g4.trans (g3.trans
    (g2.trans (g1.trans (g0.trans gFinish)))))))

@[simp] theorem outputResult_halt (s : State) (rest : List UInt256) :
    (outputResult s rest).halt = .Returned := by
  simp [outputResult]

@[simp] theorem outputResult_returnData (s : State) (rest : List UInt256) :
    (outputResult s rest).hReturn = digestBytes s := by
  simp [outputResult]

@[simp] theorem outputResult_memory (s : State) (rest : List UInt256) :
    (outputResult s rest).memory =
      MachineState.writeBytes s.memory (digestBytes s) 0 := by
  rfl

/-- The exact memory window consumed by the terminal `RETURN`. -/
theorem outputResult_memoryWindow (s : State) (rest : List UInt256) :
    MachineState.readPadded (outputResult s rest).memory 0 32 = digestBytes s := by
  rw [outputResult_memory]
  have hsize : (digestBytes s).size = 32 := by
    simp [digestBytes, Data.Bytes.natToBytesPadded, ByteArray.size]
  simpa [hsize] using Challenge.EvmProof.Memory.readPadded_writeBytes_same
    s.memory (digestBytes s) 0

/-- Reading the returned memory as an EVM word recovers the packed digest. -/
theorem outputResult_readWord (s : State) (rest : List UInt256) :
    MachineState.readWord (outputResult s rest).memory 0 = digestWord s := by
  rw [outputResult_memory]
  exact Challenge.EvmProof.Memory.readWord_writeWord s.memory 0 (digestWord s)

end Challenge.Sha256.Submission.Proofs.Bytecode.Output
