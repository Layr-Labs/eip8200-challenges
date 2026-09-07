import Challenge.Ripemd160.Submission.Proofs.Bytecode.Artifact
import Challenge.Ripemd160.Submission.Proofs.Bytecode.Word
import Challenge.EvmProof.Meter

set_option warningAsError true
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

/-!
# Direct bytecode trace for the RIPEMD-160 message schedule

The reference schedule has one sixteen-iteration loop.  Each iteration calls
the compiled `readLE32` and `xSet` helpers, loading four message bytes and
storing the resulting 32-bit word in the dedicated `X[i]` slot.
-/

namespace Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule

open EvmSemantics
open EvmSemantics.EVM

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (YulEvmCompiler.Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Challenge.EvmProof.Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

@[simp] private theorem succSmall (n : Nat) (h : n + 1 < 2 ^ 256) :
    (UInt256.ofNat n).succ = UInt256.ofNat (n + 1) :=
  Challenge.EvmProof.Word.succ_ofNat h

@[simp] private theorem addSmall (a b : Nat) (h : a + b < 2 ^ 256) :
    UInt256.ofNat a + UInt256.ofNat b = UInt256.ofNat (a + b) :=
  Challenge.EvmProof.Word.ofNat_add_ofNat h

abbrev Located :=
  Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka

def scheduleStartPath : List Located :=
  [⟨152, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨153, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩]

def conditionPath : List Located :=
  [⟨154, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨155, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨156, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨157, .op .LT, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨158, .op .ISZERO, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨159, .push ⟨2, by decide⟩ (UInt256.ofNat 0xff), by rfl, by decide⟩,
   ⟨160, .op .JUMPI, by rfl, wfOp (by decide) trivial rfl⟩]

def setupReadPath : List Located :=
  [⟨161, .push ⟨2, by decide⟩ (UInt256.ofNat 0xf4), by rfl, by decide⟩,
   ⟨162, .push ⟨2, by decide⟩ (UInt256.ofNat 0xee), by rfl, by decide⟩,
   ⟨163, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨164, .op (.Dup ⟨3, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨165, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨166, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨167, .op (.Dup ⟨5, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨168, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨169, .push ⟨2, by decide⟩ (UInt256.ofNat 0x52), by rfl, by decide⟩,
   ⟨170, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def readLEPath : List Located :=
  [⟨55, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨56, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨57, .op .MLOAD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨58, .op (.Dup ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨59, .push ⟨1, by decide⟩ (UInt256.ofNat 3), by rfl, by decide⟩,
   ⟨60, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨61, .push ⟨1, by decide⟩ (UInt256.ofNat 24), by rfl, by decide⟩,
   ⟨62, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨63, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨64, .push ⟨1, by decide⟩ (UInt256.ofNat 2), by rfl, by decide⟩,
   ⟨65, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨66, .push ⟨1, by decide⟩ (UInt256.ofNat 16), by rfl, by decide⟩,
   ⟨67, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨68, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨69, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨70, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨71, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨72, .push ⟨1, by decide⟩ (UInt256.ofNat 8), by rfl, by decide⟩,
   ⟨73, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨74, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨75, .push ⟨0, by decide⟩ 0, by rfl, by decide⟩,
   ⟨76, .op .BYTE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨77, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨78, .op .OR, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨79, .op (.Swap ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨80, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨81, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨82, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨83, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨84, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

/-- Maximal prefix executable by the current generic stepper.  The next
instruction is `BYTE`, which is the one missing `runInstr` case. -/
def readLEPrefixPath : List Located := readLEPath.take 5

def setupXSetPath : List Located :=
  [⟨171, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨172, .op (.Dup ⟨2, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨173, .push ⟨2, by decide⟩ (UInt256.ofNat 0x27), by rfl, by decide⟩,
   ⟨174, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def xSetPath : List Located :=
  [⟨27, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨28, .push ⟨1, by decide⟩ (UInt256.ofNat 5), by rfl, by decide⟩,
   ⟨29, .op .SHL, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨30, .push ⟨2, by decide⟩ (UInt256.ofNat 672), by rfl, by decide⟩,
   ⟨31, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨32, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨33, .push ⟨4, by decide⟩ (UInt256.ofNat 4294967295), by rfl, by decide⟩,
   ⟨34, .op .AND, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨35, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨36, .op .MSTORE, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨37, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def incrementPath : List Located :=
  [⟨175, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨176, .push ⟨1, by decide⟩ (UInt256.ofNat 1), by rfl, by decide⟩,
   ⟨177, .op (.Dup ⟨1, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨178, .op .ADD, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨179, .op (.Swap ⟨0, by decide⟩), by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨180, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨181, .push ⟨2, by decide⟩ (UInt256.ofNat 0xd3), by rfl, by decide⟩,
   ⟨182, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

def exitPath : List Located :=
  [⟨183, .op .JUMPDEST, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨184, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨185, .op .POP, by rfl, wfOp (by decide) trivial rfl⟩,
   ⟨186, .op .JUMP, by rfl, wfOp (by decide) trivial rfl⟩]

@[simp] private theorem schedulePC (i : Nat) (hlo : 152 ≤ i) (hhi : i ≤ 186) :
    Artifact.submissionArtifact.instructionPC i =
      [0xd1, 0xd2, 0xd3, 0xd4, 0xd6, 0xd7, 0xd8, 0xd9,
       0xdc, 0xdd, 0xe0, 0xe3, 0xe4, 0xe5, 0xe7, 0xe8,
       0xe9, 0xea, 0xed, 0xee, 0xef, 0xf0, 0xf3, 0xf4,
       0xf5, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb, 0xfe, 0xff,
       0x100, 0x101, 0x102][i - 152]! := by
  interval_cases i <;> rfl

@[simp] private theorem readPC (i : Nat) (hlo : 55 ≤ i) (hhi : i ≤ 84) :
    Artifact.submissionArtifact.instructionPC i =
      [0x52, 0x53, 0x54, 0x55, 0x56, 0x58, 0x59, 0x5b,
       0x5c, 0x5d, 0x5f, 0x60, 0x62, 0x63, 0x64, 0x65,
       0x67, 0x68, 0x6a, 0x6b, 0x6c, 0x6d, 0x6e, 0x6f,
       0x70, 0x71, 0x72, 0x73, 0x74, 0x75][i - 55]! := by
  interval_cases i <;> rfl

@[simp] private theorem xSetPC (i : Nat) (hlo : 27 ≤ i) (hhi : i ≤ 39) :
    Artifact.submissionArtifact.instructionPC i =
      [39, 40, 42, 43, 46, 47, 48, 53, 54, 55, 56, 57, 58][i - 27]! := by
  interval_cases i <;> rfl

def loadOffsetWord (msgOff : UInt256) (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) + msgOff

def xSlotWord (i : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + UInt256.ofNat 0x2a0

def readLEWord (memory : ByteArray) (off : UInt256) : UInt256 :=
  let w := MachineState.readWord memory off.toNat
  UInt256.lor
    (UInt256.lor (UInt256.byteAt ⟨0⟩ w)
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 1) w)
        (UInt256.ofNat 8)))
    (UInt256.lor
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 2) w)
        (UInt256.ofNat 16))
      (UInt256.shiftLeft (UInt256.byteAt (UInt256.ofNat 3) w)
        (UInt256.ofNat 24)))

def scheduleEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 0xd1
           stack := [msgOff, returnDest] ++ rest }

def loopAt (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0xd3
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0xdd
           stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest }

def readEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0x52
           stack := [loadOffsetWord msgOff i, 0, UInt256.ofNat 0xee,
             UInt256.ofNat 0xf4, UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 0xee
           stack := [readLEWord s.memory (loadOffsetWord msgOff i),
             UInt256.ofNat 0xf4, UInt256.ofNat i, msgOff, returnDest] ++ rest
           activeWords := s.activeWordsAfterUInt256
             (loadOffsetWord msgOff i).toNat 32 }

def beforeFirstByte (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let off := loadOffsetWord msgOff i
  let w := MachineState.readWord s.memory off.toNat
  { s with
    pc := UInt256.ofNat 0x58
    stack := [UInt256.ofNat 3, w, w, off, 0, UInt256.ofNat 0xee,
      UInt256.ofNat 0xf4, UInt256.ofNat i, msgOff, returnDest] ++ rest
    activeWords := s.activeWordsAfterUInt256 off.toNat 32 }

def xSetEntry (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  { loaded with
    pc := UInt256.ofNat 0x27
    stack := [UInt256.ofNat i,
        readLEWord s.memory (loadOffsetWord msgOff i), UInt256.ofNat 0xf4,
        UInt256.ofNat i, msgOff, returnDest] ++ rest }

def afterStore (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  let loaded := afterRead s msgOff returnDest rest i
  let value := UInt256.land (readLEWord s.memory (loadOffsetWord msgOff i))
    (UInt256.ofNat 0xffffffff)
  { loaded with
    pc := UInt256.ofNat 0xf4
    stack := [UInt256.ofNat i, msgOff, returnDest] ++ rest
    memory := MachineState.writeBytes loaded.memory
      (Data.Bytes.natToBytesPadded value.toNat 32) (xSlotWord i).toNat
    activeWords := loaded.activeWordsAfterUInt256 (xSlotWord i).toNat 32 }

def afterIteration (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) : State :=
  { afterStore s msgOff returnDest rest i with
      pc := UInt256.ofNat 0xd3
      stack := [UInt256.ofNat (i + 1), msgOff, returnDest] ++ rest }

set_option linter.unusedSimpArgs false in
theorem run_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scheduleStartPath
      (scheduleEntry s msgOff returnDest rest) =
        some (loopAt s msgOff returnDest rest 0) := by
  have hc2 : rest.length + 2 < 1024 := by omega
  simp [scheduleStartPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scheduleEntry, loopAt, hc2, hrun]
  decide

set_option linter.unusedSimpArgs false in
theorem run_condition_continue (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1019) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s msgOff returnDest rest i) =
        some (afterCondition s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hiWord : (UInt256.ofNat i).toNat = i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat 16) =
      UInt256.ofNat 1 := by
    simp [UInt256.lt, hiWord, Challenge.EvmProof.Word.word_toNat_ofNat, hi]
  have hzero : UInt256.isZero (UInt256.ofNat 1) = 0 := by decide
  have hfalse : UInt256.isTrue (0 : UInt256) = false := by decide
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterCondition, hc3, hc4, hc5, hrun, hlt, hzero, hfalse]

set_option linter.unusedSimpArgs false in
theorem run_setupRead (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (_hi : i < 16)
    (hstack : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupReadPath
      (afterCondition s msgOff returnDest rest i) =
        some (readEntry s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 0x52 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 55 (by rfl)
  have hoff : msgOff + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 2) =
      loadOffsetWord msgOff i := by
    rw [loadOffsetWord]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  simp [setupReadPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterCondition, readEntry, hc3, hc4, hc5, hc6, hc7, hc8, hrun, hcode,
    hdest, hoff]
  decide

set_option linter.unusedSimpArgs false in
theorem run_readLEPrefix (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1014)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock readLEPrefixPath
      (readEntry s msgOff returnDest rest i) =
        some (beforeFirstByte s msgOff returnDest rest i) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  simp [readLEPrefixPath, readLEPath,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    readEntry, beforeFirstByte,
    hc7, hc8, hc9, hc10, hrun,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock readLEPath
      (readEntry s msgOff returnDest rest i) =
        some (afterRead s msgOff returnDest rest i) := by
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hc11 : rest.length + 11 < 1024 := by omega
  have hc12 : rest.length + 12 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 0xee = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 171 (by rfl)
  simp [readLEPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    readEntry, afterRead, readLEWord, List.exchange,
    hc6, hc7, hc8, hc9, hc10, hc11, hc12, hrun, hcode, hdest,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_setupXSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1017)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock setupXSetPath
      (afterRead s msgOff returnDest rest i) =
        some (xSetEntry s msgOff returnDest rest i) := by
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 0x27 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 27 (by rfl)
  simp [setupXSetPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterRead, xSetEntry, hc5, hc6, hc7, hrun, hcode, hdest]

set_option linter.unusedSimpArgs false in
theorem run_xSet (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (_hi : i < 16)
    (hstack : rest.length < 1015)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock xSetPath
      (xSetEntry s msgOff returnDest rest i) =
        some (afterStore s msgOff returnDest rest i) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hdest : Decode.isValidJumpDest submissionBytecode 0xf4 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 175 (by rfl)
  have hslot : UInt256.ofNat 0x2a0 +
        UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) = xSlotWord i := by
    rw [xSlotWord]
    exact Challenge.EvmProof.Word.word_add_comm _ _
  simp [xSetPath, Word.land_comm, List.exchange,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    xSetEntry, afterStore, afterRead, List.exchange,
    hc4, hc5, hc6, hc7, hc8, hc9, hrun, hcode, hdest, hslot,
    State.activeWordsAfterUInt256]

set_option linter.unusedSimpArgs false in
theorem run_increment (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock incrementPath
      (afterStore s msgOff returnDest rest i) =
        some (afterIteration s msgOff returnDest rest i) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hadd : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) :=
    Challenge.EvmProof.Word.ofNat_add_ofNat (by omega)
  have hdest : Decode.isValidJumpDest submissionBytecode 0xd3 = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 154 (by rfl)
  simp [incrementPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterStore, afterIteration, afterRead, List.exchange,
    hc3, hc4, hc5, hrun, hcode, hdest, hadd]

def gasSteps_readLEPrefix (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1014)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (readEntry s msgOff returnDest rest i)
      (beforeFirstByte s msgOff returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka readLEPrefixPath
  · exact hcode
  · exact hfork
  · exact run_readLEPrefix s msgOff returnDest rest i hstack hrun
  · exact hrun
  · exact hnp

def gasSteps_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (readEntry s msgOff returnDest rest i)
      (afterRead s msgOff returnDest rest i) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka readLEPath
  · exact hcode
  · exact hfork
  · exact run_readLE s msgOff returnDest rest i hstack hcode hrun
  · exact hrun
  · exact hnp

/-- One complete schedule iteration, conditional only on the `readLE32`
helper trace whose four `BYTE` instructions are not yet supported by the
generic executable stepper. -/
def gasSteps_iteration_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (i : Nat) (hi : i < 16)
    (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (gread : Challenge.EvmProof.GasSteps
      (readEntry s msgOff returnDest rest i)
      (afterRead s msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (loopAt s msgOff returnDest rest i)
      (afterIteration s msgOff returnDest rest i) := by
  have gCondition : Challenge.EvmProof.GasSteps
      (loopAt s msgOff returnDest rest i)
      (afterCondition s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka conditionPath
    · exact hcode
    · exact hfork
    · exact run_condition_continue s msgOff returnDest rest i hi (by omega) hrun
    · exact hrun
    · exact hnp
  have gSetupRead : Challenge.EvmProof.GasSteps
      (afterCondition s msgOff returnDest rest i)
      (readEntry s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka setupReadPath
    · exact hcode
    · exact hfork
    · exact run_setupRead s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gSetupXSet : Challenge.EvmProof.GasSteps
      (afterRead s msgOff returnDest rest i)
      (xSetEntry s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka setupXSetPath
    · exact hcode
    · exact hfork
    · exact run_setupXSet s msgOff returnDest rest i (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gXSet : Challenge.EvmProof.GasSteps
      (xSetEntry s msgOff returnDest rest i)
      (afterStore s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka xSetPath
    · exact hcode
    · exact hfork
    · exact run_xSet s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  have gIncrement : Challenge.EvmProof.GasSteps
      (afterStore s msgOff returnDest rest i)
      (afterIteration s msgOff returnDest rest i) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka incrementPath
    · exact hcode
    · exact hfork
    · exact run_increment s msgOff returnDest rest i hi (by omega) hcode hrun
    · exact hrun
    · exact hnp
  exact gCondition.trans <| gSetupRead.trans <| gread.trans <|
    gSetupXSet.trans <| gXSet.trans gIncrement

def loopState (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : Nat → State
  | 0 => loopAt s msgOff returnDest rest 0
  | i + 1 => afterIteration (loopState s msgOff returnDest rest i)
      msgOff returnDest rest i

@[simp] theorem loopState_executionEnv (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopState_halt (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    (loopState s msgOff returnDest rest i).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih =>
      simp [loopState, afterIteration, afterStore, afterRead, ih]

@[simp] theorem loopAt_loopState (s : State)
    (msgOff returnDest : UInt256) (rest : List UInt256) (i : Nat) :
    loopAt (loopState s msgOff returnDest rest i) msgOff returnDest rest i =
      loopState s msgOff returnDest rest i := by
  cases i <;> rfl

def gasSteps_loop_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hread : ∀ (i : Nat), i < 16 →
      Challenge.EvmProof.GasSteps
        (readEntry (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)
        (afterRead (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (loopState s msgOff returnDest rest 0)
      (loopState s msgOff returnDest rest 16) := by
  apply Challenge.EvmProof.GasSteps.iterateBounded (count := 16)
  intro i hi
  let q := loopState s msgOff returnDest rest i
  have hqcode : q.executionEnv.code = submissionBytecode := by
    simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by
    simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  let gone := gasSteps_iteration_of_readLE q msgOff returnDest rest i hi hstack
    hqcode hqfork hqrun hqnp (by simpa [q] using hread i hi)
  exact Challenge.EvmProof.GasSteps.cast gone (by simp [q]) (by
    simp [q, loopState])

def afterExitCondition (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with
    pc := UInt256.ofNat 0xff
    stack := [UInt256.ofNat 16, msgOff, returnDest] ++ rest }

def scheduleReturned (s : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := returnDest, stack := rest }

set_option linter.unusedSimpArgs false in
theorem run_condition_exit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1019)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock conditionPath
      (loopAt s msgOff returnDest rest 16) =
        some (afterExitCondition s msgOff returnDest rest) := by
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat 16) (UInt256.ofNat 16) = 0 := by decide
  have hzero : UInt256.isZero (0 : UInt256) = UInt256.ofNat 1 := by decide
  have htrue : UInt256.isTrue (UInt256.ofNat 1) = true := by decide
  have hdest : Decode.isValidJumpDest submissionBytecode 0xff = true :=
    Artifact.submissionArtifact.isValidJumpDest_index 183 (by rfl)
  simp [conditionPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    loopAt, afterExitCondition, hc3, hc4, hc5, hrun, hcode,
    hlt, hzero, htrue, hdest]

set_option linter.unusedSimpArgs false in
theorem run_exit (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock exitPath
      (afterExitCondition s msgOff returnDest rest) =
        some (scheduleReturned s returnDest rest) := by
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  simp [exitPath, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    afterExitCondition, scheduleReturned, hc1, hc2, hc3, hrun, hcode, hreturn]

def gasSteps_scheduleStart (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1021)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (loopState s msgOff returnDest rest 0) := by
  apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka scheduleStartPath
  · exact hcode
  · exact hfork
  · exact run_scheduleStart s msgOff returnDest rest hstack hrun
  · exact hrun
  · exact hnp

/-- Complete sixteen-word schedule trace factored over a `readLE32` helper
certificate. -/
def gasSteps_schedule_of_readLE (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true)
    (hread : ∀ (i : Nat), i < 16 →
      Challenge.EvmProof.GasSteps
        (readEntry (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)
        (afterRead (loopState s msgOff returnDest rest i)
          msgOff returnDest rest i)) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (scheduleReturned (loopState s msgOff returnDest rest 16)
        returnDest rest) := by
  have gstart := gasSteps_scheduleStart s msgOff returnDest rest (by omega)
    hcode hfork hrun hnp
  have gloop := gasSteps_loop_of_readLE s msgOff returnDest rest hstack
    hcode hfork hrun hnp hread
  let q := loopState s msgOff returnDest rest 16
  have hqcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  have gcondition : Challenge.EvmProof.GasSteps
      (loopAt q msgOff returnDest rest 16)
      (afterExitCondition q msgOff returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka conditionPath
    · exact hqcode
    · exact hqfork
    · exact run_condition_exit q msgOff returnDest rest (by omega) hqcode hqrun
    · exact hqrun
    · exact hqnp
  have gcondition' : Challenge.EvmProof.GasSteps q
      (afterExitCondition q msgOff returnDest rest) :=
    Challenge.EvmProof.GasSteps.cast gcondition (by simp [q]) rfl
  have gexit : Challenge.EvmProof.GasSteps
      (afterExitCondition q msgOff returnDest rest)
      (scheduleReturned q returnDest rest) := by
    apply Challenge.EvmProof.Stepper.runLocatedBlock_sound
      Artifact.submissionArtifact .Osaka exitPath
    · exact hqcode
    · exact hqfork
    · exact run_exit q msgOff returnDest rest (by omega) hqcode hqrun hreturn
    · exact hqrun
    · exact hqnp
  exact gstart.trans <| gloop.trans <| gcondition'.trans gexit

/-- Unconditional direct trace of the complete compiled `schedule(msgOff)`
function, including all four `BYTE` instructions in each `readLE32` call. -/
def gasSteps_schedule (s : State) (msgOff returnDest : UInt256)
    (rest : List UInt256) (hstack : rest.length < 1012)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false)
    (hreturn : Decode.isValidJumpDest submissionBytecode returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps (scheduleEntry s msgOff returnDest rest)
      (scheduleReturned (loopState s msgOff returnDest rest 16)
        returnDest rest) := by
  apply gasSteps_schedule_of_readLE s msgOff returnDest rest hstack
    hcode hfork hrun hnp hreturn
  intro i hi
  let q := loopState s msgOff returnDest rest i
  have hqcode : q.executionEnv.code = submissionBytecode := by simpa [q] using hcode
  have hqfork : q.fork = .Osaka := by simpa [q, State.fork] using hfork
  have hqrun : q.halt = .Running := by simpa [q] using hrun
  have hqnp : Precompile.isPrecompileWithConfig q.executionEnv.precompileConfig q.executionEnv.fork
      q.executionEnv.codeAddr = false := by simpa [q] using hnp
  simpa [q] using gasSteps_readLE q msgOff returnDest rest i hstack
    hqcode hqfork hqrun hqnp

end Challenge.Ripemd160.Submission.Proofs.Bytecode.Schedule
