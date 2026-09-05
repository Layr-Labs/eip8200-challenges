import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock
import Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory
import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp
open Challenge.Modexp.Submission.Proofs.Limbs
open Challenge.Modexp.Submission.Proofs.Bytecode
open Challenge.EvmProof

private def wfOp {op : Operation}
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op)
    (hplain : YulEvmCompiler.plainOp op)
    (havailable : op.availableInFork .Osaka = true) :
    Stepper.WellFormed .Osaka (.op op) :=
  ⟨hopcode, hplain, havailable⟩

private def opAt (index : Nat) (op : Operation)
    (hget : Artifact.submissionInstructions[index]? = some (.op op) := by rfl)
    (hopcode : Decode.opcodeOf (Instr.opByte op) = some op := by decide)
    (hplain : YulEvmCompiler.plainOp op := by trivial)
    (havailable : op.availableInFork .Osaka = true := by rfl) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .op op, hget, wfOp hopcode hplain havailable⟩

private def pushAt (index : Nat) (width : Fin 33) (value : UInt256)
    (hget : Artifact.submissionInstructions[index]? = some (.push width value) := by rfl)
    (hwf : Stepper.WellFormed .Osaka (.push width value) := by decide) :
    Stepper.Located Artifact.submissionArtifact .Osaka :=
  ⟨index, .push width value, hget, hwf⟩

def scratch : UInt256 := UInt256.ofNat 0x2400

def candidate : Nat := 0x1400

def kClear : UInt256 := UInt256.ofNat 1641

def kLoop : UInt256 := UInt256.ofNat 1646

def kFirst : UInt256 := UInt256.ofNat 1676

def kSecond : UInt256 := UInt256.ofNat 1697

def kShift : UInt256 := UInt256.ofNat 1715

def kFinish : UInt256 := UInt256.ofNat 1736

def kReduce : UInt256 := UInt256.ofNat 1763

def kDone : UInt256 := UInt256.ofNat 1777

def frame (i : Nat) (a b out modulus n : UInt256) (np ret : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat i, a, b, out, modulus, n, np, ret] ++ rest

def entry (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1625
           stack := [a, b, out, modulus, n, np, ret] ++ rest }

def loop (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1646
           stack := frame i a b out modulus n np ret rest }

def cleanReturned (s : State) (_a _b _out _modulus _n _np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest }

theorem entry_frame (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) :
    (entry s a b out modulus n np ret rest).stack =
      [a, b, out, modulus, n, np, ret] ++ rest := rfl

theorem frame_length (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) :
    (frame i a b out modulus n np ret rest).length = rest.length + 8 := by
  simp [frame]

def clearCall (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 19
           stack := [scratch, n + 2, kClear] ++ frame 0 a b out modulus n np ret rest }

def firstCall (s : State) (i : Nat) (a b out modulus n np ret digit : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1503
           stack := [scratch, b, digit, n, kFirst] ++ frame i a b out modulus n np ret rest }

def secondCall (s : State) (i : Nat) (a b out modulus n np ret q : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1503
           stack := [scratch, modulus, q, n, kSecond] ++ frame i a b out modulus n np ret rest }

def shiftCall (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 58
           stack := [scratch, scratch + 32, n + 1, kShift] ++
             frame i a b out modulus n np ret rest }

def reduceCall (s : State) (i : Nat) (a b out modulus n np ret high : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 174
           stack := [0, 0, high, 0, scratch, 0, 0, modulus, n, kReduce] ++
             frame i a b out modulus n np ret rest }

def outputCall (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 58
           stack := [out, scratch, n, kDone] ++ frame i a b out modulus n np ret rest }

def coreReturned (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  cleanReturned s a b out modulus n np ret rest

def clearState (s : State) (n : Nat) : State :=
  { s with
    memory := BigHelpers.clearMemory s.memory scratch (n + 2)
    activeWords := BigHelpers.clearWords s.activeWords scratch (n + 2) }

def touch (active : UInt256) (address : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter active.toNat address 32)

def loadState (s : State) (address : Nat) : State :=
  { s with activeWords := touch s.activeWords address }

private theorem wordAddress (p : UInt256) (j : Nat)
    (hfit : p.toNat + 32 * j < 2 ^ 256) :
    p + UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) =
      UInt256.ofNat (p.toNat + 32 * j) := by
  have hj : j < 2 ^ 256 := by omega
  have hm : j * 2 ^ 5 < 2 ^ 256 := by norm_num; omega
  rw [Word.shiftLeft_ofNat hj (by decide) hm]
  apply Word.word_ext
  simp [Word.word_toNat_add, Nat.mul_comm]

def bodyEntry (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { loop s i a b out modulus n np ret rest with pc := UInt256.ofNat 1655 }

def finish (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { loop s n.toNat a b out modulus n np ret rest with pc := UInt256.ofNat 1736 }

def firstEntry (s : State) (i : Nat) (a b out modulus n np ret digit : UInt256)
    (rest : List UInt256) : State :=
  MontgomeryWordBlock.entry (loadState s (a.toNat + 32 * i)) scratch b digit n.toNat
    kFirst (frame i a b out modulus n np ret rest)

def secondEntry (s : State) (i : Nat) (a b out modulus n np ret q : UInt256)
    (rest : List UInt256) : State :=
  MontgomeryWordBlock.entry (loadState s scratch.toNat) scratch modulus q n.toNat kSecond
    (frame i a b out modulus n np ret rest)

def shiftEntry (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyEntry s scratch (scratch + 32) (n.toNat + 1) kShift
    (frame i a b out modulus n np ret rest)

def zeroState (s : State) (address : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) address
    activeWords := touch s.activeWords address }

def reduceEntry (s : State) (i : Nat) (a b out modulus n np ret high : UInt256)
    (rest : List UInt256) : State :=
  MontgomeryReduceBlock.reduceEntry (loadState s (scratch.toNat + 32 * i)) scratch modulus high
    n.toNat kReduce (frame i a b out modulus n np ret rest)

def outputEntry (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyEntry s out scratch n.toNat kDone
    (frame i a b out modulus n np ret rest)

def entryClearPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1227 .JUMPDEST, pushAt 1228 0 0, pushAt 1229 2 1641,
   opAt 1230 (.Dup ⟨6, by decide⟩), pushAt 1231 1 2, opAt 1232 .ADD,
   pushAt 1233 2 9216, pushAt 1234 2 19, opAt 1235 .JUMP]

def clearReturnPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1236 .JUMPDEST, pushAt 1237 2 1646, opAt 1238 .JUMP]

def guardPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1239 .JUMPDEST, opAt 1240 (.Dup ⟨5, by decide⟩),
   opAt 1241 (.Dup ⟨1, by decide⟩), opAt 1242 .LT, opAt 1243 .ISZERO,
   pushAt 1244 2 1736, opAt 1245 .JUMPI]

def firstCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1246 (.Dup ⟨0, by decide⟩), pushAt 1247 1 5, opAt 1248 .SHL,
   opAt 1249 (.Dup ⟨2, by decide⟩), opAt 1250 .ADD, opAt 1251 .MLOAD,
   pushAt 1252 2 1676, opAt 1253 (.Dup ⟨7, by decide⟩),
   opAt 1254 (.Swap ⟨0, by decide⟩), opAt 1255 (.Swap ⟨1, by decide⟩),
   opAt 1256 (.Dup ⟨5, by decide⟩), pushAt 1257 2 9216,
   pushAt 1258 2 1503, opAt 1259 .JUMP]

def secondCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1260 .JUMPDEST, pushAt 1261 2 9216, opAt 1262 .MLOAD,
   opAt 1263 (.Dup ⟨7, by decide⟩), opAt 1264 .MUL,
   pushAt 1265 2 1697, opAt 1266 (.Dup ⟨7, by decide⟩),
   opAt 1267 (.Swap ⟨0, by decide⟩), opAt 1268 (.Swap ⟨1, by decide⟩),
   opAt 1269 (.Dup ⟨7, by decide⟩), pushAt 1270 2 9216,
   pushAt 1271 2 1503, opAt 1272 .JUMP]

def shiftCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1273 .JUMPDEST, pushAt 1274 2 1715, opAt 1275 (.Dup ⟨6, by decide⟩),
   pushAt 1276 1 1, opAt 1277 .ADD, pushAt 1278 2 9248,
   pushAt 1279 2 9216, pushAt 1280 2 58, opAt 1281 .JUMP]

def shiftZeroPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1282 .JUMPDEST, pushAt 1283 0 0, opAt 1284 (.Dup ⟨6, by decide⟩),
   pushAt 1285 1 1, opAt 1286 .ADD, pushAt 1287 1 5, opAt 1288 .SHL,
   pushAt 1289 2 9216, opAt 1290 .ADD, opAt 1291 .MSTORE,
   pushAt 1292 1 1, opAt 1293 .ADD, pushAt 1294 2 1646, opAt 1295 .JUMP]

def reduceCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1296 .JUMPDEST, pushAt 1297 2 1763, opAt 1298 (.Dup ⟨6, by decide⟩),
   opAt 1299 (.Dup ⟨6, by decide⟩), pushAt 1300 0 0, pushAt 1301 0 0,
   pushAt 1302 2 9216, pushAt 1303 0 0, opAt 1304 (.Dup ⟨5, by decide⟩),
   pushAt 1305 1 5, opAt 1306 .SHL, pushAt 1307 2 9216, opAt 1308 .ADD,
   opAt 1309 .MLOAD, pushAt 1310 0 0, pushAt 1311 0 0,
   pushAt 1312 2 174, opAt 1313 .JUMP]

def outputCallPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1314 .JUMPDEST, pushAt 1315 2 1777, opAt 1316 (.Dup ⟨6, by decide⟩),
   opAt 1317 (.Dup ⟨5, by decide⟩), pushAt 1318 2 9216,
   opAt 1319 (.Swap ⟨0, by decide⟩), pushAt 1320 2 58, opAt 1321 .JUMP]

def cleanupPath : List (Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1322 .JUMPDEST, opAt 1323 .POP, opAt 1324 .POP, opAt 1325 .POP,
   opAt 1326 .POP, opAt 1327 .POP, opAt 1328 .POP, opAt 1329 .POP,
   opAt 1330 .JUMP]

@[simp] private theorem driverPCs (i : Nat) (hi : 1227 ≤ i) (hii : i ≤ 1330) :
    Artifact.submissionArtifact.instructionPC i =
      [1625,1626,1627,1630,1631,1633,1634,1637,1640,1641,1642,1645,
       1646,1647,1648,1649,1650,1651,1654,1655,1656,1658,1659,1660,
       1661,1662,1665,1666,1667,1668,1669,1672,1675,1676,1677,1680,
       1681,1682,1683,1686,1687,1688,1689,1690,1693,1696,1697,1698,
       1701,1702,1704,1705,1708,1711,1714,1715,1716,1717,1718,1720,
       1721,1723,1724,1727,1728,1729,1731,1732,1735,1736,1737,1740,
       1741,1742,1743,1744,1747,1748,1749,1751,1752,1755,1756,1757,
       1758,1759,1762,1763,1764,1767,1768,1769,1772,1773,1776,1777,
       1778,1779,1780,1781,1782,1783,1784,1785][i - 1227]! := by
  interval_cases i <;> decide

theorem memoryCarry_wordProgress (memory : ByteArray) (x t : Nat)
    (word : UInt256) (j : Nat) :
    Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock.memoryCarry memory x t word j =
      Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.wordProgress memory x t word 0 j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock.memoryCarry, Challenge.Modexp.Submission.Proofs.Montgomery.WordLoop.wordProgress, ih]

theorem clearMemory_clearScratch (memory : ByteArray) (t count : Nat)
    (hfit : t + 32 * count < Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B) :
    BigHelpers.clearMemory memory (UInt256.ofNat t) count =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.clearProgress memory t count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : t + 32 * count < 2 ^ 256 := by
        change t + 32 * (count + 1) < 2 ^ 256 at hfit
        omega
      have hprevB : t + 32 * count < Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B := by
        simpa [Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B, radix] using hprev
      simp only [BigHelpers.clearMemory, Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.clearProgress]
      rw [ih hprevB, BigHelpers.clearOffset_toNat t count hprev]

theorem copyMemory_shiftProgress (memory : ByteArray) (t count : Nat)
    (hfit : t + 32 * (count + 1) < Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B) :
    BigHelpers.copyMemory memory (UInt256.ofNat t) (UInt256.ofNat (t + 32)) count =
      Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftProgress memory t count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      have hprev : t + 32 * (count + 1) < 2 ^ 256 := by
        change t + 32 * (count + 2) < 2 ^ 256 at hfit
        omega
      have hsrc : t + 32 + 32 * count < 2 ^ 256 := by omega
      have hdst : t + 32 * count < 2 ^ 256 := by omega
      have hprevB : t + 32 * (count + 1) < Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B := by
        simpa [Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B, radix] using hprev
      simp only [BigHelpers.copyMemory, Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftProgress]
      rw [ih hprevB, BigHelpers.clearOffset_toNat (t + 32) count hsrc,
        BigHelpers.clearOffset_toNat t count hdst]
      have haddr : t + 32 + 32 * count = t + 32 * (count + 1) := by omega
      rw [haddr]

theorem copyMemory_zero_shiftDown (memory : ByteArray) (t n : Nat)
    (hfit : t + 32 * (n + 2) < Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.B) :
    MachineState.writeBytes
        (BigHelpers.copyMemory memory (UInt256.ofNat t) (UInt256.ofNat (t + 32)) (n + 1))
        (Data.Bytes.natToBytesPadded 0 32) (t + 32 * (n + 1)) =
      Challenge.Modexp.Submission.Proofs.Montgomery.ShiftMemory.shiftDown memory t n := by
  rw [copyMemory_shiftProgress memory t (n + 1) (by omega)]
  rfl

def coreStep := Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreStep

def coreProgress := Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreProgress

theorem coreStep_wordProgress (memory : ByteArray) (a b modulus t n i : Nat)
    (np : UInt256) :
    coreStep memory a b modulus t n i np =
      Challenge.Modexp.Submission.Proofs.Montgomery.CoreMemory.coreStep memory a b modulus t n i np := rfl

theorem frame_clean (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) :
    { cleanReturned s a b out modulus n np ret rest with
      pc := s.pc
      stack := s.stack
      memory := s.memory
      activeWords := s.activeWords } = s := by
  cases s
  rfl

set_option linter.unusedSimpArgs false in
theorem run_entryClear (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock entryClearPath (entry s a b out modulus n np ret rest) =
      some (clearCall s a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hjump : Decode.isValidJumpDest submissionBytecode 19 = true := by
    have hpc : Artifact.instructionPC 15 = 19 := by decide
    simpa [hpc] using (Artifact.isValidJumpDest_index 15 (by rfl))
  have hto : (19 : UInt256).toNat = 19 := by decide
  have hsum : (2 : UInt256) + n = n + 2 := Word.word_add_comm _ _
  simp [entryClearPath, opAt, pushAt, wfOp, entry, clearCall, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, Nat.add_assoc, cap, hcode, hrun, hjump, hto, hsum,
    scratch]
  decide

set_option linter.unusedSimpArgs false in
theorem run_clearReturn (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hn : n.toNat ≤ 32)
    (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock clearReturnPath
        (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
          (frame 0 a b out modulus n np ret rest)) =
      some (loop (clearState s n.toNat) 0 a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hcount : n.toNat + 2 < 2 ^ 256 := by omega
  have hjump : Decode.isValidJumpDest submissionBytecode 1646 = true := by
    have h := Artifact.isValidJumpDest_index 1239 (by rfl)
    have hpc : Artifact.instructionPC 1239 = 1646 := by decide
    simpa [hpc] using h
  have hc1 : rest.length + 1 < 1024 := by omega
  have hc2 : rest.length + 2 < 1024 := by omega
  have hc3 : rest.length + 3 < 1024 := by omega
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hto : (1646 : UInt256).toNat = 1646 := by decide
  simp [clearReturnPath, opAt, pushAt, wfOp, BigHelpers.clearReturned,
    clearState, loop, frame, BigHelpers.clearWords, BigHelpers.clearMemory,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, cap, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9,
    hcode, hrun, hcount, hjump, hto, kClear, kLoop, scratch]
  decide

set_option linter.unusedSimpArgs false in
theorem run_guard (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hi : i < n.toNat) (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (loop s i a b out modulus n np ret rest) =
      some (bodyEntry s i a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hn256 : n.toNat < 2 ^ 256 := n.val.isLt
  have hi256 : i < 2 ^ 256 := by omega
  have hltNat : (UInt256.lt (UInt256.ofNat i) n).toNat = 1 := by
    rw [Word.word_toNat_lt, Word.word_toNat_ofNat, Nat.mod_eq_of_lt hi256]
    simp [hi]
  have hlt : UInt256.lt (UInt256.ofNat i) n = UInt256.ofNat 1 := by
    apply Word.word_ext
    rw [hltNat, Word.word_toNat_ofNat]
    decide
  have hc : ¬ UInt256.isTrue (UInt256.isZero
      (UInt256.lt (UInt256.ofNat i) n)) := by
    rw [hlt]
    decide
  have honeFalse : ¬ UInt256.isTrue (UInt256.isZero (UInt256.ofNat 1)) := by
    decide
  simp [guardPath, opAt, pushAt, wfOp, bodyEntry, loop, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, Nat.add_assoc, cap, hrun, hc, honeFalse, hlt]

set_option linter.unusedSimpArgs false in
theorem run_guard_finish (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock guardPath (loop s n.toNat a b out modulus n np ret rest) =
      some (finish s a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hn256 : n.toNat < 2 ^ 256 := n.val.isLt
  have hzero : UInt256.lt n n = UInt256.ofNat 0 := by
    simp [UInt256.lt, Word.word_toNat_ofNat, Nat.mod_eq_of_lt, hn256]
  have hnword : UInt256.ofNat n.toNat = n :=
    (Word.word_eq_ofNat_toNat n).symm
  have hzero' : UInt256.lt (UInt256.ofNat n.toNat) n = UInt256.ofNat 0 := by
    rw [hnword]
    exact hzero
  have hc : UInt256.isTrue (UInt256.isZero
      (UInt256.lt (UInt256.ofNat n.toNat) n)) := by
    rw [hzero']
    decide
  have hzeroBool : UInt256.isTrue (UInt256.isZero (UInt256.ofNat 0)) := by
    decide
  have hpc : Artifact.instructionPC 1296 = 1736 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 1736 = true := by
    simpa [hpc] using (Artifact.isValidJumpDest_index 1296 (by rfl))
  have hto : (1736 : UInt256).toNat = 1736 := by decide
  have hpcWord : (1736 : UInt256) = UInt256.ofNat 1736 := by decide
  simp [guardPath, opAt, pushAt, wfOp, finish, loop, frame,
    Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
    Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt, Nat.add_assoc, cap, hcode, hrun, hc, hzero, hzero',
    hzeroBool, hjump, hto, hpcWord]

set_option linter.unusedSimpArgs false in
theorem run_firstCall (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (digit : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (haddr : a.toNat + 32 * i < 2 ^ 256)
    (hdigit : digit = MachineState.readWord s.memory
      (a.toNat + 32 * i))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock firstCallPath
        (bodyEntry s i a b out modulus n np ret rest) =
      some (firstEntry (bodyEntry s i a b out modulus n np ret rest)
        i a b out modulus n np ret digit rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hword := wordAddress a i haddr
  have hi256 : i < 2 ^ 256 := by omega
  have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
      UInt256.ofNat (i * 2 ^ 5) := by
    apply Word.shiftLeft_ofNat hi256 (by norm_num)
    omega
  have haddrNat :
      (a + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat =
        a.toNat + 32 * i := by
    rw [hword, Word.word_toNat_ofNat, Nat.mod_eq_of_lt haddr]
  have haddrNat' :
      (a.toNat + (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat) %
          2 ^ 256 = a.toNat + 32 * i := by
    simpa only [Word.word_toNat_add] using haddrNat
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have haddrNat'' :
      (a.toNat + (UInt256.shiftLeft (UInt256.ofNat i) (5 : UInt256)).toNat) %
          2 ^ 256 = a.toNat + 32 * i := by
    simpa only [hfive] using haddrNat'
  have hactive :
      MachineState.activeWordsAfter s.activeWords.toNat
          ((a.toNat + (UInt256.shiftLeft (UInt256.ofNat i) (5 : UInt256)).toNat) %
            2 ^ 256) 32 =
        MachineState.activeWordsAfter s.activeWords.toNat (a.toNat + 32 * i) 32 := by
    rw [haddrNat'']
  have hread :
      MachineState.readWord s.memory
          ((a.toNat + (UInt256.shiftLeft (UInt256.ofNat i) (5 : UInt256)).toNat) %
            2 ^ 256) =
        MachineState.readWord s.memory (a.toNat + 32 * i) := by
    rw [haddrNat'']
  norm_num at hactive hread
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hamod := Nat.mod_eq_of_lt haddr
  have hjump : Decode.isValidJumpDest submissionBytecode 1503 = true := by
    have hpc : Artifact.instructionPC 1120 = 1503 := by decide
    simpa [hpc] using (Artifact.isValidJumpDest_index 1120 (by rfl))
  have hto : (1503 : UInt256).toNat = 1503 := by decide
  have hpcWord : (1503 : UInt256) = UInt256.ofNat 1503 := by decide
  have hscratch : (9216 : UInt256) = UInt256.ofNat 9216 := by decide
  have hfirstWord : (1676 : UInt256) = UInt256.ofNat 1676 := by decide
  simp (config := { maxSteps := 400000 })
    [firstCallPath, opAt, pushAt, wfOp, bodyEntry, firstEntry, loadState,
     MontgomeryWordBlock.entry,
     loop, frame, touch, Stepper.runLocatedBlock, Stepper.runLocated,
     Stepper.runInstr, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap, hrun, hcode,
     State.activeWordsAfterUInt256, List.exchange, hword, hshift, haddrNat,
     haddrNat', haddrNat'', hactive, hread, hamod, hdigit, hnword, hjump,
     hto, hpcWord, hscratch, hfirstWord, scratch, kFirst]

def gasSteps_entryClear (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (entry s a b out modulus n np ret rest)
      (clearCall s a b out modulus n np ret rest) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka entryClearPath
    (by simpa [entry, Artifact.submissionArtifact] using hcode)
    (by simpa [entry, State.fork] using hfork)
    (run_entryClear s a b out modulus n np ret rest hcap hcode hrun)
    (by simpa [entry] using hrun)
    (by simpa [entry, State.fork] using hnp)

def gasSteps_clearReturn (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hn : n.toNat ≤ 32)
    (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps
        (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
          (frame 0 a b out modulus n np ret rest))
      (loop (clearState s n.toNat) 0 a b out modulus n np ret rest) := by
  have hc :
      (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
        (frame 0 a b out modulus n np ret rest)).executionEnv.code =
        submissionBytecode := by
    simpa [BigHelpers.clearReturned] using hcode
  have hf :
      (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
        (frame 0 a b out modulus n np ret rest)).fork = .Osaka := by
    simpa [BigHelpers.clearReturned, State.fork] using hfork
  have hr :
      (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
        (frame 0 a b out modulus n np ret rest)).halt = .Running := by
    simpa [BigHelpers.clearReturned] using hrun
  have hp :
      Precompile.isPrecompileWithConfig
          (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
            (frame 0 a b out modulus n np ret rest)).executionEnv.precompileConfig
          (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
            (frame 0 a b out modulus n np ret rest)).executionEnv.fork
          (BigHelpers.clearReturned s scratch (n.toNat + 2) kClear
            (frame 0 a b out modulus n np ret rest)).executionEnv.codeAddr = false := by
    simpa [BigHelpers.clearReturned, State.fork] using hnp
  exact Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka clearReturnPath
    hc hf (run_clearReturn s a b out modulus n np ret rest hn hcap hcode hrun) hr hp

def gasSteps_guard (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hi : i < n.toNat)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loop s i a b out modulus n np ret rest)
      (bodyEntry s i a b out modulus n np ret rest) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    (by simpa [loop, Artifact.submissionArtifact] using hcode)
    (by simpa [loop, State.fork] using hfork)
    (run_guard s i a b out modulus n np ret rest hcap hi hrun)
    (by simpa [loop] using hrun)
    (by simpa [loop, State.fork] using hnp)

def gasSteps_guard_finish (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (loop s n.toNat a b out modulus n np ret rest)
      (finish s a b out modulus n np ret rest) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka guardPath
    (by simpa [loop, Artifact.submissionArtifact] using hcode)
    (by simpa [loop, State.fork] using hfork)
    (run_guard_finish s a b out modulus n np ret rest hcap hcode hrun)
    (by simpa [loop] using hrun)
    (by simpa [loop, State.fork] using hnp)

def gasSteps_firstCall (s : State) (i : Nat)
    (a b out modulus n np ret digit : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (haddr : a.toNat + 32 * i < 2 ^ 256)
    (hdigit : digit = MachineState.readWord s.memory (a.toNat + 32 * i))
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    GasSteps (bodyEntry s i a b out modulus n np ret rest)
      (firstEntry (bodyEntry s i a b out modulus n np ret rest)
        i a b out modulus n np ret digit rest) :=
  Stepper.runLocatedBlock_sound Artifact.submissionArtifact .Osaka firstCallPath
    (by simpa [bodyEntry, loop, Artifact.submissionArtifact] using hcode)
    (by simpa [bodyEntry, loop, State.fork] using hfork)
    (run_firstCall s i a b out modulus n np ret digit rest hcap haddr hdigit hcode hrun)
    (by simpa [bodyEntry, loop] using hrun)
    (by simpa [bodyEntry, loop, State.fork] using hnp)

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCoreDriver
