import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryWordBlock
import Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryReduceBlock

set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

namespace Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths

open EvmSemantics EvmSemantics.EVM YulEvmCompiler
open Challenge.Modexp
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

def loop (s : State) (i : Nat) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1646
           stack := frame i a b out modulus n np ret rest }

def loadState (s : State) (address : Nat) : State :=
  { s with
    activeWords := UInt256.ofNat
      (MachineState.activeWordsAfter s.activeWords.toNat address 32) }

def touch (active : UInt256) (address : Nat) : UInt256 :=
  UInt256.ofNat (MachineState.activeWordsAfter active.toNat address 32)

def secondEntry (s : State) (i : Nat)
    (a b out modulus n np ret q : UInt256) (rest : List UInt256) : State :=
  MontgomeryWordBlock.entry (loadState s scratch.toNat)
    scratch modulus q n.toNat kSecond
    (frame i a b out modulus n np ret rest)

def shiftEntry (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  BigHelpers.copyEntry s scratch (scratch + 32) (n.toNat + 1) kShift
    (frame i a b out modulus n np ret rest)

def zeroState (s : State) (address : Nat) : State :=
  { s with
    memory := MachineState.writeBytes s.memory
      (Data.Bytes.natToBytesPadded 0 32) address
    activeWords := touch s.activeWords address }

def shiftZeroState (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256) (rest : List UInt256) : State :=
  loop (zeroState s (scratch.toNat + 32 * (n.toNat + 1)))
    (i + 1) a b out modulus n np ret rest

def reduceEntry (s : State) (a b out modulus n np ret high : UInt256)
    (rest : List UInt256) : State :=
  MontgomeryReduceBlock.reduceEntry
    (loadState s (scratch.toNat + 32 * n.toNat))
    scratch modulus high n.toNat kReduce
    (frame n.toNat a b out modulus n np ret rest)

def outputEntry (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.copyEntry s out scratch n.toNat kDone
    (frame n.toNat a b out modulus n np ret rest)

def cleanReturned (s : State) (_a _b _out _modulus _n _np ret : UInt256)
    (rest : List UInt256) : State :=
  { s with pc := ret
           stack := rest }

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

@[simp] private theorem corePCs (i : Nat) (hi : 1260 ≤ i) (hii : i ≤ 1330) :
    Artifact.submissionArtifact.instructionPC i =
      [1676,1677,1680,1681,1682,1683,1686,1687,1688,1689,1690,1693,
       1696,1697,1698,1701,1702,1704,1705,1708,1711,1714,1715,1716,
       1717,1718,1720,1721,1723,1724,1727,1728,1729,1731,1732,1735,
       1736,1737,1740,1741,1742,1743,1744,1747,1748,1749,1751,1752,
       1755,1756,1757,1758,1759,1762,1763,1764,1767,1768,1769,1772,
       1773,1776,1777,1778,1779,1780,1781,1782,1783,1784,1785][i - 1260]! := by
  interval_cases i <;> decide

private theorem wordAddress (p : UInt256) (j : Nat)
    (hfit : p.toNat + 32 * j < 2 ^ 256) :
    p + UInt256.shiftLeft (UInt256.ofNat j) (UInt256.ofNat 5) =
      UInt256.ofNat (p.toNat + 32 * j) := by
  have hj : j < 2 ^ 256 := by omega
  have hm : j * 2 ^ 5 < 2 ^ 256 := by norm_num; omega
  rw [Word.shiftLeft_ofNat hj (by decide) hm]
  apply Word.word_ext
  simp [Word.word_toNat_add, Nat.mul_comm]

@[simp] private theorem jump1503 :
    Decode.isValidJumpDest submissionBytecode 1503 = true := by
  have hpc : Artifact.instructionPC 1120 = 1503 := by decide
  simpa [hpc] using (Artifact.isValidJumpDest_index 1120 (by rfl))

@[simp] private theorem jump58 :
    Decode.isValidJumpDest submissionBytecode 58 = true := by
  have hpc : Artifact.instructionPC 46 = 58 := by decide
  have h := Artifact.isValidJumpDest_index 46 (by rfl)
  rw [hpc] at h
  exact h

@[simp] private theorem jump174 :
    Decode.isValidJumpDest submissionBytecode 174 = true := by
  have hpc : Artifact.instructionPC 147 = 174 := by decide
  have h := Artifact.isValidJumpDest_index 147 (by rfl)
  rw [hpc] at h
  exact h

@[simp] private theorem jump1646 :
    Decode.isValidJumpDest submissionBytecode 1646 = true := by
  have hpc : Artifact.instructionPC 1239 = 1646 := by decide
  have h := Artifact.isValidJumpDest_index 1239 (by rfl)
  rw [hpc] at h
  exact h

set_option linter.unusedSimpArgs false in
theorem run_secondCall (s : State) (i : Nat)
    (a b out modulus n np ret _digit q : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame i a b out modulus n np ret rest)
    (hpc : s.pc = kFirst)
    (hq : q = MachineState.readWord s.memory scratch.toNat * np)
    (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock secondCallPath s =
      some (secondEntry s i a b out modulus n np ret q rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hmul : np * MachineState.readWord s.memory scratch.toNat =
      MachineState.readWord s.memory scratch.toNat * np := by
    apply Word.word_ext
    change (np.val * (MachineState.readWord s.memory scratch.toNat).val).val =
      ((MachineState.readWord s.memory scratch.toNat).val * np.val).val
    rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hnwordToNat : (UInt256.ofNat n.toNat).toNat = n.toNat := by
    rw [hnword]
  have hjump : Decode.isValidJumpDest submissionBytecode 1503 = true := jump1503
  have hto : (1503 : UInt256).toNat = 1503 := by decide
  have hpcWord : (1503 : UInt256) = UInt256.ofNat 1503 := by decide
  have hsecondWord : (1697 : UInt256) = UInt256.ofNat 1697 := by decide
  have hscratch : (9216 : UInt256) = UInt256.ofNat 9216 := by decide
  simp (config := { maxSteps := 200000 })
    [secondCallPath, opAt, pushAt, wfOp, secondEntry, loadState,
     MontgomeryWordBlock.entry, frame, Stepper.runLocatedBlock,
     Stepper.runLocated, Stepper.runInstr, Word.succ_ofNat_mod,
     Word.ofNat_add_mod, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
     Nat.mod_eq_of_lt, Nat.add_assoc, cap, hstack, hpc, hq, hnword, hrun, hcode,
     State.activeWordsAfterUInt256, List.exchange, hjump, hto, hpcWord,
     hsecondWord, hscratch, scratch, kSecond, kFirst]
  simpa [scratch] using hmul

set_option linter.unusedSimpArgs false in
theorem run_shiftCall (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame i a b out modulus n np ret rest)
    (hpc : s.pc = kSecond)
    (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock shiftCallPath s =
      some (shiftEntry s i a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hnwordToNat : (UInt256.ofNat n.toNat).toNat = n.toNat := by
    rw [hnword]
  have hshift : (9248 : UInt256) = scratch + 32 := by decide
  have htarget : (1715 : UInt256) = UInt256.ofNat 1715 := by decide
  have hpcWord : (1715 : UInt256).toNat = 1715 := by decide
  have hcopy : (58 : UInt256).toNat = 58 := by decide
  have hnplus : (1 : UInt256) + n = UInt256.ofNat (n.toNat + 1) := by
    rw [show (1 : UInt256) = UInt256.ofNat 1 from by decide,
      ← hnword, Word.ofNat_add_mod, Nat.add_comm 1 n.toNat,
      hnwordToNat]
  have hnplusLit : UInt256.ofNat 1 + n = UInt256.ofNat (n.toNat + 1) := by
    rw [← hnword, Word.ofNat_add_mod, Nat.add_comm 1 n.toNat,
      hnwordToNat]
  simp (config := { maxSteps := 200000 })
    [shiftCallPath, opAt, pushAt, wfOp, shiftEntry, frame,
     BigHelpers.copyEntry, Stepper.runLocatedBlock, Stepper.runLocated,
     Stepper.runInstr, Word.succ_ofNat_mod, Word.ofNat_add_mod,
     Word.literal_eq_ofNat, Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
     Nat.add_assoc, cap,
     hstack, hpc, hnword, hrun, hcode, hshift, htarget, hpcWord, hcopy,
     hnplus, hnplusLit, scratch, kSecond, kShift]

set_option linter.unusedSimpArgs false in
theorem run_shiftZero (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame i a b out modulus n np ret rest)
    (hpc : s.pc = kShift)
    (hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock shiftZeroPath s =
      some (shiftZeroState s i a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hnwordToNat : (UInt256.ofNat n.toNat).toNat = n.toNat := by
    rw [hnword]
  have haddrfit : scratch.toNat + 32 * (n.toNat + 1) < 2 ^ 256 := by
    norm_num [scratch]
    omega
  have haddr : scratch + UInt256.shiftLeft (UInt256.ofNat (n.toNat + 1))
      (UInt256.ofNat 5) =
      UInt256.ofNat (scratch.toNat + 32 * (n.toNat + 1)) := by
    exact wordAddress scratch (n.toNat + 1) haddrfit
  have hbase : (9248 : UInt256) = scratch + 32 := by decide
  have hloop : (1646 : UInt256) = UInt256.ofNat 1646 := by decide
  have hnplus : (1 : UInt256) + n = UInt256.ofNat (n.toNat + 1) := by
    rw [show (1 : UInt256) = UInt256.ofNat 1 from by decide,
      ← hnword, Word.ofNat_add_mod, Nat.add_comm 1 n.toNat,
      hnwordToNat]
  have hnplusLit : UInt256.ofNat 1 + n = UInt256.ofNat (n.toNat + 1) := by
    rw [← hnword, Word.ofNat_add_mod, Nat.add_comm 1 n.toNat,
      hnwordToNat]
  have hinc : (1 : UInt256) + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    rw [show (1 : UInt256) = UInt256.ofNat 1 from by decide,
      Word.ofNat_add_mod, Nat.add_comm 1 i]
  have hincNat : UInt256.ofNat (1 + i) = UInt256.ofNat (i + 1) := by
    rw [Nat.add_comm 1 i]
  simp only [Word.literal_eq_ofNat] at hnplus hinc haddr
  have hshiftNext :
      ((UInt256.ofNat (n.toNat + 1)).shiftLeft (UInt256.ofNat 5)).toNat =
        32 * (n.toNat + 1) := by
    have hs := Word.shiftLeft_ofNat (value := n.toNat + 1) (shift := 5)
      (by omega : n.toNat + 1 < 2 ^ 256)
      (by norm_num : 5 < 256)
      (by norm_num; omega : (n.toNat + 1) * 2 ^ 5 < 2 ^ 256)
    rw [hs, Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by norm_num; omega : (n.toNat + 1) * 2 ^ 5 < 2 ^ 256)]
    norm_num [Nat.mul_comm]
  have haddrNat :
      (scratch.toNat +
        ((UInt256.ofNat 1 + n).shiftLeft (UInt256.ofNat 5)).toNat) % 2 ^ 256 =
          scratch.toNat + 32 * (n.toNat + 1) := by
    rw [hnplus, hshiftNext, Nat.mod_eq_of_lt haddrfit]
  have haddrMod :
      (9216 + 32 * (n.toNat + 1)) % 2 ^ 256 =
        9216 + 32 * (n.toNat + 1) := by
    have hfit : 9216 + 32 * (n.toNat + 1) < 2 ^ 256 := by
      norm_num
      omega
    exact Nat.mod_eq_of_lt hfit
  norm_num only [show (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      by norm_num] at haddrMod
  simp (config := { maxSteps := 300000 })
    [shiftZeroPath, opAt, pushAt, wfOp, shiftZeroState, zeroState, loop,
     frame, touch, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
     Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap, hstack, hpc,
     hnword, hnwordToNat, hn, hrun, hcode, haddrfit, haddr, haddrNat, hshiftNext,
     hbase, hloop,
     hnplus, hnplusLit, hinc, hincNat,
     jump1646, scratch, kShift, kLoop, State.activeWordsAfterUInt256]
  rw [haddrMod]
  exact ⟨rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem run_reduceCall (s : State) (a b out modulus n np ret high : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame n.toNat a b out modulus n np ret rest)
    (hpc : s.pc = kFinish)
    (hhigh : high = MachineState.readWord s.memory
      (scratch.toNat + 32 * n.toNat))
    (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock reduceCallPath s =
      some (reduceEntry s a b out modulus n np ret high rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have haddrfit : scratch.toNat + 32 * n.toNat < 2 ^ 256 := by
    norm_num [scratch]
    omega
  have haddr := wordAddress scratch n.toNat haddrfit
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hnwordToNat : (UInt256.ofNat n.toNat).toNat = n.toNat := by
    rw [hnword]
  have hshiftN :
      n.shiftLeft (UInt256.ofNat 5) = UInt256.ofNat (n.toNat * 2 ^ 5) := by
    have h0 :
        (UInt256.ofNat n.toNat).shiftLeft (UInt256.ofNat 5) =
          UInt256.ofNat (n.toNat * 2 ^ 5) := by
      exact Word.shiftLeft_ofNat (value := n.toNat) (shift := 5)
        n.val.isLt (by norm_num) (by norm_num; omega)
    simpa only [hnword] using h0
  have hshiftNToNat :
      (n.shiftLeft (UInt256.ofNat 5)).toNat = 32 * n.toNat := by
    rw [hshiftN, Word.word_toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by norm_num; omega : n.toNat * 2 ^ 5 < 2 ^ 256)]
    norm_num [Nat.mul_comm]
  have haddrEq : scratch + UInt256.shiftLeft (UInt256.ofNat n.toNat)
      (UInt256.ofNat 5) =
      UInt256.ofNat (scratch.toNat + 32 * n.toNat) := haddr
  have hloadAddr :
      (scratch.toNat + (n.shiftLeft (UInt256.ofNat 5)).toNat) % 2 ^ 256 =
        scratch.toNat + 32 * n.toNat := by
    rw [hshiftNToNat]
    exact Nat.mod_eq_of_lt haddrfit
  have hloadMod :
      (9216 + 32 * n.toNat) % 2 ^ 256 = 9216 + 32 * n.toNat := by
    have hfit : 9216 + 32 * n.toNat < 2 ^ 256 := by
      norm_num
      omega
    exact Nat.mod_eq_of_lt hfit
  norm_num only [show (2 ^ 256 : Nat) =
      115792089237316195423570985008687907853269984665640564039457584007913129639936
      by norm_num] at hloadMod
  have hbase : (9216 : UInt256) = scratch := by decide
  have hreduce : (1763 : UInt256) = UInt256.ofNat 1763 := by decide
  have hto : (174 : UInt256).toNat = 174 := by decide
  have hpcWord : (174 : UInt256) = UInt256.ofNat 174 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 174 = true := jump174
  simp (config := { maxSteps := 300000 })
    [reduceCallPath, opAt, pushAt, wfOp, reduceEntry, loadState,
     MontgomeryReduceBlock.reduceEntry, frame, Stepper.runLocatedBlock,
     Stepper.runLocated, Stepper.runInstr, Word.succ_ofNat_mod,
     Word.ofNat_add_mod, Word.literal_eq_ofNat, Word.word_toNat_ofNat,
     Nat.mod_eq_of_lt, Nat.add_assoc,
     cap, hstack, hpc, hhigh, hnword, haddrfit, haddr, haddrEq, hloadAddr,
     hbase,
     hreduce, hto, hpcWord, hjump, hrun, hcode, State.activeWordsAfterUInt256,
     hshiftN, hshiftNToNat, scratch, kReduce, kFinish]
  rw [Nat.mul_comm n.toNat 32, hloadMod]
  exact ⟨rfl, rfl, rfl, rfl⟩

set_option linter.unusedSimpArgs false in
theorem run_outputCall (s : State) (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame n.toNat a b out modulus n np ret rest)
    (hpc : s.pc = kReduce)
    (_hn : n.toNat ≤ 32)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock outputCallPath s =
      some (outputEntry s a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hnword : UInt256.ofNat n.toNat = n := (Word.word_eq_ofNat_toNat n).symm
  have hout : (1777 : UInt256) = UInt256.ofNat 1777 := by decide
  have hcopy : (58 : UInt256).toNat = 58 := by decide
  have hjump : Decode.isValidJumpDest submissionBytecode 58 = true := jump58
  simp (config := { maxSteps := 200000 })
    [outputCallPath, opAt, pushAt, wfOp, outputEntry, BigHelpers.copyEntry,
     frame, Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.literal_eq_ofNat,
     Word.word_toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_assoc, cap, hstack, hpc,
     hnword, hcode, hrun, hout, hcopy, hjump, List.exchange, scratch,
     kReduce, kDone]

set_option linter.unusedSimpArgs false in
theorem run_cleanup (s : State) (i : Nat)
    (a b out modulus n np ret : UInt256)
    (rest : List UInt256) (hcap : rest.length + 8 < 1000)
    (hstack : s.stack = frame i a b out modulus n np ret rest)
    (hpc : s.pc = kDone)
    (hret : Decode.isValidJumpDest submissionBytecode ret.toNat = true)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Stepper.runLocatedBlock cleanupPath s =
      some (cleanReturned s a b out modulus n np ret rest) := by
  have cap : ∀ k, k ≤ 24 → rest.length + k < 1024 := by omega
  have hto : ret.toNat < 2 ^ 256 := ret.val.isLt
  simp (config := { maxSteps := 200000 })
    [cleanupPath, opAt, pushAt, wfOp, cleanReturned, frame,
     Stepper.runLocatedBlock, Stepper.runLocated, Stepper.runInstr,
     Word.succ_ofNat_mod, Word.ofNat_add_mod, Word.word_toNat_ofNat,
     Nat.add_assoc, cap, hstack, hpc, hret, hcode, hrun, hto, kDone]

end Challenge.Modexp.Submission.Proofs.Bytecode.MontgomeryCorePaths
