import Challenge.Modexp.Submission.Proofs.Bytecode.BigModulus
import Challenge.Modexp.Submission.Proofs.Bytecode.BigLoad
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
/-!
# Certified base-conversion path

The emitted base-conversion loop streams every base byte through two masked
modular additions.  This artifact replaces it with a direct load of a *prefix*
of the base followed by the same bitwise loop over the remaining bytes.

If the modulus's top limb (index `count - 1`) is nonzero then
`modulus ≥ 2 ^ (256 * (count - 1))`, so the leading `32 * (count - 1)` bytes of
the base already form a residue and can be moved into place with the certified
`loadBigEndian` helper instead of being reduced bit by bit.  When the top limb
is zero, or the base is shorter than that prefix, the computed prefix length is
`0` and every byte still goes through the reducing loop.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigBase

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

/-! ## Basic blocks -/

def stubPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 632 .JUMPDEST,
   pushAt 633 2 1627,
   opAt 634 .JUMP]

def toClearDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1185 .JUMPDEST,
   pushAt 1186 2 1639,
   opAt 1187 (.Dup ⟨2, by decide⟩),
   pushAt 1188 2 3072,
   pushAt 1189 2 19,
   opAt 1190 .JUMP]

def startBaseLoopPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1191 .JUMPDEST,
   pushAt 1192 1 1,
   pushAt 1193 2 3072,
   opAt 1194 .MSTORE]

def directComputePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1195 1 1,
   opAt 1196 (.Dup ⟨2, by decide⟩),
   opAt 1197 .SUB,
   pushAt 1198 1 5,
   opAt 1199 .SHL,
   opAt 1200 (.Dup ⟨0, by decide⟩),
   opAt 1201 .MLOAD,
   opAt 1202 .ISZERO,
   opAt 1203 .ISZERO,
   opAt 1204 (.Dup ⟨1, by decide⟩),
   opAt 1205 (.Dup ⟨5, by decide⟩),
   opAt 1206 .LT,
   opAt 1207 .ISZERO,
   opAt 1208 .AND,
   pushAt 1209 0 0,
   opAt 1210 .SUB,
   opAt 1211 .AND]

def loadCallPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1212 2 1677,
   pushAt 1213 2 1024,
   opAt 1214 (.Dup ⟨2, by decide⟩),
   opAt 1215 (.Dup ⟨9, by decide⟩),
   pushAt 1216 2 439,
   opAt 1217 .JUMP]

def outerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1218 .JUMPDEST,
   opAt 1219 (.Dup ⟨3, by decide⟩),
   opAt 1220 (.Dup ⟨1, by decide⟩),
   opAt 1221 .LT,
   opAt 1222 .ISZERO,
   pushAt 1223 2 1765,
   opAt 1224 .JUMPI]

def outerToInnerPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1225 (.Dup ⟨0, by decide⟩),
   opAt 1226 (.Dup ⟨7, by decide⟩),
   opAt 1227 .ADD,
   opAt 1228 (.Dup ⟨0, by decide⟩),
   opAt 1229 .CALLDATALOAD,
   pushAt 1230 0 0,
   opAt 1231 .BYTE,
   pushAt 1232 0 0]

def innerGuardPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1233 .JUMPDEST,
   pushAt 1234 1 8,
   opAt 1235 (.Dup ⟨1, by decide⟩),
   opAt 1236 .LT,
   opAt 1237 .ISZERO,
   pushAt 1238 2 1754,
   opAt 1239 .JUMPI]

def innerToDoublePath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [pushAt 1240 2 1721,
   opAt 1241 (.Dup ⟨6, by decide⟩),
   pushAt 1242 0 0,
   pushAt 1243 1 1,
   pushAt 1244 2 1024,
   pushAt 1245 2 1024,
   pushAt 1246 2 104,
   opAt 1247 .JUMP]

def innerToAddBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1248 .JUMPDEST,
   pushAt 1249 2 1746,
   opAt 1250 (.Dup ⟨6, by decide⟩),
   pushAt 1251 0 0,
   pushAt 1252 1 1,
   opAt 1253 (.Dup ⟨5, by decide⟩),
   opAt 1254 (.Dup ⟨5, by decide⟩),
   pushAt 1255 1 7,
   opAt 1256 .SUB,
   opAt 1257 .SHR,
   opAt 1258 .AND,
   pushAt 1259 2 3072,
   pushAt 1260 2 1024,
   pushAt 1261 2 104,
   opAt 1262 .JUMP]

def innerAfterBitPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1263 .JUMPDEST,
   pushAt 1264 1 1,
   opAt 1265 .ADD,
   pushAt 1266 2 1694,
   opAt 1267 .JUMP]

def innerFinishPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1268 .JUMPDEST,
   opAt 1269 .POP,
   opAt 1270 .POP,
   opAt 1271 .POP,
   pushAt 1272 1 1,
   opAt 1273 .ADD,
   pushAt 1274 2 1677,
   opAt 1275 .JUMP]

def outerFinishToAccumulatorPath :
    List (Challenge.EvmProof.Stepper.Located Artifact.submissionArtifact .Osaka) :=
  [opAt 1276 .JUMPDEST,
   opAt 1277 .POP,
   pushAt 1278 2 944,
   opAt 1279 (.Dup ⟨2, by decide⟩),
   pushAt 1280 0 0,
   pushAt 1281 1 1,
   pushAt 1282 2 3072,
   pushAt 1283 2 2048,
   pushAt 1284 2 104,
   opAt 1285 .JUMP]

/-! ## The directly loaded prefix -/

/-- Byte offset of the modulus's top limb, exactly as the bytecode computes it
(`shl(5, sub(n, 1))`).  Left as a machine word so the definition is total. -/
def topOffsetWord (count : Nat) : UInt256 :=
  UInt256.shiftLeft (UInt256.ofNat count - 1) 5

def topOffset (count : Nat) : Nat := (topOffsetWord count).toNat

/-- `1` when the top modulus limb is nonzero *and* the prefix fits in the base,
`0` otherwise -- the branchless condition the bytecode forms. -/
def directTake (memory : ByteArray) (count baseSize : Nat) : Nat :=
  if (MachineState.readWord memory (topOffset count)).toNat = 0 then 0
  else if baseSize < topOffset count then 0
  else 1

/-- Number of leading base bytes moved into place by `loadBigEndian`. -/
def directValue (memory : ByteArray) (count baseSize : Nat) : Nat :=
  directTake memory count baseSize * topOffset count

theorem directTake_le_one (memory : ByteArray) (count baseSize : Nat) :
    directTake memory count baseSize ≤ 1 := by
  unfold directTake
  split
  · omega
  · split <;> omega

/-- The cap makes the prefix length unconditionally bounded by the base length,
so no new range hypothesis has to propagate downstream. -/
theorem directValue_le (memory : ByteArray) (count baseSize : Nat) :
    directValue memory count baseSize ≤ baseSize := by
  unfold directValue directTake
  split
  · omega
  · split
    · omega
    · omega

private theorem land_comm (a b : UInt256) :
    UInt256.land a b = UInt256.land b a := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_land, Nat.land_comm]

/-- The word the bytecode leaves on the stack is exactly `directValue`. -/
theorem directWord_eq (memory : ByteArray) (count baseSize : Nat)
    (hbase : baseSize < 2 ^ 256) :
    UInt256.land
        (0 - UInt256.land
          (UInt256.lt (UInt256.ofNat baseSize) (topOffsetWord count)).isZero
          (MachineState.readWord memory (topOffset count)).isZero.isZero)
        (topOffsetWord count) =
      UInt256.ofNat (directValue memory count baseSize) := by
  have htopdef : (topOffsetWord count).toNat = topOffset count := rfl
  have hbaseNat : (UInt256.ofNat baseSize).toNat = baseSize := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt hbase]
  have hcond :
      (UInt256.land
        (UInt256.lt (UInt256.ofNat baseSize) (topOffsetWord count)).isZero
        (MachineState.readWord memory (topOffset count)).isZero.isZero).toNat =
      directTake memory count baseSize := by
    unfold directTake
    by_cases hzero : (MachineState.readWord memory (topOffset count)).toNat = 0
    · simp [Challenge.EvmProof.Word.word_toNat_land,
        Challenge.EvmProof.Word.word_toNat_isZero,
        Challenge.EvmProof.Word.word_toNat_lt, hbaseNat, htopdef, hzero]
    · by_cases hlt : baseSize < topOffset count
      · simp [Challenge.EvmProof.Word.word_toNat_land,
          Challenge.EvmProof.Word.word_toNat_isZero,
          Challenge.EvmProof.Word.word_toNat_lt, hbaseNat, htopdef, hzero, hlt]
      · simp [Challenge.EvmProof.Word.word_toNat_land,
          Challenge.EvmProof.Word.word_toNat_isZero,
          Challenge.EvmProof.Word.word_toNat_lt, hbaseNat, htopdef, hzero, hlt]
  have hle1 :
      (UInt256.land
        (UInt256.lt (UInt256.ofNat baseSize) (topOffsetWord count)).isZero
        (MachineState.readWord memory (topOffset count)).isZero.isZero).toNat
      ≤ 1 := by
    rw [hcond]; exact directTake_le_one memory count baseSize
  have hmask := BigHelpers.land_sub_zero_take_toNat (topOffsetWord count) hle1
  rw [← Challenge.EvmProof.Word.word_eq_ofNat_toNat] at hmask
  rw [land_comm]
  apply Challenge.EvmProof.Word.word_ext
  rw [hmask, Challenge.EvmProof.Word.word_toNat_ofNat, hcond]
  have hbound : directValue memory count baseSize < 2 ^ 256 := by
    have := Nat.mul_le_mul_right (topOffset count)
      (directTake_le_one memory count baseSize)
    have htop : topOffset count < 2 ^ 256 := (topOffsetWord count).val.isLt
    simp only [directValue]
    omega
  rw [Nat.mod_eq_of_lt hbound]
  rfl

/-! ## States -/

def frame (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : List UInt256 :=
  [accumulator, UInt256.ofNat count] ++ rest

/-- The stack below the limb count: base length, exponent length, modulus
length and the base offset. -/
def baseTail (baseSize e m baseOff : Nat) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat baseSize, UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest

/-- The in-place stub hands control to the appended body. -/
def stubbed (s : State) (count : Nat) (rest : List UInt256) : State :=
  { BigModulus.scanNonzero s count rest with pc := UInt256.ofNat 1627 }

def afterClearDouble (s : State) (accumulator : UInt256) (count : Nat)
    (rest : List UInt256) : State :=
  BigHelpers.clearReturned (stubbed s count rest) 3072 count 1639
    (frame accumulator count rest)

/-- After `mstore(0x0c00, 1)`. -/
def baseWritten (t : State) : State :=
  { t with pc := UInt256.ofNat 1646
           memory := MachineState.writeBytes t.memory
             (Data.Bytes.natToBytesPadded 1 32) 3072
           activeWords := UInt256.ofNat (MachineState.activeWordsAfter
             t.activeWords.toNat 3072 32) }

/-- After the branchless prefix-length computation. -/
def baseDirectOf (t : State) (count baseSize : Nat) : State :=
  { t with pc := UInt256.ofNat 1665
           stack := UInt256.ofNat (directValue t.memory count baseSize) :: t.stack
           activeWords := UInt256.ofNat (MachineState.activeWordsAfter
             t.activeWords.toNat (topOffset count) 32) }

/-- Prefix length actually used from a given region-entry state. -/
def basePrefix (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) : Nat :=
  directValue (baseWritten (afterClearDouble s accumulator count rest)).memory
    count baseSize

def baseLoopEntry (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256) : State :=
  BigLoad.loadReturned
    (baseDirectOf (baseWritten (afterClearDouble s accumulator count
      (baseTail baseSize e m baseOff rest))) count baseSize)
    (UInt256.ofNat baseOff)
    (UInt256.ofNat (basePrefix s accumulator count baseSize
      (baseTail baseSize e m baseOff rest)))
    (UInt256.ofNat 1024) (UInt256.ofNat 1677)
    (UInt256.ofNat (basePrefix s accumulator count baseSize
        (baseTail baseSize e m baseOff rest)) ::
      frame accumulator count (baseTail baseSize e m baseOff rest))

def baseBit (byte : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight byte (UInt256.ofNat (7 - j))) 1

def loadedBaseByte (s : State) (baseOff i : Nat) : UInt256 :=
  UInt256.byteAt 0 (MachineState.readWord s.executionEnv.calldata (baseOff + i))

def bitProgress (count : Nat) (byte : UInt256) : Nat → State → State
  | 0, s => s
  | j + 1, s =>
      let before := bitProgress count byte j s
      let doubled := BigHelpers.addReturned before 1024 1024 1 0 count 1721 []
      BigHelpers.addReturned doubled 1024 3072 (baseBit byte j) 0 count 1746 []

def baseProgress (count baseOff : Nat) : Nat → State → State
  | 0, s => s
  | i + 1, s =>
      let before := baseProgress count baseOff i s
      bitProgress count (loadedBaseByte before baseOff i) 8 before

@[simp] theorem bitProgress_halt (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) : (bitProgress count byte j s).halt = s.halt := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem bitProgress_executionEnv (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (bitProgress count byte j s).executionEnv = s.executionEnv := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp [bitProgress, BigHelpers.addReturned, ih]

@[simp] theorem bitProgress_activeFork (count : Nat) (byte : UInt256)
    (j : Nat) (s : State) :
    (bitProgress count byte j s).fork = s.fork := by
  simp [State.fork]

@[simp] theorem baseProgress_halt (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).halt = s.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgress, ih]

@[simp] theorem baseProgress_executionEnv (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).executionEnv = s.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [baseProgress, ih]

@[simp] theorem baseProgress_activeFork (count baseOff i : Nat) (s : State) :
    (baseProgress count baseOff i s).fork = s.fork := by
  simp [State.fork]

@[simp] theorem loadedBaseByte_baseProgress (count baseOff i j : Nat)
    (s : State) :
    loadedBaseByte (baseProgress count baseOff j s) baseOff i =
      loadedBaseByte s baseOff i := by
  simp [loadedBaseByte]

def outerLoop (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { s with pc := UInt256.ofNat 1677
           stack := [UInt256.ofNat i, accumulator, UInt256.ofNat count,
             UInt256.ofNat baseSize] ++ rest }

def outerBody (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulator count baseSize rest i with
      pc := UInt256.ofNat 1686 }

def innerLoop (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  let progress := bitProgress count byte j s
  { progress with
    pc := UInt256.ofNat 1694
    stack := [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
      UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest }

def innerBody (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) (j : Nat) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest j with
      pc := UInt256.ofNat 1704 }

def innerExit (s : State) (accumulator : UInt256) (count baseSize i : Nat)
    (offset byte : UInt256) (rest : List UInt256) : State :=
  { innerLoop s accumulator count baseSize i offset byte rest 8 with
      pc := UInt256.ofNat 1754 }

def outerExit (s : State) (accumulator : UInt256) (count baseSize : Nat)
    (rest : List UInt256) (i : Nat) : State :=
  { outerLoop s accumulator count baseSize rest i with
      pc := UInt256.ofNat 1765 }

def innerFrame (accumulator : UInt256) (count baseSize i j : Nat)
    (offset byte : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat j, byte, offset, UInt256.ofNat i, accumulator,
    UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest

def doubledReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 1721
    (innerFrame accumulator count baseSize i j offset byte rest)

def bitReturned (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 1746
    (innerFrame accumulator count baseSize i j offset byte rest)

/-! ## Program-counter tables and jump destinations -/

@[simp] private theorem stubPCs (i : Nat) (hi : 632 ≤ i)
    (hii : i ≤ 634) :
    Artifact.submissionArtifact.instructionPC i =
      ([811,812,815])[i - 632]! := by
  interval_cases i <;> decide

@[simp] private theorem appendedPCs (i : Nat) (hi : 1185 ≤ i)
    (hii : i ≤ 1285) :
    Artifact.submissionArtifact.instructionPC i =
      ([1627,1628,1631,1632,1635,1638,1639,1640,1642,1645,1646,1648,1649,1650,1652,
        1653,1654,1655,1656,1657,1658,1659,1660,1661,1662,1663,1664,1665,1668,1671,
        1672,1673,1676,1677,1678,1679,1680,1681,1682,1685,1686,1687,1688,1689,1690,
        1691,1692,1693,1694,1695,1697,1698,1699,1700,1703,1704,1707,1708,1709,1711,
        1714,1717,1720,1721,1722,1725,1726,1727,1729,1730,1731,1733,1734,1735,1736,
        1739,1742,1745,1746,1747,1749,1750,1753,1754,1755,1756,1757,1758,1760,1761,
        1764,1765,1766,1767,1770,1771,1772,1774,1777,1780,1783])[i - 1185]! := by
  interval_cases i <;> decide

private theorem jump19 :
    Decode.isValidJumpDest submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump104 :
    Decode.isValidJumpDest submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

private theorem jump439 :
    Decode.isValidJumpDest submissionBytecode 439 = true :=
  Artifact.isValidJumpDest_index 353 (by rfl)

private theorem jump1627 :
    Decode.isValidJumpDest submissionBytecode 1627 = true :=
  Artifact.isValidJumpDest_index 1185 (by rfl)

private theorem jump1639 :
    Decode.isValidJumpDest submissionBytecode 1639 = true :=
  Artifact.isValidJumpDest_index 1191 (by rfl)

private theorem jump1677 :
    Decode.isValidJumpDest submissionBytecode 1677 = true :=
  Artifact.isValidJumpDest_index 1218 (by rfl)

private theorem jump1694 :
    Decode.isValidJumpDest submissionBytecode 1694 = true :=
  Artifact.isValidJumpDest_index 1233 (by rfl)

private theorem jump1721 :
    Decode.isValidJumpDest submissionBytecode 1721 = true :=
  Artifact.isValidJumpDest_index 1248 (by rfl)

private theorem jump1746 :
    Decode.isValidJumpDest submissionBytecode 1746 = true :=
  Artifact.isValidJumpDest_index 1263 (by rfl)

private theorem jump1754 :
    Decode.isValidJumpDest submissionBytecode 1754 = true :=
  Artifact.isValidJumpDest_index 1268 (by rfl)

private theorem jump1765 :
    Decode.isValidJumpDest submissionBytecode 1765 = true :=
  Artifact.isValidJumpDest_index 1276 (by rfl)

/-! ## Block semantics -/

set_option linter.unusedSimpArgs false in
theorem run_stub (s : State) (count : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock stubPath
      (BigModulus.scanNonzero s count rest) =
      some (stubbed s count rest) := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  have h1627 : (1627 : UInt256).toNat = 1627 := by decide
  have h1627Word : (1627 : UInt256) = UInt256.ofNat 1627 := by decide
  simp (disch := omega) [stubPath, opAt, pushAt, wfOp, stubbed,
    BigModulus.scanNonzero, stubPCs, hcode, hrun, jump1627, h1627, h1627Word,
    hc, Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_toClearDouble (s : State) (accumulator : UInt256)
    (count : Nat) (rest : List UInt256) (hcap : rest.length < 1016)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock toClearDoublePath
      (stubbed s count rest) =
      some (BigHelpers.clearEntry (stubbed s count rest)
        3072 count 1639 (frame accumulator count rest)) := by
  have hc : ∀ n ≤ 8, rest.length + n < 1024 := by omega
  have h19 : (19 : UInt256).toNat = 19 := by decide
  have h19Word : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have h1627 : (UInt256.ofNat 1627).toNat = 1627 := by decide
  simp (disch := omega) [toClearDoublePath, opAt, pushAt, wfOp, stubbed,
    BigModulus.scanNonzero, BigHelpers.clearEntry, frame, appendedPCs, hacc,
    hcode, hrun, jump19, h19, h19Word, h1627, hc,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_startBaseLoop (t : State) (hcap : t.stack.length < 1016)
    (hpc : t.pc = 1639) (hrun : t.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock startBaseLoopPath t =
      some (baseWritten t) := by
  have hc : ∀ n ≤ 8, t.stack.length + n < 1024 := by omega
  have hlen : t.stack.length < 1024 := by omega
  have h1639 : (1639 : UInt256).toNat = 1639 := by decide
  have h1639Word : (1639 : UInt256) = UInt256.ofNat 1639 := by decide
  have h1639Nat : (UInt256.ofNat 1639).toNat = 1639 := by decide
  have h1Nat : (1 : UInt256).toNat = 1 := by decide
  have h3072Nat : (3072 : UInt256).toNat = 3072 := by decide
  simp (disch := omega) [startBaseLoopPath, opAt, pushAt, wfOp, baseWritten,
    appendedPCs, hpc, hrun, h1639, h1639Word, h1639Nat, h1Nat, h3072Nat, hc, hlen,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_directCompute (t : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 1010) (hbase : baseSize < 2 ^ 256)
    (hstack : t.stack = frame accumulator count
      (baseTail baseSize e m baseOff rest))
    (hpc : t.pc = UInt256.ofNat 1646) (hrun : t.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock directComputePath t =
      some (baseDirectOf t count baseSize) := by
  have hc : ∀ n ≤ 12, rest.length + n < 1024 := by omega
  have h1646 : (UInt256.ofNat 1646).toNat = 1646 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hdirect := directWord_eq t.memory count baseSize hbase
  simp only [topOffsetWord, topOffset] at hdirect
  simp (disch := omega) [directComputePath, opAt, pushAt, wfOp, baseDirectOf,
    frame, baseTail, appendedPCs, hpc, hstack, hrun, h1646, hc, hzero,
    topOffsetWord, topOffset, hdirect,
    State.activeWordsAfterUInt256,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_loadCall (t : State) (accumulator : UInt256)
    (count baseSize e m baseOff direct : Nat) (rest : List UInt256)
    (hcap : rest.length < 1010)
    (hstack : t.stack = UInt256.ofNat direct ::
      frame accumulator count (baseTail baseSize e m baseOff rest))
    (hpc : t.pc = UInt256.ofNat 1665)
    (hcode : t.executionEnv.code = submissionBytecode)
    (hrun : t.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock loadCallPath t =
      some (BigLoad.loadEntry t (UInt256.ofNat baseOff)
        (UInt256.ofNat direct) (UInt256.ofNat 1024) (UInt256.ofNat 1677)
        t.stack) := by
  have hc : ∀ n ≤ 14, rest.length + n < 1024 := by omega
  have h1665 : (UInt256.ofNat 1665).toNat = 1665 := by decide
  have h439 : (439 : UInt256).toNat = 439 := by decide
  have h439Word : (439 : UInt256) = UInt256.ofNat 439 := by decide
  have h1024Word : (1024 : UInt256) = UInt256.ofNat 1024 := by decide
  have h1677Word : (1677 : UInt256) = UInt256.ofNat 1677 := by decide
  simp (disch := omega) [loadCallPath, opAt, pushAt, wfOp, BigLoad.loadEntry,
    frame, baseTail, appendedPCs, hpc, hstack, hcode, hrun, jump439,
    h1665, h439, h439Word, h1024Word, h1677Word, hc,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerGuard (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (hbase : baseSize < 2 ^ 256)
    (hi : i < baseSize) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulator count baseSize rest i) =
      some (outerBody s accumulator count baseSize rest i) := by
  have hi256 : i < 2 ^ 256 := hi.trans hbase
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (UInt256.ofNat baseSize) = 1 := by
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hbase, if_pos hi]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerBody,
    appendedPCs, hrun, hlt, honeNat, hc4, hc5, hc6, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerToInner (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1013) (hbaseOff : baseOff + i < 2 ^ 256)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerToInnerPath
      (outerBody s accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i) =
      some (innerLoop s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) (loadedBaseByte s baseOff i)
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) 0) := by
  have hi : i < 2 ^ 256 := by omega
  have hbase : baseOff < 2 ^ 256 := by omega
  have hadd := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := baseOff) (by omega)
  have hoffNat : (UInt256.ofNat (baseOff + i)).toNat = baseOff + i := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hbaseOff]
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hc10 : rest.length + 10 < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have h0Word : (0 : UInt256) = UInt256.ofNat 0 := by decide
  simp [outerToInnerPath, opAt, pushAt, wfOp, outerBody, outerLoop,
    innerLoop, bitProgress, loadedBaseByte, appendedPCs, hrun, hadd,
    hoffNat, hzero, h0Word, hc7, hc8, hc9, hc10,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm]

set_option linter.unusedSimpArgs false in
theorem run_innerGuard (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013) (hj : j < 8)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulator count baseSize i offset byte rest j) =
      some (innerBody s accumulator count baseSize i offset byte rest j) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hlt : UInt256.lt (UInt256.ofNat j) 8 = 1 := by
    have hj256 : j < 2 ^ 256 := by omega
    have h8 : (8 : UInt256).toNat = 8 := by decide
    rw [UInt256.lt, Challenge.EvmProof.Word.word_toNat_ofNat,
      Nat.mod_eq_of_lt hj256, h8, if_pos hj]
    decide
  have honeNat : (1 : UInt256).toNat = 1 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerBody,
    appendedPCs, hrun, hlt, honeNat, hc7, hc8, hc9, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToDouble (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToDoublePath
      (innerBody s accumulator count baseSize i offset byte rest j) =
      some (BigHelpers.addEntry
        (innerBody s accumulator count baseSize i offset byte rest j)
        1024 1024 1 0 count 1721
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hc : ∀ n ≤ 14, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp (disch := omega) [innerToDoublePath, opAt, pushAt, wfOp, innerBody,
    innerLoop, BigHelpers.addEntry, innerFrame, appendedPCs, hcode, hrun,
    jump104, h104, h104Word, hzero, hc,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerToAddBit (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1007) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerToAddBitPath
      (doubledReturned s accumulator count baseSize i j offset byte rest) =
      some (BigHelpers.addEntry
        (doubledReturned s accumulator count baseSize i j offset byte rest)
        1024 3072 (baseBit byte j) 0 count 1746
        (innerFrame accumulator count baseSize i j offset byte rest)) := by
  have hj7 : j ≤ 7 := by omega
  have hsub := Challenge.EvmProof.Word.ofNat_sub_ofNat hj7
    (by norm_num : 7 < 2 ^ 256)
  have hc : ∀ n ≤ 14, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h1721 : (1721 : UInt256).toNat = 1721 := by decide
  have h1721Word : (1721 : UInt256) = UInt256.ofNat 1721 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hseven : (7 : UInt256) = UInt256.ofNat 7 := by decide
  simp (disch := omega) [innerToAddBitPath, opAt, pushAt, wfOp,
    doubledReturned, innerBody, innerLoop, BigHelpers.addReturned,
    BigHelpers.addEntry, innerFrame, baseBit, appendedPCs, hcode, hrun,
    jump104, hsub, h104, h104Word, h1721, h1721Word, hzero, hone, hseven, hc,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerAfterBit (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256)
    (rest : List UInt256) (hcap : rest.length < 1013) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerAfterBitPath
      (bitReturned s accumulator count baseSize i j offset byte rest) =
      some (innerLoop s accumulator count baseSize i offset byte rest (j + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := j) (b := 1) (by omega : j + 1 < 2 ^ 256)
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have h1694 : (1694 : UInt256).toNat = 1694 := by decide
  have h1694Word : (1694 : UInt256) = UInt256.ofNat 1694 := by decide
  have h1746 : (1746 : UInt256).toNat = 1746 := by decide
  have h1746Word : (1746 : UInt256) = UInt256.ofNat 1746 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerAfterBitPath, opAt, pushAt, wfOp, bitReturned,
    doubledReturned, innerBody, innerLoop, innerFrame, bitProgress,
    BigHelpers.addReturned, appendedPCs, hcode, hrun, jump1694,
    hinc, h1694, h1694Word, h1746, h1746Word, hone, hc7, hc8, hc9,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinishGuard (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerGuardPath
      (innerLoop s accumulator count baseSize i offset byte rest 8) =
      some (innerExit s accumulator count baseSize i offset byte rest) := by
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have hc9 : rest.length + 9 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1754 : (1754 : UInt256).toNat = 1754 := by decide
  have h1754Word : (1754 : UInt256) = UInt256.ofNat 1754 := by decide
  have h8Nat : (8 : UInt256).toNat = 8 := by decide
  simp [innerGuardPath, opAt, pushAt, wfOp, innerLoop, innerExit,
    appendedPCs, hcode, hrun, jump1754, hzeroFalse, h1754, h1754Word,
    h8Nat, hc7, hc8, hc9, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_innerFinish (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1013) (hi : i + 1 < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock innerFinishPath
      (innerExit s accumulator count baseSize i offset byte rest) =
      some (outerLoop (bitProgress count byte 8 s) accumulator count baseSize
        rest (i + 1)) := by
  have hinc := Challenge.EvmProof.Word.ofNat_add_ofNat
    (a := i) (b := 1) hi
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hc7 : rest.length + 7 < 1024 := by omega
  have hc8 : rest.length + 8 < 1024 := by omega
  have h1677 : (1677 : UInt256).toNat = 1677 := by decide
  have h1677Word : (1677 : UInt256) = UInt256.ofNat 1677 := by decide
  have h1754 : (1754 : UInt256).toNat = 1754 := by decide
  have h1754Word : (1754 : UInt256) = UInt256.ofNat 1754 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [innerFinishPath, opAt, pushAt, wfOp, innerExit, innerLoop,
    outerLoop, appendedPCs, hcode, hrun, jump1677, hinc,
    h1677, h1677Word, h1754, h1754Word, hone, hc4, hc5, hc6, hc7, hc8,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerFinishGuard (s : State) (accumulator : UInt256)
    (count baseSize : Nat) (rest : List UInt256)
    (hcap : rest.length < 1016) (_hbase : baseSize < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerGuardPath
      (outerLoop s accumulator count baseSize rest baseSize) =
      some (outerExit s accumulator count baseSize rest baseSize) := by
  have hc4 : rest.length + 4 < 1024 := by omega
  have hc5 : rest.length + 5 < 1024 := by omega
  have hc6 : rest.length + 6 < 1024 := by omega
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have h1765 : (1765 : UInt256).toNat = 1765 := by decide
  have h1765Word : (1765 : UInt256) = UInt256.ofNat 1765 := by decide
  simp [outerGuardPath, opAt, pushAt, wfOp, outerLoop, outerExit,
    appendedPCs, hcode, hrun, jump1765, hzeroFalse, h1765, h1765Word,
    hc4, hc5, hc6, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

set_option linter.unusedSimpArgs false in
theorem run_outerFinishToAccumulator (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (rest : List UInt256)
    (hcap : rest.length < 1009) (hcode : s.executionEnv.code = submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock outerFinishToAccumulatorPath
      (outerExit s accumulator count baseSize rest i) =
      some (BigHelpers.addEntry (outerExit s accumulator count baseSize rest i)
        2048 3072 1 0 count 944
        ([accumulator, UInt256.ofNat count, UInt256.ofNat baseSize] ++ rest)) := by
  have hc : ∀ n ≤ 12, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256).toNat = 104 := by decide
  have h104Word : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h1765 : (1765 : UInt256).toNat = 1765 := by decide
  have h1765Word : (1765 : UInt256) = UInt256.ofNat 1765 := by decide
  have h944Word : (944 : UInt256) = UInt256.ofNat 944 := by decide
  have hzero : ({ val := 0 } : UInt256) = 0 := by decide
  simp (disch := omega) [outerFinishToAccumulatorPath, opAt, pushAt, wfOp,
    outerExit, outerLoop, BigHelpers.addEntry, appendedPCs, hcode, hrun,
    jump104, h104, h104Word, h1765, h1765Word, h944Word, hzero, hc,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.succ_ofNat_mod, Nat.add_assoc]

/-! ## Gas traces -/

def gasSteps_innerIteration (s : State) (accumulator : UInt256)
    (count baseSize i j : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256) (hj : j < 8)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulator count baseSize i offset byte rest j)
      (innerLoop s accumulator count baseSize i offset byte rest (j + 1)) := by
  have hframe : (innerFrame accumulator count baseSize i j offset byte rest).length <
      1000 := by
    simp [innerFrame]
    omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerGuard s accumulator count baseSize i j offset byte rest
        (by omega) hj hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have htoDouble := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerToDoublePath
      (by simpa [innerBody, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerBody, innerLoop, State.fork] using hfork)
      (run_innerToDouble s accumulator count baseSize i j offset byte rest
        (by omega) hcode hrun)
      (by simpa [innerBody, innerLoop] using hrun)
      (by simpa [innerBody, innerLoop, State.fork] using hnp)
  have hdouble := BigHelpers.gasSteps_addMaskedMod
    (innerBody s accumulator count baseSize i offset byte rest j)
    1024 1024 1 0 count 1721
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [innerBody, innerLoop] using hcode)
    (by simpa [innerBody, innerLoop, State.fork] using hfork)
    (by simpa [innerBody, innerLoop] using hrun)
    (by simpa [innerBody, innerLoop, State.fork] using hnp) jump1721
  have htoBit := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerToAddBitPath
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hfork)
      (run_innerToAddBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop] using hrun)
      (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
        innerLoop, State.fork] using hnp)
  have hbit := BigHelpers.gasSteps_addMaskedMod
    (doubledReturned s accumulator count baseSize i j offset byte rest)
    1024 3072 (baseBit byte j) 0 count 1746
    (innerFrame accumulator count baseSize i j offset byte rest) hframe hcount
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hcode)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hfork)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop] using hrun)
    (by simpa [doubledReturned, BigHelpers.addReturned, innerBody,
      innerLoop, State.fork] using hnp) jump1746
  have hafter := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerAfterBitPath
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, State.fork] using hfork)
      (run_innerAfterBit s accumulator count baseSize i j offset byte rest
        (by omega) hj hcode hrun)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop] using hrun)
      (by simpa [bitReturned, doubledReturned, BigHelpers.addReturned,
        innerBody, innerLoop, State.fork] using hnp)
  exact hguard.trans <| htoDouble.trans <| hdouble.trans <|
    htoBit.trans <| hbit.trans hafter

def gasSteps_innerLoop (s : State) (accumulator : UInt256)
    (count baseSize i : Nat) (offset byte : UInt256) (rest : List UInt256)
    (hcap : rest.length < 993) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (innerLoop s accumulator count baseSize i offset byte rest 0)
      (innerLoop s accumulator count baseSize i offset byte rest 8) := by
  exact Challenge.EvmProof.GasSteps.iterateBounded 8 fun j hj =>
    gasSteps_innerIteration s accumulator count baseSize i j offset byte rest
      hcap hcount hj hcode hfork hrun hnp

def gasSteps_baseByte (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff i : Nat) (rest : List UInt256)
    (hcap : rest.length < 990) (hcount : count < 2 ^ 256)
    (hbase : baseSize < 2 ^ 256) (hi : i < baseSize)
    (hoff : baseOff + i < 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (outerLoop s accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest) i)
      (outerLoop (bitProgress count (loadedBaseByte s baseOff i) 8 s)
        accumulator count baseSize
        ([UInt256.ofNat e, UInt256.ofNat m, UInt256.ofNat baseOff] ++ rest)
        (i + 1)) := by
  let byte := loadedBaseByte s baseOff i
  let fullRest := [UInt256.ofNat e, UInt256.ofNat m,
    UInt256.ofNat baseOff] ++ rest
  have hfull : fullRest.length < 993 := by simp [fullRest]; omega
  have hguard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerGuardPath
      (by simpa [outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerLoop, State.fork] using hfork)
      (run_outerGuard s accumulator count baseSize i fullRest
        (by simp [fullRest]; omega) hbase hi hrun)
      (by simpa [outerLoop] using hrun)
      (by simpa [outerLoop, State.fork] using hnp)
  have hload := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka outerToInnerPath
      (by simpa [outerBody, outerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [outerBody, outerLoop, State.fork] using hfork)
      (run_outerToInner s accumulator count baseSize e m baseOff i rest
        (by omega) hoff hrun)
      (by simpa [outerBody, outerLoop] using hrun)
      (by simpa [outerBody, outerLoop, State.fork] using hnp)
  have hinner := gasSteps_innerLoop s accumulator count baseSize i
    (UInt256.ofNat (baseOff + i)) byte fullRest hfull hcount hcode hfork hrun hnp
  have hfinishGuard := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerGuardPath
      (by simpa [innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerLoop, State.fork] using hfork)
      (run_innerFinishGuard s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) hcode hrun)
      (by simpa [innerLoop] using hrun)
      (by simpa [innerLoop, State.fork] using hnp)
  have hfinish := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka innerFinishPath
      (by simpa [innerExit, innerLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [innerExit, innerLoop, State.fork] using hfork)
      (run_innerFinish s accumulator count baseSize i
        (UInt256.ofNat (baseOff + i)) byte fullRest
        (by simp [fullRest]; omega) (by omega) hcode hrun)
      (by simpa [innerExit, innerLoop] using hrun)
      (by simpa [innerExit, innerLoop, State.fork] using hnp)
  exact Challenge.EvmProof.GasSteps.cast
    (hguard.trans (hload.trans (hinner.trans (hfinishGuard.trans hfinish))))
    (by simp [fullRest]) (by simp [byte, fullRest])

set_option linter.unusedSimpArgs false in
def gasSteps_baseSetup (s : State) (accumulator : UInt256)
    (count baseSize e m baseOff : Nat) (rest : List UInt256)
    (hcap : rest.length < 990)
    (hacc : accumulator = BigModulus.scanOr s.memory count)
    (hcount : count < 2 ^ 256) (hbase : baseSize < 2 ^ 256)
    (hoff : baseOff < 2 ^ 256)
    (hoffFit : baseOff + baseSize ≤ 2 ^ 256)
    (hcode : s.executionEnv.code = submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig s.executionEnv.fork
      s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (BigModulus.scanNonzero s count (baseTail baseSize e m baseOff rest))
      (baseLoopEntry s accumulator count baseSize e m baseOff rest) := by
  have htail : (baseTail baseSize e m baseOff rest).length = rest.length + 4 := by
    simp [baseTail]
  have hframe : (frame accumulator count
      (baseTail baseSize e m baseOff rest)).length < 1017 := by
    simp [frame, htail]
    omega
  have hcodeStub :
      (stubbed s count (baseTail baseSize e m baseOff rest)).executionEnv.code =
        submissionBytecode := by
    simpa [stubbed, BigModulus.scanNonzero] using hcode
  have hforkStub :
      (stubbed s count (baseTail baseSize e m baseOff rest)).fork = .Osaka := by
    simpa [stubbed, BigModulus.scanNonzero, State.fork] using hfork
  have hrunStub :
      (stubbed s count (baseTail baseSize e m baseOff rest)).halt = .Running := by
    simpa [stubbed, BigModulus.scanNonzero] using hrun
  have hnpStub : Precompile.isPrecompileWithConfig
      (stubbed s count (baseTail baseSize e m baseOff rest)).executionEnv.precompileConfig
      (stubbed s count (baseTail baseSize e m baseOff rest)).executionEnv.fork
      (stubbed s count (baseTail baseSize e m baseOff rest)).executionEnv.codeAddr
      = false := by
    simpa [stubbed, BigModulus.scanNonzero, State.fork] using hnp
  have hstub := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka stubPath
      (by simpa [BigModulus.scanNonzero, Artifact.submissionArtifact] using hcode)
      (by simpa [BigModulus.scanNonzero, State.fork] using hfork)
      (run_stub s count (baseTail baseSize e m baseOff rest) (by omega) hcode hrun)
      (by simpa [BigModulus.scanNonzero] using hrun)
      (by simpa [BigModulus.scanNonzero, State.fork] using hnp)
  have htoClear := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka toClearDoublePath
      (by simpa [Artifact.submissionArtifact] using hcodeStub)
      hforkStub
      (run_toClearDouble s accumulator count (baseTail baseSize e m baseOff rest)
        (by omega) hacc hcode hrun)
      hrunStub hnpStub
  have hclear := BigHelpers.gasSteps_clear
    (stubbed s count (baseTail baseSize e m baseOff rest)) 3072 count 1639
    (frame accumulator count (baseTail baseSize e m baseOff rest)) hframe hcount
    hcodeStub hforkStub hrunStub hnpStub jump1639
  have hcodeCleared :
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).executionEnv.code =
        submissionBytecode := by
    simpa [afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero] using hcode
  have hforkCleared :
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).fork = .Osaka := by
    simpa [afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero, State.fork] using hfork
  have hrunCleared :
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).halt = .Running := by
    simpa [afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero] using hrun
  have hnpCleared : Precompile.isPrecompileWithConfig
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).executionEnv.precompileConfig
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).executionEnv.fork
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).executionEnv.codeAddr = false := by
    simpa [afterClearDouble, BigHelpers.clearReturned, stubbed,
      BigModulus.scanNonzero, State.fork] using hnp
  have hstackCleared :
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).stack =
        frame accumulator count (baseTail baseSize e m baseOff rest) := by
    simp [afterClearDouble, BigHelpers.clearReturned]
  have hpcCleared :
      (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest)).pc = 1639 := by
    simp [afterClearDouble, BigHelpers.clearReturned]
  have hmstore := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka startBaseLoopPath
      (by simpa [Artifact.submissionArtifact] using hcodeCleared)
      hforkCleared
      (run_startBaseLoop (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))
        (by rw [hstackCleared]; simp [frame, htail]; omega)
        hpcCleared hrunCleared)
      hrunCleared hnpCleared
  have hstackWritten :
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).stack =
        frame accumulator count (baseTail baseSize e m baseOff rest) := by
    simpa [baseWritten] using hstackCleared
  have hpcWritten :
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).pc = UInt256.ofNat 1646 := by
    simp [baseWritten]
  have hcodeWritten :
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).executionEnv.code =
        submissionBytecode := by
    simpa [baseWritten] using hcodeCleared
  have hforkWritten :
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).fork = .Osaka := by
    simpa [baseWritten, State.fork] using hforkCleared
  have hrunWritten :
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).halt = .Running := by
    simpa [baseWritten] using hrunCleared
  have hnpWritten : Precompile.isPrecompileWithConfig
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).executionEnv.precompileConfig
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).executionEnv.fork
      (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))).executionEnv.codeAddr
      = false := by
    simpa [baseWritten, State.fork] using hnpCleared
  have hdirect := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka directComputePath
      (by simpa [Artifact.submissionArtifact] using hcodeWritten)
      hforkWritten
      (run_directCompute (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) accumulator count baseSize
        e m baseOff rest (by omega) hbase hstackWritten hpcWritten hrunWritten)
      hrunWritten hnpWritten
  have hstackComputed :
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).stack =
        UInt256.ofNat (basePrefix s accumulator count baseSize
          (baseTail baseSize e m baseOff rest)) ::
          frame accumulator count (baseTail baseSize e m baseOff rest) := by
    simp [baseDirectOf, basePrefix, hstackWritten]
  have hpcComputed :
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).pc =
        UInt256.ofNat 1665 := by
    simp [baseDirectOf]
  have hcodeComputed :
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).executionEnv.code =
        submissionBytecode := by
    simpa [baseDirectOf] using hcodeWritten
  have hforkComputed :
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).fork = .Osaka := by
    simpa [baseDirectOf, State.fork] using hforkWritten
  have hrunComputed :
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).halt =
        .Running := by
    simpa [baseDirectOf] using hrunWritten
  have hnpComputed : Precompile.isPrecompileWithConfig
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).executionEnv.precompileConfig
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).executionEnv.fork
      (baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).executionEnv.codeAddr
      = false := by
    simpa [baseDirectOf, State.fork] using hnpWritten
  have hcall := Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka loadCallPath
      (by simpa [Artifact.submissionArtifact] using hcodeComputed)
      hforkComputed
      (run_loadCall (baseDirectOf (baseWritten (afterClearDouble s accumulator
        count (baseTail baseSize e m baseOff rest))) count baseSize)
        accumulator count baseSize e m baseOff
        (basePrefix s accumulator count baseSize
          (baseTail baseSize e m baseOff rest)) rest
        (by omega) hstackComputed hpcComputed hcodeComputed hrunComputed)
      hrunComputed hnpComputed
  have hdirectLe : basePrefix s accumulator count baseSize
      (baseTail baseSize e m baseOff rest) ≤ baseSize :=
    directValue_le _ count baseSize
  have hcapLoad :
      ((baseDirectOf (baseWritten (afterClearDouble s accumulator count
        (baseTail baseSize e m baseOff rest))) count baseSize).stack).length
      < 1000 := by
    rw [hstackComputed]
    simp [frame, htail]
    omega
  have hload := BigLoad.gasSteps_loadBigEndian
    (baseDirectOf (baseWritten (afterClearDouble s accumulator count
      (baseTail baseSize e m baseOff rest))) count baseSize)
    baseOff
    (basePrefix s accumulator count baseSize
      (baseTail baseSize e m baseOff rest))
    (UInt256.ofNat 1024) (UInt256.ofNat 1677)
    ((baseDirectOf (baseWritten (afterClearDouble s accumulator count
      (baseTail baseSize e m baseOff rest))) count baseSize).stack)
    hcapLoad hoff (by omega) (by omega)
    hcodeComputed hforkComputed hrunComputed hnpComputed
    (by
      have h : (UInt256.ofNat 1677).toNat = 1677 := by decide
      rw [h]; exact jump1677)
  exact Challenge.EvmProof.GasSteps.cast
    (hstub.trans (htoClear.trans (hclear.trans (hmstore.trans
      (hdirect.trans (hcall.trans hload))))))
    rfl
    (by rw [baseLoopEntry]; rw [hstackComputed])

end Challenge.Modexp.Submission.Proofs.Bytecode.BigBase
