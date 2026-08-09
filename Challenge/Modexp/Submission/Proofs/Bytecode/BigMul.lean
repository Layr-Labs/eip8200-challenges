import Challenge.Modexp.Submission.Proofs.Bytecode.BigHelpers
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Size
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
/-!
# Certified multi-limb modular multiplication

`mulModBig` is a *flat* double-and-add: a scan phase computes a tight bound
`total` on the bit length of the multiplier, and a single loop then walks bit
indices `0 ≤ K < total`, adding the running power on a set bit and doubling it
every step.  Only `total` iterations run, and a clear bit costs one masked add
instead of two, so the loop is value-dependent.

The corresponding bytes live past the end of the compiled program: the region
`[0x0136, 0x01b2)` that the compiler emitted for `mulModBig` was replaced, in
place and at exactly the same byte *and* instruction count, by
`JUMPDEST; PUSH2 <appended>; JUMP` plus unreachable filler.  Every instruction
index below 1069 therefore still denotes the same instruction it did before.
-/

namespace Challenge.Modexp.Submission.Proofs.Bytecode.BigMul

open EvmSemantics
open EvmSemantics.EVM
open YulEvmCompiler
open Challenge.Modexp.Submission.Proofs.Bytecode

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

/-! ## Basic blocks of the appended `mulModBig` -/

/-- Entry stub at pc 310 jumps to the appended body, which pushes `total := 0`
and `i := 0` and falls into the scan loop head. -/
def mulEntryPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 265 .JUMPDEST, pushAt 266 2 1460, opAt 267 .JUMP,
   opAt 1069 .JUMPDEST, pushAt 1070 0 0, pushAt 1071 0 0]

/-- `i < count` test at the head of the scan loop. -/
def scanGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1072 .JUMPDEST, opAt 1073 (.Dup ⟨6, by decide⟩),
   opAt 1074 (.Dup ⟨1, by decide⟩), opAt 1075 .LT, opAt 1076 .ISZERO,
   pushAt 1077 2 1519, opAt 1078 .JUMPI]

/-- Load limb `i` and test it against zero. -/
def scanLoadPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1079 (.Dup ⟨0, by decide⟩), pushAt 1080 1 5, opAt 1081 .SHL,
   opAt 1082 (.Dup ⟨4, by decide⟩), opAt 1083 .ADD, opAt 1084 .MLOAD,
   opAt 1085 (.Dup ⟨0, by decide⟩), opAt 1086 .ISZERO,
   pushAt 1087 2 1510, opAt 1088 .JUMPI]

/-- A nonzero limb starts the bit-length loop at `width := 0`. -/
def bitlenSetupPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [pushAt 1089 0 0]

/-- `shr(width, w) ≠ 0` test at the head of the bit-length loop. -/
def bitlenGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1090 .JUMPDEST, opAt 1091 (.Dup ⟨1, by decide⟩),
   opAt 1092 (.Dup ⟨1, by decide⟩), opAt 1093 .SHR, opAt 1094 .ISZERO,
   pushAt 1095 2 1502, opAt 1096 .JUMPI]

/-- `width := width + 1`, back to the bit-length head. -/
def bitlenNextPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [pushAt 1097 1 1, opAt 1098 .ADD, pushAt 1099 2 1486, opAt 1100 .JUMP]

/-- `total := (i <<< 8) + width`, then fall into the scan increment. -/
def bitlenDonePath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1101 .JUMPDEST, opAt 1102 (.Dup ⟨2, by decide⟩), pushAt 1103 1 8,
   opAt 1104 .SHL, opAt 1105 .ADD, opAt 1106 (.Swap ⟨2, by decide⟩),
   opAt 1107 .POP]

/-- Drop the loaded limb, `i := i + 1`, back to the scan head. -/
def scanNextPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1108 .JUMPDEST, opAt 1109 .POP, pushAt 1110 1 1, opAt 1111 .ADD,
   pushAt 1112 2 1463, opAt 1113 .JUMP]

/-- Scan finished: drop `i` and call `clearLimbs(out, count)`. -/
def scanDonePath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1114 .JUMPDEST, opAt 1115 .POP, pushAt 1116 2 1530,
   opAt 1117 (.Dup ⟨6, by decide⟩), opAt 1118 (.Dup ⟨5, by decide⟩),
   pushAt 1119 2 19, opAt 1120 .JUMP]

/-- Call `copyLimbs(0x1000, a, count)`. -/
def mulToCopyPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1121 .JUMPDEST, pushAt 1122 2 1543, opAt 1123 (.Dup ⟨6, by decide⟩),
   opAt 1124 (.Dup ⟨3, by decide⟩), pushAt 1125 2 4096, pushAt 1126 2 58,
   opAt 1127 .JUMP]

/-- `K := 0`, falling into the flat loop head. -/
def mulSetupPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1128 .JUMPDEST, pushAt 1129 0 0]

/-- `K < total` test at the head of the flat loop. -/
def flatGuardPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1130 .JUMPDEST, opAt 1131 (.Dup ⟨1, by decide⟩),
   opAt 1132 (.Dup ⟨1, by decide⟩), opAt 1133 .LT, opAt 1134 .ISZERO,
   pushAt 1135 2 1618, opAt 1136 .JUMPI]

/-- Read bit `K` of the multiplier and branch on it. -/
def flatBitPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1137 (.Dup ⟨0, by decide⟩), pushAt 1138 1 8, opAt 1139 .SHR,
   pushAt 1140 1 5, opAt 1141 .SHL, opAt 1142 (.Dup ⟨4, by decide⟩),
   opAt 1143 .ADD, opAt 1144 .MLOAD, pushAt 1145 1 255,
   opAt 1146 (.Dup ⟨2, by decide⟩), opAt 1147 .AND, opAt 1148 .SHR,
   pushAt 1149 1 1, opAt 1150 .AND, opAt 1151 .ISZERO,
   pushAt 1152 2 1592, opAt 1153 .JUMPI]

/-- Set bit: `addMaskedMod(out, 0x1000, 1, modulus, count)`. -/
def flatAddPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [pushAt 1154 2 1592, opAt 1155 (.Dup ⟨7, by decide⟩),
   opAt 1156 (.Dup ⟨7, by decide⟩), pushAt 1157 1 1, pushAt 1158 2 4096,
   opAt 1159 (.Dup ⟨9, by decide⟩), pushAt 1160 2 104, opAt 1161 .JUMP]

/-- Every step: `addMaskedMod(0x1000, 0x1000, 1, modulus, count)`. -/
def flatDoublePath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1162 .JUMPDEST, pushAt 1163 2 1610, opAt 1164 (.Dup ⟨7, by decide⟩),
   opAt 1165 (.Dup ⟨7, by decide⟩), pushAt 1166 1 1, pushAt 1167 2 4096,
   pushAt 1168 2 4096, pushAt 1169 2 104, opAt 1170 .JUMP]

/-- `K := K + 1`, back to the flat loop head. -/
def flatNextPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1171 .JUMPDEST, pushAt 1172 1 1, opAt 1173 .ADD,
   pushAt 1174 2 1545, opAt 1175 .JUMP]

/-- Drop the seven locals and return. -/
def mulExitPath :
    List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka) :=
  [opAt 1176 .JUMPDEST, opAt 1177 .POP, opAt 1178 .POP, opAt 1179 .POP,
   opAt 1180 .POP, opAt 1181 .POP, opAt 1182 .POP, opAt 1183 .POP,
   opAt 1184 .JUMP]

/-! ## Program counters and jump destinations -/

@[simp] private theorem mulStubPCs (i : Nat) (hi : 265 ≤ i) (hii : i ≤ 267) :
    Artifact.submissionArtifact.instructionPC i = ([310,311,314])[i - 265]! := by
  interval_cases i <;> decide

@[simp] private theorem listGetZero {α : Type} (head default : α)
    (tail : List α) :
    (head :: tail)[0]?.getD default = head := by
  rfl

@[simp] private theorem listGetElemZero {α : Type} (head : α)
    (tail : List α) :
    (head :: tail)[0]? = some head := by
  rfl

@[simp] private theorem scanPCs (i : Nat) (hi : 1069 ≤ i) (hii : i ≤ 1099) :
    Artifact.submissionArtifact.instructionPC i =
      ([1460,1461,1462,1463,1464,1465,1466,1467,1468,1471,1472,1473,1475,1476,
        1477,1478,1479,1480,1481,1484,1485,1486,1487,1488,1489,1490,1491,1494,
        1495,1497,1498])[i - 1069]! := by
  interval_cases i <;> decide

@[simp] private theorem scanTailPCs (i : Nat) (hi : 1100 ≤ i) (hii : i ≤ 1129) :
    Artifact.submissionArtifact.instructionPC i =
      ([1501,1502,1503,1504,1506,1507,1508,1509,1510,1511,1512,1514,1515,1518,
        1519,1520,1521,1524,1525,1526,1529,1530,1531,1534,1535,1536,1539,1542,
        1543,1544])[i - 1100]! := by
  interval_cases i <;> decide

@[simp] private theorem flatPCs (i : Nat) (hi : 1130 ≤ i) (hii : i ≤ 1159) :
    Artifact.submissionArtifact.instructionPC i =
      ([1545,1546,1547,1548,1549,1550,1553,1554,1555,1557,1558,1560,1561,1562,
        1563,1564,1566,1567,1568,1569,1571,1572,1573,1576,1577,1580,1581,1582,
        1584,1587])[i - 1130]! := by
  interval_cases i <;> decide

@[simp] private theorem flatTailPCs (i : Nat) (hi : 1160 ≤ i) (hii : i ≤ 1184) :
    Artifact.submissionArtifact.instructionPC i =
      ([1588,1591,1592,1593,1596,1597,1598,1600,1603,1606,1609,1610,1611,1613,
        1614,1617,1618,1619,1620,1621,1622,1623,1624,1625,1626])[i - 1160]! := by
  interval_cases i <;> decide

private theorem jump1460 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1460 = true :=
  Artifact.isValidJumpDest_index 1069 (by rfl)

private theorem jump1463 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1463 = true :=
  Artifact.isValidJumpDest_index 1072 (by rfl)

private theorem jump1486 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1486 = true :=
  Artifact.isValidJumpDest_index 1090 (by rfl)

private theorem jump1502 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1502 = true :=
  Artifact.isValidJumpDest_index 1101 (by rfl)

private theorem jump1510 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1510 = true :=
  Artifact.isValidJumpDest_index 1108 (by rfl)

private theorem jump1519 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1519 = true :=
  Artifact.isValidJumpDest_index 1114 (by rfl)

private theorem jump1530 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1530 = true :=
  Artifact.isValidJumpDest_index 1121 (by rfl)

private theorem jump1543 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1543 = true :=
  Artifact.isValidJumpDest_index 1128 (by rfl)

private theorem jump1545 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1545 = true :=
  Artifact.isValidJumpDest_index 1130 (by rfl)

private theorem jump1592 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1592 = true :=
  Artifact.isValidJumpDest_index 1162 (by rfl)

private theorem jump1610 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1610 = true :=
  Artifact.isValidJumpDest_index 1171 (by rfl)

private theorem jump1618 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 1618 = true :=
  Artifact.isValidJumpDest_index 1176 (by rfl)

private theorem jump19 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 19 = true :=
  Artifact.isValidJumpDest_index 15 (by rfl)

private theorem jump58 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 58 = true :=
  Artifact.isValidJumpDest_index 46 (by rfl)

private theorem jump104 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode 104 = true :=
  Artifact.isValidJumpDest_index 83 (by rfl)

/-! ## Addresses, words and bits, as the bytecode computes them -/

/-- Address of limb `i` of the multiplier: `add(shl(5, i), b)`. -/
def scanPtr (b : UInt256) (i : Nat) : UInt256 :=
  b + UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)

/-- Address of the limb holding bit `K`: `add(shl(5, shr(8, K)), b)`. -/
def flatPtr (b : UInt256) (k : Nat) : UInt256 :=
  b + UInt256.shiftLeft
    (UInt256.shiftRight (UInt256.ofNat k) (UInt256.ofNat 8)) (UInt256.ofNat 5)

/-- Limb `i` of the multiplier. -/
def scanWord (memory : ByteArray) (b : UInt256) (i : Nat) : UInt256 :=
  MachineState.readWord memory (scanPtr b i).toNat

/-- The limb holding bit `K` of the multiplier. -/
def flatWord (memory : ByteArray) (b : UInt256) (k : Nat) : UInt256 :=
  MachineState.readWord memory (flatPtr b k).toNat

/-- Bit `K` of the multiplier: `and(shr(and(K, 255), w), 1)`. -/
def flatBit (memory : ByteArray) (b : UInt256) (k : Nat) : UInt256 :=
  UInt256.land (UInt256.ofNat 1)
    (UInt256.shiftRight (flatWord memory b k)
      (UInt256.land (UInt256.ofNat k) (UInt256.ofNat 255)))

/-- The scan's running bound after `i` limbs. -/
def scanTotal (memory : ByteArray) (b : UInt256) : Nat → Nat
  | 0 => 0
  | i + 1 =>
      if (scanWord memory b i).toNat = 0 then scanTotal memory b i
      else (256 * i + (scanWord memory b i).toNat.size) % 2 ^ 256

/-- `ofNat` already reduces modulo the word size. -/
private theorem ofNat_mod (n : Nat) :
    UInt256.ofNat n = UInt256.ofNat (n % 2 ^ 256) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256))]

/-- Shifting left by eight commutes with the embedding even when it wraps. -/
private theorem shiftLeft_eight (i : Nat) :
    UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 8) =
      UInt256.ofNat (256 * i) := by
  have h8 : (UInt256.ofNat 8).toNat = 8 := by
    rw [Challenge.EvmProof.Word.word_toNat_ofNat]
    exact Nat.mod_eq_of_lt (by norm_num)
  have h256 : (2 : Nat) ^ 8 = 256 := by norm_num
  unfold UInt256.shiftLeft
  rw [if_neg (by rw [h8]; omega), h8,
    show UInt256.size = 2 ^ 256 from rfl, Nat.shiftLeft_eq]
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat, h256,
    Nat.mod_mod_of_dvd _ (dvd_refl (2 ^ 256)), Nat.mul_comm 256 i,
    Nat.mul_mod i 256 (2 ^ 256),
    Nat.mod_eq_of_lt (show 256 < 2 ^ 256 by norm_num)]

/-! ## States -/

def mulFrame (a b out modulus : UInt256) (count : Nat) (returnDest : UInt256)
    (rest : List UInt256) : List UInt256 :=
  [a, b, out, modulus, UInt256.ofNat count, returnDest] ++ rest

def mulEntry (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 310
           stack := mulFrame a b out modulus count returnDest rest }

/-- Effect of the single `MLOAD` in a scan iteration. -/
def scanLoaded (current : State) (b : UInt256) (i : Nat) : State :=
  { current with activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      current.activeWords.toNat (scanPtr b i).toNat 32) }

/-- The scan writes nothing; only memory activation grows. -/
def scanProgress (current : State) (b : UInt256) : Nat → State
  | 0 => current
  | i + 1 => scanLoaded (scanProgress current b i) b i

def scanLoop (current : State) (a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1463
                 stack := [UInt256.ofNat i, UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

def scanBody (current : State) (a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1472
                 stack := [UInt256.ofNat i, UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

/-- After the limb load and its zero test, both arms carry `[w, i, total]`. -/
def scanTested (current : State) (w a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1510
                 stack := [w, UInt256.ofNat i, UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

/-- A nonzero limb continues into the bit-length loop instead. -/
def scanNonzero (current : State) (w a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1485
                 stack := [w, UInt256.ofNat i, UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

def bitlenLoop (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1486
                 stack := [UInt256.ofNat width, w, UInt256.ofNat i,
                   UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

def bitlenDone (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1502
                 stack := [UInt256.ofNat width, w, UInt256.ofNat i,
                   UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

def scanExit (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1519
                 stack := [UInt256.ofNat count, UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

def mulAfterClear (s : State) (a b out modulus : UInt256) (count total : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  { s with pc := UInt256.ofNat 1530
           stack := [UInt256.ofNat total] ++
             mulFrame a b out modulus count returnDest rest
           memory := BigHelpers.clearMemory s.memory out count
           activeWords := BigHelpers.clearWords s.activeWords out count }

def mulAfterCopy (s : State) (a b out modulus : UInt256) (count total : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  let cleared := mulAfterClear s a b out modulus count total returnDest rest
  { cleared with
    pc := UInt256.ofNat 1543
    memory := BigHelpers.copyMemory cleared.memory (UInt256.ofNat 4096) a count
    activeWords := BigHelpers.copyWords cleared.activeWords
      (UInt256.ofNat 4096) a count }

def flatFrame (a b out modulus : UInt256) (count total k : Nat)
    (returnDest : UInt256) (rest : List UInt256) : List UInt256 :=
  [UInt256.ofNat k, UInt256.ofNat total] ++
    mulFrame a b out modulus count returnDest rest

def flatLoop (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1545
                 stack := flatFrame a b out modulus count total k returnDest rest }

def flatBody (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1554
                 stack := flatFrame a b out modulus count total k returnDest rest }

/-- Effect of the single `MLOAD` in a flat-loop iteration. -/
def flatLoaded (current : State) (b : UInt256) (k : Nat) : State :=
  { current with activeWords := UInt256.ofNat (MachineState.activeWordsAfter
      current.activeWords.toNat (flatPtr b k).toNat 32) }

/-- State at the doubling, reached either by the zero-bit branch or by the
masked add's return. -/
def flatAfterAdd (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  let loaded := flatLoaded current b k
  if (flatBit current.memory b k).toNat = 0 then
    { loaded with pc := UInt256.ofNat 1592
                  stack := flatFrame a b out modulus count total k returnDest rest }
  else
    BigHelpers.addReturned loaded out (UInt256.ofNat 4096) (UInt256.ofNat 1)
      modulus count (UInt256.ofNat 1592)
      (flatFrame a b out modulus count total k returnDest rest)

def flatAfterDouble (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  BigHelpers.addReturned
    (flatAfterAdd current a b out modulus count total k returnDest rest)
    (UInt256.ofNat 4096) (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
    (UInt256.ofNat 1610)
    (flatFrame a b out modulus count total k returnDest rest)

def flatProgress (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256) :
    Nat → State
  | 0 => current
  | k + 1 =>
      flatAfterDouble
        (flatProgress current a b out modulus count total returnDest rest k)
        a b out modulus count total k returnDest rest

def mulReturned (current : State) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := returnDest, stack := rest }

/-- Fall-through of the bit-length guard, just before `width := width + 1`. -/
def bitlenBody (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1495
                 stack := [UInt256.ofNat width, w, UInt256.ofNat i,
                   UInt256.ofNat total] ++
                   mulFrame a b out modulus count returnDest rest }

/-- Head of the doubling block; both bit branches arrive here. -/
def flatDblEntry (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1592
                 stack := flatFrame a b out modulus count total k returnDest rest }

/-- Head of the masked-add call, taken only on a set bit. -/
def flatAddCall (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1577
                 stack := flatFrame a b out modulus count total k returnDest rest }

/-- Head of the loop increment, reached from the doubling's return. -/
def flatIncEntry (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256)
    (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1610
                 stack := flatFrame a b out modulus count total k returnDest rest }

/-- Head of the epilogue that drops the seven locals. -/
def flatExit (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256) : State :=
  { current with pc := UInt256.ofNat 1618
                 stack := flatFrame a b out modulus count total total returnDest
                   rest }

/-! ## Straight-line block semantics -/

set_option linter.unusedSimpArgs false in
theorem run_mulEntry (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulEntryPath
      (mulEntry s a b out modulus count returnDest rest) =
    some (scanLoop s a b out modulus count 0 0 returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h1460 : (1460 : UInt256) = UInt256.ofNat 1460 := by decide
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1460 : UInt256).toNat = true := by
    rw [show (1460 : UInt256).toNat = 1460 by decide]
    exact jump1460
  simp (disch := omega) [mulEntryPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulEntry, scanLoop, mulFrame, mulStubPCs, scanPCs, hcode, hrun, hvalid,
    jump1460, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h1460, hzero]

set_option linter.unusedSimpArgs false in
theorem run_scanGuard (current : State) (a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256) (hi : i < count)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanGuardPath
      (scanLoop current a b out modulus count i total returnDest rest) =
    some (scanBody current a b out modulus count i total returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hi256 : i < 2 ^ 256 := hi.trans hcount
  have hlt : i % 2 ^ 256 < count % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hi256, Nat.mod_eq_of_lt hcount]
    exact hi
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (disch := omega) [scanGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scanLoop, scanBody, mulFrame, scanPCs, hrun, UInt256.lt, UInt256.isTrue,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero, Nat.add_assoc, hc, hi]

set_option linter.unusedSimpArgs false in
theorem run_scanFinishGuard (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hcount : count < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanGuardPath
      (scanLoop current a b out modulus count count total returnDest rest) =
    some (scanExit current a b out modulus count total returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h1519 : (1519 : UInt256) = UInt256.ofNat 1519 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1519 : UInt256).toNat = true := by
    rw [show (1519 : UInt256).toNat = 1519 by decide]
    exact jump1519
  simp (disch := omega) [scanGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scanLoop, scanExit, mulFrame, scanPCs, hcode, hrun, UInt256.lt,
    UInt256.isTrue, hzeroFalse, hvalid, jump1519,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1519]

set_option linter.unusedSimpArgs false in
theorem run_scanLoadZero (current : State) (a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hzero : (scanWord current.memory b i).toNat = 0)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanLoadPath
      (scanBody current a b out modulus count i total returnDest rest) =
    some (scanTested (scanLoaded current b i) (scanWord current.memory b i)
      a b out modulus count i total returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have h1510 : (1510 : UInt256) = UInt256.ofNat 1510 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1510 : UInt256).toNat = true := by
    rw [show (1510 : UInt256).toNat = 1510 by decide]
    exact jump1510
  simp only [scanWord, scanPtr, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow] at hzero
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [scanLoadPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      scanBody, scanTested, scanLoaded, scanWord, scanPtr, mulFrame, scanPCs, UInt256.isTrue,
      hcode, hrun, hfive, h1510, hvalid, jump1510, hzero,
      State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_scanLoadNonzero (current : State) (a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hnz : ¬(scanWord current.memory b i).toNat = 0)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanLoadPath
      (scanBody current a b out modulus count i total returnDest rest) =
    some (scanNonzero (scanLoaded current b i) (scanWord current.memory b i)
      a b out modulus count i total returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  simp only [scanWord, scanPtr, Challenge.EvmProof.Word.word_toNat_add,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.reducePow] at hnz
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [scanLoadPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      scanBody, scanNonzero, scanLoaded, scanWord, scanPtr, mulFrame, scanPCs, UInt256.isTrue,
      hrun, hfive, hnz, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_bitlenSetup (current : State) (w a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitlenSetupPath
      (scanNonzero current w a b out modulus count i total returnDest rest) =
    some (bitlenLoop current w a b out modulus count i total 0 returnDest
      rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (disch := omega) [bitlenSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scanNonzero, bitlenLoop, mulFrame, scanPCs, hrun,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc, hc, hzero]

set_option linter.unusedSimpArgs false in
theorem run_bitlenGuard (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (_hwidth : width < 256)
    (hnz : ¬(UInt256.shiftRight w (UInt256.ofNat width)).toNat = 0)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitlenGuardPath
      (bitlenLoop current w a b out modulus count i total width returnDest
        rest) =
    some (bitlenBody current w a b out modulus count i total width returnDest
      rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  simp (disch := omega) [bitlenGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitlenLoop, bitlenBody, mulFrame, UInt256.isTrue, scanPCs, hrun, hnz,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_bitlenFinishGuard (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (_hwidth : width < 2 ^ 256)
    (hz : (UInt256.shiftRight w (UInt256.ofNat width)).toNat = 0)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitlenGuardPath
      (bitlenLoop current w a b out modulus count i total width returnDest
        rest) =
    some (bitlenDone current w a b out modulus count i total width returnDest
      rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h1502 : (1502 : UInt256) = UInt256.ofNat 1502 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1502 : UInt256).toNat = true := by
    rw [show (1502 : UInt256).toNat = 1502 by decide]
    exact jump1502
  simp (disch := omega) [bitlenGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitlenLoop, bitlenDone, mulFrame, UInt256.isTrue, scanPCs, hcode, hrun, hz, hvalid,
    jump1502, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1502]

set_option linter.unusedSimpArgs false in
theorem run_bitlenNext (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitlenNextPath
      (bitlenBody current w a b out modulus count i total width returnDest
        rest) =
    some (bitlenLoop current w a b out modulus count i total (width + 1)
      returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hinc : (1 : UInt256) + UInt256.ofNat width = UInt256.ofNat (width + 1) := by
    have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
    rw [h1, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_comm]
  have h1486 : (1486 : UInt256) = UInt256.ofNat 1486 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1486 : UInt256).toNat = true := by
    rw [show (1486 : UInt256).toNat = 1486 by decide]
    exact jump1486
  simp (disch := omega) [bitlenNextPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitlenBody, bitlenLoop, mulFrame, scanPCs, hcode, hrun, hvalid, jump1486,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1486, Artifact.ofNat_one_add_comm, hinc]

set_option linter.unusedSimpArgs false in
theorem run_bitlenDone (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock bitlenDonePath
      (bitlenDone current w a b out modulus count i total width returnDest
        rest) =
    some (scanTested current w a b out modulus count i
      ((256 * i + width) % 2 ^ 256) returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have height : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have hshift := shiftLeft_eight i
  have hadd : UInt256.ofNat (256 * i) + UInt256.ofNat width =
      UInt256.ofNat ((256 * i + width) % 2 ^ 256) :=
    (Challenge.EvmProof.Word.ofNat_add_mod _ _).trans (ofNat_mod _)
  simp (disch := omega) [bitlenDonePath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    bitlenDone, scanTested, mulFrame, scanPCs, scanTailPCs, hrun, height,
    hshift, hadd, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod, Nat.mod_eq_of_lt,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_scanNext (current : State) (w a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanNextPath
      (scanTested current w a b out modulus count i total returnDest rest) =
    some (scanLoop current a b out modulus count (i + 1) total returnDest
      rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hinc : (1 : UInt256) + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
    have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
    rw [h1, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_comm]
  have h1463 : (1463 : UInt256) = UInt256.ofNat 1463 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1463 : UInt256).toNat = true := by
    rw [show (1463 : UInt256).toNat = 1463 by decide]
    exact jump1463
  simp (disch := omega) [scanNextPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scanTested, scanLoop, mulFrame, scanTailPCs, hcode, hrun, hvalid, jump1463,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1463, Artifact.ofNat_one_add_comm, hinc]

set_option linter.unusedSimpArgs false in
theorem run_scanDone (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock scanDonePath
      (scanExit current a b out modulus count total returnDest rest) =
    some (BigHelpers.clearEntry current out count (UInt256.ofNat 1530)
      ([UInt256.ofNat total] ++
        mulFrame a b out modulus count returnDest rest)) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h19 : (19 : UInt256) = UInt256.ofNat 19 := by decide
  have h1530 : (1530 : UInt256) = UInt256.ofNat 1530 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (19 : UInt256).toNat = true := by
    rw [show (19 : UInt256).toNat = 19 by decide]
    exact jump19
  simp (disch := omega) [scanDonePath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    scanExit, BigHelpers.clearEntry, mulFrame, scanTailPCs, hcode, hrun,
    hvalid, jump19, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h19, h1530]

set_option linter.unusedSimpArgs false in
theorem run_mulToCopy (s : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulToCopyPath
      (mulAfterClear s a b out modulus count total returnDest rest) =
    some (BigHelpers.copyEntry
      (mulAfterClear s a b out modulus count total returnDest rest)
      (UInt256.ofNat 4096) a count (UInt256.ofNat 1543)
      ([UInt256.ofNat total] ++
        mulFrame a b out modulus count returnDest rest)) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h58 : (58 : UInt256) = UInt256.ofNat 58 := by decide
  have h1543 : (1543 : UInt256) = UInt256.ofNat 1543 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (58 : UInt256).toNat = true := by
    rw [show (58 : UInt256).toNat = 58 by decide]
    exact jump58
  simp (disch := omega) [mulToCopyPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterClear, BigHelpers.copyEntry, mulFrame, scanTailPCs, hcode, hrun,
    hvalid, jump58, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h58, h1543, h4096]

set_option linter.unusedSimpArgs false in
theorem run_mulSetup (s : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (hrun : s.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulSetupPath
      (mulAfterCopy s a b out modulus count total returnDest rest) =
    some (flatLoop (mulAfterCopy s a b out modulus count total returnDest rest)
      a b out modulus count total 0 returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hzero : ({ val := 0 } : UInt256) = UInt256.ofNat 0 := by decide
  simp (disch := omega) [mulSetupPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    mulAfterCopy, mulAfterClear, flatLoop, flatFrame, mulFrame, scanTailPCs,
    hrun, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.add_assoc, hc, hzero]

set_option linter.unusedSimpArgs false in
theorem run_flatGuard (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (htotal : total < 2 ^ 256) (hk : k < total)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatGuardPath
      (flatLoop current a b out modulus count total k returnDest rest) =
    some (flatBody current a b out modulus count total k returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hk256 : k < 2 ^ 256 := hk.trans htotal
  have hlt : k % 2 ^ 256 < total % 2 ^ 256 := by
    rw [Nat.mod_eq_of_lt hk256, Nat.mod_eq_of_lt htotal]
    exact hk
  have honeIsZero : (UInt256.ofNat 1).isZero.toNat = 0 := by decide
  simp (disch := omega) [flatGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatLoop, flatBody, flatFrame, mulFrame, flatPCs, hrun, UInt256.lt,
    UInt256.isTrue, Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    hlt, honeIsZero, Nat.add_assoc, hc, hk]

set_option linter.unusedSimpArgs false in
theorem run_flatFinishGuard (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000) (htotal : total < 2 ^ 256)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatGuardPath
      (flatLoop current a b out modulus count total total returnDest rest) =
    some (flatExit current a b out modulus count total returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h1618 : (1618 : UInt256) = UInt256.ofNat 1618 := by decide
  have hzeroFalse : ¬(UInt256.ofNat 0).isZero.toNat = 0 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1618 : UInt256).toNat = true := by
    rw [show (1618 : UInt256).toNat = 1618 by decide]
    exact jump1618
  simp (disch := omega) [flatGuardPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatLoop, flatExit, flatFrame, mulFrame, flatPCs, hcode, hrun, UInt256.lt,
    UInt256.isTrue, hzeroFalse, hvalid, jump1618,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1618]

set_option linter.unusedSimpArgs false in
theorem run_flatBitZero (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hbit : (flatBit current.memory b k).toNat = 0)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatBitPath
      (flatBody current a b out modulus count total k returnDest rest) =
    some (flatDblEntry (flatLoaded current b k) a b out modulus count total k
      returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have height : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have h1592 : (1592 : UInt256) = UInt256.ofNat 1592 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1592 : UInt256).toNat = true := by
    rw [show (1592 : UInt256).toNat = 1592 by decide]
    exact jump1592
  simp [flatBit, flatWord, flatPtr] at hbit
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [flatBitPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      flatBody, flatDblEntry, flatLoaded, flatBit, flatWord, flatPtr,
      UInt256.isTrue,
      flatFrame, mulFrame, flatPCs, flatTailPCs, hcode, hrun, hfive, height,
      h255, hone, h1592, hvalid, jump1592, hbit, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_flatBitOne (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hbit : ¬(flatBit current.memory b k).toNat = 0)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatBitPath
      (flatBody current a b out modulus count total k returnDest rest) =
    some (flatAddCall (flatLoaded current b k) a b out modulus count total k
      returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hfive : (5 : UInt256) = UInt256.ofNat 5 := by decide
  have height : (8 : UInt256) = UInt256.ofNat 8 := by decide
  have h255 : (255 : UInt256) = UInt256.ofNat 255 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  simp [flatBit, flatWord, flatPtr] at hbit
  simp (config := { maxSteps := 400000 }) (disch := omega)
    [flatBitPath, opAt, pushAt, wfOp,
      Challenge.EvmProof.Stepper.runLocatedBlock,
      Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
      flatBody, flatAddCall, flatLoaded, flatBit, flatWord, flatPtr,
      UInt256.isTrue,
      flatFrame, mulFrame, flatPCs, flatTailPCs, hrun, hfive, height,
      h255, hone, hbit, State.activeWordsAfterUInt256,
      Challenge.EvmProof.Word.succ_ofNat_mod,
      Challenge.EvmProof.Word.ofNat_add_mod,
      Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
      List.exchange, Nat.add_assoc, hc]

set_option linter.unusedSimpArgs false in
theorem run_flatAdd (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatAddPath
      (flatAddCall current a b out modulus count total k returnDest rest) =
    some (BigHelpers.addEntry current out (UInt256.ofNat 4096)
      (UInt256.ofNat 1) modulus count (UInt256.ofNat 1592)
      (flatFrame a b out modulus count total k returnDest rest)) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h1592 : (1592 : UInt256) = UInt256.ofNat 1592 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (disch := omega) [flatAddPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatAddCall, BigHelpers.addEntry, flatFrame, mulFrame, flatPCs,
    flatTailPCs, hcode, hrun, hvalid, jump104,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h104, h1592, h4096, hone]

set_option linter.unusedSimpArgs false in
theorem run_flatDouble (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatDoublePath
      (flatDblEntry current a b out modulus count total k returnDest rest) =
    some (BigHelpers.addEntry current (UInt256.ofNat 4096)
      (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
      (UInt256.ofNat 1610)
      (flatFrame a b out modulus count total k returnDest rest)) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have h104 : (104 : UInt256) = UInt256.ofNat 104 := by decide
  have h1610 : (1610 : UInt256) = UInt256.ofNat 1610 := by decide
  have h4096 : (4096 : UInt256) = UInt256.ofNat 4096 := by decide
  have hone : (1 : UInt256) = UInt256.ofNat 1 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (104 : UInt256).toNat = true := by
    rw [show (104 : UInt256).toNat = 104 by decide]
    exact jump104
  simp (disch := omega) [flatDoublePath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatDblEntry, BigHelpers.addEntry, flatFrame, mulFrame, flatTailPCs,
    hcode, hrun, hvalid, jump104,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, List.exchange, Nat.add_assoc,
    hc, h104, h1610, h4096, hone]

set_option linter.unusedSimpArgs false in
theorem run_flatNext (current : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running) :
    Challenge.EvmProof.Stepper.runLocatedBlock flatNextPath
      (flatIncEntry current a b out modulus count total k returnDest rest) =
    some (flatLoop current a b out modulus count total (k + 1) returnDest
      rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  have hinc : (1 : UInt256) + UInt256.ofNat k = UInt256.ofNat (k + 1) := by
    have h1 : (1 : UInt256) = UInt256.ofNat 1 := by decide
    rw [h1, Challenge.EvmProof.Word.ofNat_add_mod, Nat.add_comm]
  have h1545 : (1545 : UInt256) = UInt256.ofNat 1545 := by decide
  have hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (1545 : UInt256).toNat = true := by
    rw [show (1545 : UInt256).toNat = 1545 by decide]
    exact jump1545
  simp (disch := omega) [flatNextPath, opAt, pushAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatIncEntry, flatLoop, flatFrame, mulFrame, flatTailPCs, hcode, hrun,
    hvalid, jump1545,
    Challenge.EvmProof.Word.succ_ofNat_mod,
    Challenge.EvmProof.Word.ofNat_add_mod,
    Challenge.EvmProof.Word.word_toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hc, h1545, Artifact.ofNat_one_add_comm, hinc]

set_option linter.unusedSimpArgs false in
theorem run_mulExit (current : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 1000)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hrun : current.halt = .Running)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.Stepper.runLocatedBlock mulExitPath
      (flatExit current a b out modulus count total returnDest rest) =
    some (mulReturned current returnDest rest) := by
  have hc : ∀ n ≤ 20, rest.length + n < 1024 := by omega
  simp (disch := omega) [mulExitPath, opAt, wfOp,
    Challenge.EvmProof.Stepper.runLocatedBlock,
    Challenge.EvmProof.Stepper.runLocated, Challenge.EvmProof.Stepper.runInstr,
    flatExit, flatFrame, mulFrame, mulReturned, flatTailPCs, hcode, hrun,
    hvalid, Challenge.EvmProof.Word.succ_ofNat_mod, List.exchange,
    Nat.add_assoc, hc]

/-! ## Bit length of a loaded limb

The bit-length loop increments `width` while `shr(width, w)` is nonzero, so it
stops at exactly `Nat.size w.toNat`. -/

private theorem toNat_lt (w : UInt256) : w.toNat < 2 ^ 256 := w.val.isLt

private theorem size_le_256 (w : UInt256) : w.toNat.size ≤ 256 :=
  Nat.size_le.mpr (toNat_lt w)

private theorem shiftRight_ne_zero_of_lt_size (w : UInt256) (k : Nat)
    (hk : k < w.toNat.size) :
    ¬(UInt256.shiftRight w (UInt256.ofNat k)).toNat = 0 := by
  have hk256 : k < 256 := Nat.lt_of_lt_of_le hk (size_le_256 w)
  rw [Challenge.EvmProof.Word.shiftRight_toNat w hk256, Nat.shiftRight_eq_div_pow]
  have h2 : 2 ^ k ≤ w.toNat := Nat.lt_size.mp hk
  have hpos : 0 < w.toNat / 2 ^ k :=
    Nat.div_pos h2 (by positivity)
  omega

private theorem shiftRight_size_eq_zero (w : UInt256) :
    (UInt256.shiftRight w (UInt256.ofNat w.toNat.size)).toNat = 0 := by
  rcases Nat.lt_or_ge w.toNat.size 256 with h | h
  · rw [Challenge.EvmProof.Word.shiftRight_toNat w h, Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (Nat.lt_size_self _)
  · have h256 : w.toNat.size = 256 := Nat.le_antisymm (size_le_256 w) h
    have hge : (UInt256.ofNat 256).toNat ≥ 256 := by
      simp [Challenge.EvmProof.Word.word_toNat_ofNat]
    rw [h256]
    unfold UInt256.shiftRight
    rw [if_pos hge]
    rfl

/-! ## State-function preservation -/

@[simp] theorem scanProgress_memory (current : State) (b : UInt256) (i : Nat) :
    (scanProgress current b i).memory = current.memory := by
  induction i with
  | zero => rfl
  | succ i ih => simp [scanProgress, scanLoaded, ih]

@[simp] theorem scanProgress_executionEnv (current : State) (b : UInt256)
    (i : Nat) :
    (scanProgress current b i).executionEnv = current.executionEnv := by
  induction i with
  | zero => rfl
  | succ i ih => simp [scanProgress, scanLoaded, ih]

@[simp] theorem scanProgress_halt (current : State) (b : UInt256) (i : Nat) :
    (scanProgress current b i).halt = current.halt := by
  induction i with
  | zero => rfl
  | succ i ih => simp [scanProgress, scanLoaded, ih]

@[simp] theorem flatProgress_executionEnv (current : State)
    (a b out modulus : UInt256) (count total : Nat) (returnDest : UInt256)
    (rest : List UInt256) (k : Nat) :
    (flatProgress current a b out modulus count total returnDest rest k).executionEnv =
      current.executionEnv := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [flatProgress, flatAfterDouble, BigHelpers.addReturned,
        flatAfterAdd]
      split <;> simp [flatLoaded, ih]

@[simp] theorem flatProgress_halt (current : State)
    (a b out modulus : UInt256) (count total : Nat) (returnDest : UInt256)
    (rest : List UInt256) (k : Nat) :
    (flatProgress current a b out modulus count total returnDest rest k).halt =
      current.halt := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [flatProgress, flatAfterDouble, BigHelpers.addReturned,
        flatAfterAdd]
      split <;> simp [flatLoaded, ih]

/-! ## Gas traces -/

private def sound (path : List (Challenge.EvmProof.Stepper.Located
      Artifact.submissionArtifact .Osaka)) {s t : State}
    (hres : Challenge.EvmProof.Stepper.runLocatedBlock path s = some t)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps s t :=
  Challenge.EvmProof.Stepper.runLocatedBlock_sound
    Artifact.submissionArtifact .Osaka path hcode hfork hres hrun hnp

def gasSteps_bitlenIteration (current : State) (w a b out modulus : UInt256)
    (count i total width : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hwidth : width < w.toNat.size)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig current.executionEnv.precompileConfig
      current.executionEnv.fork current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitlenLoop current w a b out modulus count i total width returnDest rest)
      (bitlenLoop current w a b out modulus count i total (width + 1) returnDest
        rest) :=
  (sound bitlenGuardPath
      (run_bitlenGuard current w a b out modulus count i total width returnDest
        rest (by omega)
        (Nat.lt_of_lt_of_le hwidth (size_le_256 w))
        (shiftRight_ne_zero_of_lt_size w width hwidth)
        (by simpa [bitlenLoop] using hrun))
      (by simpa [bitlenLoop, Artifact.submissionArtifact] using hcode)
      (by simpa [bitlenLoop, State.fork] using hfork)
      (by simpa [bitlenLoop] using hrun)
      (by simpa [bitlenLoop, State.fork] using hnp)).trans
    (sound bitlenNextPath
      (run_bitlenNext current w a b out modulus count i total width returnDest
        rest (by omega) (by simpa [bitlenBody] using hcode)
        (by simpa [bitlenBody] using hrun))
      (by simpa [bitlenBody, Artifact.submissionArtifact] using hcode)
      (by simpa [bitlenBody, State.fork] using hfork)
      (by simpa [bitlenBody] using hrun)
      (by simpa [bitlenBody, State.fork] using hnp))

def gasSteps_bitlenLoop (current : State) (w a b out modulus : UInt256)
    (count i total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980)
    (hcode : current.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : current.fork = .Osaka) (hrun : current.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig current.executionEnv.precompileConfig
      current.executionEnv.fork current.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (bitlenLoop current w a b out modulus count i total 0 returnDest rest)
      (bitlenLoop current w a b out modulus count i total w.toNat.size
        returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded w.toNat.size fun width hwidth =>
    gasSteps_bitlenIteration current w a b out modulus count i total width
      returnDest rest hcap hwidth hcode hfork hrun hnp

/-- One scan iteration: read limb `i` and, when it is nonzero, replace the
running bound with `(i <<< 8) + bitlen`. -/
def gasSteps_scanIteration (s : State) (a b out modulus : UInt256)
    (count i : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256) (hi : i < count)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanLoop (scanProgress s b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest)
      (scanLoop (scanProgress s b (i + 1)) a b out modulus count (i + 1)
        (scanTotal s.memory b (i + 1)) returnDest rest) := by
  have hmem : (scanProgress s b i).memory = s.memory := scanProgress_memory s b i
  have hcode' : (scanProgress s b i).executionEnv.code =
      Challenge.Modexp.submissionBytecode := by simpa using hcode
  have hfork' : (scanProgress s b i).fork = .Osaka := by
    simpa [State.fork] using hfork
  have hrun' : (scanProgress s b i).halt = .Running := by simpa using hrun
  have hnp' : Precompile.isPrecompileWithConfig
      (scanProgress s b i).executionEnv.precompileConfig
      (scanProgress s b i).executionEnv.fork
      (scanProgress s b i).executionEnv.codeAddr = false := by
    simpa [State.fork] using hnp
  have hstep := sound scanGuardPath
    (run_scanGuard (scanProgress s b i) a b out modulus count i
      (scanTotal s.memory b i) returnDest rest (by omega) hcount hi
      (by simpa [scanLoop] using hrun'))
    (by simpa [scanLoop, Artifact.submissionArtifact] using hcode')
    (by simpa [scanLoop, State.fork] using hfork')
    (by simpa [scanLoop] using hrun')
    (by simpa [scanLoop, State.fork] using hnp')
  by_cases hw : (scanWord s.memory b i).toNat = 0
  · have hz : (scanWord (scanProgress s b i).memory b i).toNat = 0 := by
      rw [hmem]; exact hw
    have htotal : scanTotal s.memory b (i + 1) = scanTotal s.memory b i := by
      simp [scanTotal, hw]
    rw [htotal]
    refine hstep.trans ((sound scanLoadPath
      (run_scanLoadZero (scanProgress s b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest (by omega) hz
        (by simpa [scanBody] using hcode') (by simpa [scanBody] using hrun'))
      (by simpa [scanBody, Artifact.submissionArtifact] using hcode')
      (by simpa [scanBody, State.fork] using hfork')
      (by simpa [scanBody] using hrun')
      (by simpa [scanBody, State.fork] using hnp')).trans ?_)
    exact sound scanNextPath
      (run_scanNext (scanLoaded (scanProgress s b i) b i)
        (scanWord (scanProgress s b i).memory b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest (by omega)
        (by simpa [scanTested, scanLoaded] using hcode')
        (by simpa [scanTested, scanLoaded] using hrun'))
      (by simpa [scanTested, scanLoaded, Artifact.submissionArtifact] using hcode')
      (by simpa [scanTested, scanLoaded, State.fork] using hfork')
      (by simpa [scanTested, scanLoaded] using hrun')
      (by simpa [scanTested, scanLoaded, State.fork] using hnp')
  · have hnz : ¬(scanWord (scanProgress s b i).memory b i).toNat = 0 := by
      rw [hmem]; exact hw
    have hword : scanWord (scanProgress s b i).memory b i = scanWord s.memory b i := by
      rw [hmem]
    have htotal : scanTotal s.memory b (i + 1) =
        (256 * i + (scanWord s.memory b i).toNat.size) % 2 ^ 256 := by
      simp [scanTotal, hw]
    set loaded := scanLoaded (scanProgress s b i) b i with hloaded
    have hcodeL : loaded.executionEnv.code = Challenge.Modexp.submissionBytecode := by
      simpa [hloaded, scanLoaded] using hcode'
    have hforkL : loaded.fork = .Osaka := by
      simpa [hloaded, scanLoaded, State.fork] using hfork'
    have hrunL : loaded.halt = .Running := by simpa [hloaded, scanLoaded] using hrun'
    have hnpL : Precompile.isPrecompileWithConfig
        loaded.executionEnv.precompileConfig loaded.executionEnv.fork
        loaded.executionEnv.codeAddr = false := by
      simpa [hloaded, scanLoaded, State.fork] using hnp'
    rw [htotal]
    refine hstep.trans ((sound scanLoadPath
      (run_scanLoadNonzero (scanProgress s b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest (by omega) hnz
        (by simpa [scanBody] using hrun'))
      (by simpa [scanBody, Artifact.submissionArtifact] using hcode')
      (by simpa [scanBody, State.fork] using hfork')
      (by simpa [scanBody] using hrun')
      (by simpa [scanBody, State.fork] using hnp')).trans ?_)
    rw [hword] at *
    refine ((sound bitlenSetupPath
      (run_bitlenSetup loaded (scanWord s.memory b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest (by omega)
        (by simpa [scanNonzero] using hrunL))
      (by simpa [scanNonzero, Artifact.submissionArtifact] using hcodeL)
      (by simpa [scanNonzero, State.fork] using hforkL)
      (by simpa [scanNonzero] using hrunL)
      (by simpa [scanNonzero, State.fork] using hnpL)).trans
      ((gasSteps_bitlenLoop loaded (scanWord s.memory b i) a b out modulus count i
        (scanTotal s.memory b i) returnDest rest (by omega) hcodeL hforkL hrunL
        hnpL).trans ?_))
    refine ((sound bitlenGuardPath
      (run_bitlenFinishGuard loaded (scanWord s.memory b i) a b out modulus count
        i (scanTotal s.memory b i) (scanWord s.memory b i).toNat.size returnDest
        rest (by omega)
        (Nat.lt_of_le_of_lt (size_le_256 _) (by norm_num))
        (shiftRight_size_eq_zero _)
        (by simpa [bitlenLoop] using hcodeL)
        (by simpa [bitlenLoop] using hrunL))
      (by simpa [bitlenLoop, Artifact.submissionArtifact] using hcodeL)
      (by simpa [bitlenLoop, State.fork] using hforkL)
      (by simpa [bitlenLoop] using hrunL)
      (by simpa [bitlenLoop, State.fork] using hnpL)).trans
      ((sound bitlenDonePath
        (run_bitlenDone loaded (scanWord s.memory b i) a b out modulus count i
          (scanTotal s.memory b i) (scanWord s.memory b i).toNat.size returnDest
          rest (by omega) (by simpa [bitlenDone] using hrunL))
        (by simpa [bitlenDone, Artifact.submissionArtifact] using hcodeL)
        (by simpa [bitlenDone, State.fork] using hforkL)
        (by simpa [bitlenDone] using hrunL)
        (by simpa [bitlenDone, State.fork] using hnpL)).trans ?_))
    exact sound scanNextPath
      (run_scanNext loaded (scanWord s.memory b i) a b out modulus count i
        ((256 * i + (scanWord s.memory b i).toNat.size) % 2 ^ 256) returnDest
        rest (by omega) (by simpa [scanTested] using hcodeL)
        (by simpa [scanTested] using hrunL))
      (by simpa [scanTested, Artifact.submissionArtifact] using hcodeL)
      (by simpa [scanTested, State.fork] using hforkL)
      (by simpa [scanTested] using hrunL)
      (by simpa [scanTested, State.fork] using hnpL)

def gasSteps_scanLoop (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (scanLoop (scanProgress s b 0) a b out modulus count 0
        (scanTotal s.memory b 0) returnDest rest)
      (scanLoop (scanProgress s b count) a b out modulus count count
        (scanTotal s.memory b count) returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded count fun i hi =>
    gasSteps_scanIteration s a b out modulus count i returnDest rest hcap
      hcount hi hcode hfork hrun hnp

private theorem jumpWord1592 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1592).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1592 < 2 ^ 256)]
  exact jump1592

private theorem jumpWord1610 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1610).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1610 < 2 ^ 256)]
  exact jump1610

private theorem jumpWord1530 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1530).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1530 < 2 ^ 256)]
  exact jump1530

private theorem jumpWord1543 :
    Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      (UInt256.ofNat 1543).toNat = true := by
  rw [Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1543 < 2 ^ 256)]
  exact jump1543

set_option linter.unusedSimpArgs false in
/-- Clear bit: only the doubling runs. -/
def gasSteps_flatIterationZero (base : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (htotal : total < 2 ^ 256) (hk : k < total)
    (hbit : (flatBit (flatProgress base a b out modulus count total returnDest
      rest k).memory b k).toNat = 0)
    (hcode : base.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (flatLoop (flatProgress base a b out modulus count total returnDest rest k)
        a b out modulus count total k returnDest rest)
      (flatLoop (flatProgress base a b out modulus count total returnDest rest
        (k + 1)) a b out modulus count total (k + 1) returnDest rest) := by
  have hframe : (flatFrame a b out modulus count total k returnDest rest).length
      < 1000 := by simp [flatFrame, mulFrame]; omega
  set P := flatProgress base a b out modulus count total returnDest rest k with hP
  have hcodeP : P.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hP] using hcode
  have hforkP : P.fork = .Osaka := by simpa [hP, State.fork] using hfork
  have hrunP : P.halt = .Running := by simpa [hP] using hrun
  have hnpP : Precompile.isPrecompileWithConfig P.executionEnv.precompileConfig
      P.executionEnv.fork P.executionEnv.codeAddr = false := by
    simpa [hP, State.fork] using hnp
  have hstep : flatProgress base a b out modulus count total returnDest rest
      (k + 1) =
      BigHelpers.addReturned (flatLoaded P b k) (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest) := by
    show flatAfterDouble P a b out modulus count total k returnDest rest = _
    simp [flatAfterDouble, flatAfterAdd, hbit, BigHelpers.addReturned,
      flatLoaded]
  rw [hstep]
  refine (sound flatGuardPath
      (run_flatGuard P a b out modulus count total k returnDest rest
        (by omega) htotal hk (by simpa [flatLoop] using hrunP))
      (by simpa [flatLoop, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatLoop, State.fork] using hforkP)
      (by simpa [flatLoop] using hrunP)
      (by simpa [flatLoop, State.fork] using hnpP)).trans
    ((sound flatBitPath
      (run_flatBitZero P a b out modulus count total k returnDest rest
        (by omega) hbit (by simpa [flatBody] using hcodeP)
        (by simpa [flatBody] using hrunP))
      (by simpa [flatBody, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatBody, State.fork] using hforkP)
      (by simpa [flatBody] using hrunP)
      (by simpa [flatBody, State.fork] using hnpP)).trans ?_)
  refine ((sound flatDoublePath
      (run_flatDouble (flatLoaded P b k) a b out modulus count total k returnDest
        rest (by omega) (by simpa [flatDblEntry, flatLoaded] using hcodeP)
        (by simpa [flatDblEntry, flatLoaded] using hrunP))
      (by simpa [flatDblEntry, flatLoaded, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatDblEntry, flatLoaded, State.fork] using hforkP)
      (by simpa [flatDblEntry, flatLoaded] using hrunP)
      (by simpa [flatDblEntry, flatLoaded, State.fork] using hnpP)).trans
    ((BigHelpers.gasSteps_addMaskedMod (flatLoaded P b k) (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest) hframe hcount
        (by simpa [flatLoaded] using hcodeP)
        (by simpa [flatLoaded, State.fork] using hforkP)
        (by simpa [flatLoaded] using hrunP)
        (by simpa [flatLoaded, State.fork] using hnpP)
        jumpWord1610).trans ?_))
  exact sound flatNextPath
    (run_flatNext (BigHelpers.addReturned (flatLoaded P b k) (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest))
      a b out modulus count total k returnDest rest (by omega)
      (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded] using hcodeP)
      (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded] using hrunP))
    (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded,
      Artifact.submissionArtifact] using hcodeP)
    (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded, State.fork]
      using hforkP)
    (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded] using hrunP)
    (by simpa [flatIncEntry, BigHelpers.addReturned, flatLoaded, State.fork]
      using hnpP)

set_option linter.unusedSimpArgs false in
/-- Set bit: the masked add runs before the doubling. -/
def gasSteps_flatIterationOne (base : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (htotal : total < 2 ^ 256) (hk : k < total)
    (hbit : ¬(flatBit (flatProgress base a b out modulus count total returnDest
      rest k).memory b k).toNat = 0)
    (hcode : base.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (flatLoop (flatProgress base a b out modulus count total returnDest rest k)
        a b out modulus count total k returnDest rest)
      (flatLoop (flatProgress base a b out modulus count total returnDest rest
        (k + 1)) a b out modulus count total (k + 1) returnDest rest) := by
  have hframe : (flatFrame a b out modulus count total k returnDest rest).length
      < 1000 := by simp [flatFrame, mulFrame]; omega
  set P := flatProgress base a b out modulus count total returnDest rest k with hP
  have hcodeP : P.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hP] using hcode
  have hforkP : P.fork = .Osaka := by simpa [hP, State.fork] using hfork
  have hrunP : P.halt = .Running := by simpa [hP] using hrun
  have hnpP : Precompile.isPrecompileWithConfig P.executionEnv.precompileConfig
      P.executionEnv.fork P.executionEnv.codeAddr = false := by
    simpa [hP, State.fork] using hnp
  set added := BigHelpers.addReturned (flatLoaded P b k) out (UInt256.ofNat 4096)
    (UInt256.ofNat 1) modulus count (UInt256.ofNat 1592)
    (flatFrame a b out modulus count total k returnDest rest) with hadded
  have hstep : flatProgress base a b out modulus count total returnDest rest
      (k + 1) =
      BigHelpers.addReturned added (UInt256.ofNat 4096) (UInt256.ofNat 4096)
        (UInt256.ofNat 1) modulus count (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest) := by
    rw [hadded]
    show flatAfterDouble P a b out modulus count total k returnDest rest = _
    simp [flatAfterDouble, flatAfterAdd, hbit]
  have hcodeA : added.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hadded, BigHelpers.addReturned, flatLoaded] using hcodeP
  have hforkA : added.fork = .Osaka := by
    simpa [hadded, BigHelpers.addReturned, flatLoaded, State.fork] using hforkP
  have hrunA : added.halt = .Running := by
    simpa [hadded, BigHelpers.addReturned, flatLoaded] using hrunP
  have hnpA : Precompile.isPrecompileWithConfig
      added.executionEnv.precompileConfig added.executionEnv.fork
      added.executionEnv.codeAddr = false := by
    simpa [hadded, BigHelpers.addReturned, flatLoaded, State.fork] using hnpP
  rw [hstep]
  refine (sound flatGuardPath
      (run_flatGuard P a b out modulus count total k returnDest rest
        (by omega) htotal hk (by simpa [flatLoop] using hrunP))
      (by simpa [flatLoop, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatLoop, State.fork] using hforkP)
      (by simpa [flatLoop] using hrunP)
      (by simpa [flatLoop, State.fork] using hnpP)).trans
    ((sound flatBitPath
      (run_flatBitOne P a b out modulus count total k returnDest rest
        (by omega) hbit (by simpa [flatBody] using hrunP))
      (by simpa [flatBody, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatBody, State.fork] using hforkP)
      (by simpa [flatBody] using hrunP)
      (by simpa [flatBody, State.fork] using hnpP)).trans ?_)
  refine ((sound flatAddPath
      (run_flatAdd (flatLoaded P b k) a b out modulus count total k returnDest
        rest (by omega) (by simpa [flatAddCall, flatLoaded] using hcodeP)
        (by simpa [flatAddCall, flatLoaded] using hrunP))
      (by simpa [flatAddCall, flatLoaded, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatAddCall, flatLoaded, State.fork] using hforkP)
      (by simpa [flatAddCall, flatLoaded] using hrunP)
      (by simpa [flatAddCall, flatLoaded, State.fork] using hnpP)).trans
    ((BigHelpers.gasSteps_addMaskedMod (flatLoaded P b k) out (UInt256.ofNat 4096)
        (UInt256.ofNat 1) modulus count (UInt256.ofNat 1592)
        (flatFrame a b out modulus count total k returnDest rest) hframe hcount
        (by simpa [flatLoaded] using hcodeP)
        (by simpa [flatLoaded, State.fork] using hforkP)
        (by simpa [flatLoaded] using hrunP)
        (by simpa [flatLoaded, State.fork] using hnpP)
        jumpWord1592).trans ?_))
  refine ((sound flatDoublePath
      (run_flatDouble added a b out modulus count total k returnDest rest
        (by omega) (by simpa [flatDblEntry] using hcodeA)
        (by simpa [flatDblEntry] using hrunA))
      (by simpa [flatDblEntry, Artifact.submissionArtifact] using hcodeA)
      (by simpa [flatDblEntry, State.fork] using hforkA)
      (by simpa [flatDblEntry] using hrunA)
      (by simpa [flatDblEntry, State.fork] using hnpA)).trans
    ((BigHelpers.gasSteps_addMaskedMod added (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest) hframe hcount
        hcodeA hforkA hrunA hnpA jumpWord1610).trans ?_))
  exact sound flatNextPath
    (run_flatNext (BigHelpers.addReturned added (UInt256.ofNat 4096)
        (UInt256.ofNat 4096) (UInt256.ofNat 1) modulus count
        (UInt256.ofNat 1610)
        (flatFrame a b out modulus count total k returnDest rest))
      a b out modulus count total k returnDest rest (by omega)
      (by simpa [flatIncEntry, BigHelpers.addReturned] using hcodeA)
      (by simpa [flatIncEntry, BigHelpers.addReturned] using hrunA))
    (by simpa [flatIncEntry, BigHelpers.addReturned, Artifact.submissionArtifact]
      using hcodeA)
    (by simpa [flatIncEntry, BigHelpers.addReturned, State.fork] using hforkA)
    (by simpa [flatIncEntry, BigHelpers.addReturned] using hrunA)
    (by simpa [flatIncEntry, BigHelpers.addReturned, State.fork] using hnpA)

def gasSteps_flatIteration (base : State) (a b out modulus : UInt256)
    (count total k : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (htotal : total < 2 ^ 256) (hk : k < total)
    (hcode : base.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (flatLoop (flatProgress base a b out modulus count total returnDest rest k)
        a b out modulus count total k returnDest rest)
      (flatLoop (flatProgress base a b out modulus count total returnDest rest
        (k + 1)) a b out modulus count total (k + 1) returnDest rest) := by
  by_cases hbit : (flatBit (flatProgress base a b out modulus count total
      returnDest rest k).memory b k).toNat = 0
  · exact gasSteps_flatIterationZero base a b out modulus count total k
      returnDest rest hcap hcount htotal hk hbit hcode hfork hrun hnp
  · exact gasSteps_flatIterationOne base a b out modulus count total k
      returnDest rest hcap hcount htotal hk hbit hcode hfork hrun hnp

def gasSteps_flatLoop (base : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (htotal : total < 2 ^ 256)
    (hcode : base.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (flatLoop (flatProgress base a b out modulus count total returnDest rest 0)
        a b out modulus count total 0 returnDest rest)
      (flatLoop (flatProgress base a b out modulus count total returnDest rest
        total) a b out modulus count total total returnDest rest) :=
  Challenge.EvmProof.GasSteps.iterateBounded total fun k hk =>
    gasSteps_flatIteration base a b out modulus count total k returnDest rest
      hcap hcount htotal hk hcode hfork hrun hnp

theorem scanTotal_lt (memory : ByteArray) (b : UInt256) (i : Nat) :
    scanTotal memory b i < 2 ^ 256 := by
  induction i with
  | zero => norm_num [scanTotal]
  | succ i ih =>
      by_cases h : (scanWord memory b i).toNat = 0
      · simpa [scanTotal, h] using ih
      · simp only [scanTotal, if_neg h]
        exact Nat.mod_lt _ (by positivity)

/-- The bound the scan phase leaves in `total`. -/
def mulTotal (s : State) (b : UInt256) (count : Nat) : Nat :=
  scanTotal s.memory b count

/-- State after `clearLimbs(out, n)` and `copyLimbs(0x1000, a, n)`. -/
def mulCopied (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  mulAfterCopy (scanProgress s b count) a b out modulus count
    (mulTotal s b count) returnDest rest

/-- State reached when the flat loop finishes, before the epilogue. -/
def mulApplied (s : State) (a b out modulus : UInt256) (count : Nat)
    (returnDest : UInt256) (rest : List UInt256) : State :=
  flatProgress (mulCopied s a b out modulus count returnDest rest)
    a b out modulus count (mulTotal s b count) returnDest rest
    (mulTotal s b count)

set_option linter.unusedSimpArgs false in
def gasSteps_mulInitialize (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false) :
    Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (flatLoop (mulCopied s a b out modulus count returnDest rest)
        a b out modulus count (mulTotal s b count) 0 returnDest rest) := by
  set scanned := scanProgress s b count with hscanned
  set total := mulTotal s b count with htotalDef
  set saved := [UInt256.ofNat total] ++ mulFrame a b out modulus count
    returnDest rest with hsaved
  have hsavedLen : saved.length < 1017 := by
    simp [hsaved, mulFrame]; omega
  have hsavedLen' : saved.length < 1016 := by
    simp [hsaved, mulFrame]; omega
  have hcodeS : scanned.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hscanned] using hcode
  have hforkS : scanned.fork = .Osaka := by simpa [hscanned, State.fork] using hfork
  have hrunS : scanned.halt = .Running := by simpa [hscanned] using hrun
  have hnpS : Precompile.isPrecompileWithConfig
      scanned.executionEnv.precompileConfig scanned.executionEnv.fork
      scanned.executionEnv.codeAddr = false := by
    simpa [hscanned, State.fork] using hnp
  set cleared := mulAfterClear scanned a b out modulus count total returnDest rest
    with hcleared
  have hcodeC : cleared.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hcleared, mulAfterClear] using hcodeS
  have hforkC : cleared.fork = .Osaka := by
    simpa [hcleared, mulAfterClear, State.fork] using hforkS
  have hrunC : cleared.halt = .Running := by
    simpa [hcleared, mulAfterClear] using hrunS
  have hnpC : Precompile.isPrecompileWithConfig
      cleared.executionEnv.precompileConfig cleared.executionEnv.fork
      cleared.executionEnv.codeAddr = false := by
    simpa [hcleared, mulAfterClear, State.fork] using hnpS
  have hentry := sound mulEntryPath
    (run_mulEntry s a b out modulus count returnDest rest (by omega) hcode hrun)
    (by simpa [mulEntry, Artifact.submissionArtifact] using hcode)
    (by simpa [mulEntry, State.fork] using hfork)
    (by simpa [mulEntry] using hrun)
    (by simpa [mulEntry, State.fork] using hnp)
  have hscan := gasSteps_scanLoop s a b out modulus count returnDest rest hcap
    hcount hcode hfork hrun hnp
  have hexit := sound scanGuardPath
    (run_scanFinishGuard scanned a b out modulus count total returnDest rest
      (by omega) hcount (by simpa [scanLoop] using hcodeS)
      (by simpa [scanLoop] using hrunS))
    (by simpa [scanLoop, Artifact.submissionArtifact] using hcodeS)
    (by simpa [scanLoop, State.fork] using hforkS)
    (by simpa [scanLoop] using hrunS)
    (by simpa [scanLoop, State.fork] using hnpS)
  have hdone := sound scanDonePath
    (run_scanDone scanned a b out modulus count total returnDest rest
      (by omega) (by simpa [scanExit] using hcodeS)
      (by simpa [scanExit] using hrunS))
    (by simpa [scanExit, Artifact.submissionArtifact] using hcodeS)
    (by simpa [scanExit, State.fork] using hforkS)
    (by simpa [scanExit] using hrunS)
    (by simpa [scanExit, State.fork] using hnpS)
  have hclear : Challenge.EvmProof.GasSteps
      (BigHelpers.clearEntry scanned out count (UInt256.ofNat 1530) saved)
      cleared :=
    Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_clear scanned out count (UInt256.ofNat 1530) saved
        hsavedLen hcount hcodeS hforkS hrunS hnpS jumpWord1530)
      rfl (by simp [hcleared, hsaved, mulAfterClear, BigHelpers.clearReturned])
  have htocopy := sound mulToCopyPath
    (run_mulToCopy scanned a b out modulus count total returnDest rest
      (by omega) (by simpa [mulAfterClear] using hcodeS)
      (by simpa [mulAfterClear] using hrunS))
    (by simpa [hcleared, mulAfterClear, Artifact.submissionArtifact] using hcodeS)
    (by simpa [hcleared, mulAfterClear, State.fork] using hforkS)
    (by simpa [hcleared, mulAfterClear] using hrunS)
    (by simpa [hcleared, mulAfterClear, State.fork] using hnpS)
  have hcopy : Challenge.EvmProof.GasSteps
      (BigHelpers.copyEntry cleared (UInt256.ofNat 4096) a count
        (UInt256.ofNat 1543) saved)
      (mulAfterCopy scanned a b out modulus count total returnDest rest) :=
    Challenge.EvmProof.GasSteps.cast
      (BigHelpers.gasSteps_copy cleared (UInt256.ofNat 4096) a count
        (UInt256.ofNat 1543) saved hsavedLen' hcount hcodeC hforkC hrunC hnpC
        jumpWord1543)
      rfl (by simp [hcleared, hsaved, mulAfterCopy, mulAfterClear,
        BigHelpers.copyReturned])
  have hsetup := sound mulSetupPath
    (run_mulSetup scanned a b out modulus count total returnDest rest (by omega)
      (by simpa [mulAfterCopy, mulAfterClear] using hrunS))
    (by simpa [mulAfterCopy, mulAfterClear, Artifact.submissionArtifact] using hcodeS)
    (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hforkS)
    (by simpa [mulAfterCopy, mulAfterClear] using hrunS)
    (by simpa [mulAfterCopy, mulAfterClear, State.fork] using hnpS)
  exact hentry.trans (hscan.trans (hexit.trans (hdone.trans
    (hclear.trans (htocopy.trans (hcopy.trans hsetup))))))

def gasSteps_mulFinish (base : State) (a b out modulus : UInt256)
    (count total : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (htotal : total < 2 ^ 256)
    (hcode : base.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : base.fork = .Osaka) (hrun : base.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig base.executionEnv.precompileConfig
      base.executionEnv.fork base.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (flatLoop (flatProgress base a b out modulus count total returnDest rest
        total) a b out modulus count total total returnDest rest)
      (mulReturned (flatProgress base a b out modulus count total returnDest rest
        total) returnDest rest) := by
  set P := flatProgress base a b out modulus count total returnDest rest total
    with hP
  have hcodeP : P.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hP] using hcode
  have hforkP : P.fork = .Osaka := by simpa [hP, State.fork] using hfork
  have hrunP : P.halt = .Running := by simpa [hP] using hrun
  have hnpP : Precompile.isPrecompileWithConfig P.executionEnv.precompileConfig
      P.executionEnv.fork P.executionEnv.codeAddr = false := by
    simpa [hP, State.fork] using hnp
  exact (sound flatGuardPath
      (run_flatFinishGuard P a b out modulus count total returnDest rest
        (by omega) htotal (by simpa [flatLoop] using hcodeP)
        (by simpa [flatLoop] using hrunP))
      (by simpa [flatLoop, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatLoop, State.fork] using hforkP)
      (by simpa [flatLoop] using hrunP)
      (by simpa [flatLoop, State.fork] using hnpP)).trans
    (sound mulExitPath
      (run_mulExit P a b out modulus count total returnDest rest (by omega)
        (by simpa [flatExit] using hcodeP) (by simpa [flatExit] using hrunP)
        hvalid)
      (by simpa [flatExit, Artifact.submissionArtifact] using hcodeP)
      (by simpa [flatExit, State.fork] using hforkP)
      (by simpa [flatExit] using hrunP)
      (by simpa [flatExit, State.fork] using hnpP))

/-- The complete trace of `mulModBig`, from the call to the hand-back. -/
def gasSteps_mulModBig (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcap : rest.length < 980) (hcount : count < 2 ^ 256)
    (hcode : s.executionEnv.code = Challenge.Modexp.submissionBytecode)
    (hfork : s.fork = .Osaka) (hrun : s.halt = .Running)
    (hnp : Precompile.isPrecompileWithConfig s.executionEnv.precompileConfig
      s.executionEnv.fork s.executionEnv.codeAddr = false)
    (hvalid : Decode.isValidJumpDest Challenge.Modexp.submissionBytecode
      returnDest.toNat = true) :
    Challenge.EvmProof.GasSteps
      (mulEntry s a b out modulus count returnDest rest)
      (mulReturned (mulApplied s a b out modulus count returnDest rest)
        returnDest rest) := by
  set base := mulCopied s a b out modulus count returnDest rest with hbase
  have hcodeB : base.executionEnv.code = Challenge.Modexp.submissionBytecode := by
    simpa [hbase, mulCopied, mulAfterCopy, mulAfterClear] using hcode
  have hforkB : base.fork = .Osaka := by
    simpa [hbase, mulCopied, mulAfterCopy, mulAfterClear, State.fork] using hfork
  have hrunB : base.halt = .Running := by
    simpa [hbase, mulCopied, mulAfterCopy, mulAfterClear] using hrun
  have hnpB : Precompile.isPrecompileWithConfig
      base.executionEnv.precompileConfig base.executionEnv.fork
      base.executionEnv.codeAddr = false := by
    simpa [hbase, mulCopied, mulAfterCopy, mulAfterClear, State.fork] using hnp
  have htotal : mulTotal s b count < 2 ^ 256 := scanTotal_lt _ _ _
  exact (gasSteps_mulInitialize s a b out modulus count returnDest rest hcap
      hcount hcode hfork hrun hnp).trans
    ((gasSteps_flatLoop base a b out modulus count (mulTotal s b count)
        returnDest rest hcap hcount htotal hcodeB hforkB hrunB hnpB).trans
      (gasSteps_mulFinish base a b out modulus count (mulTotal s b count)
        returnDest rest hcap htotal hcodeB hforkB hrunB hnpB hvalid))

/-! ## The multiplier as a list of bits

The flat loop consumes bit `K` of the multiplier at step `K`.  Grouping those
bits 256 at a time recovers the limb-wise digit list the reference proof used,
which already has a value theorem. -/

def mulWordBit (word : UInt256) (j : Nat) : UInt256 :=
  UInt256.land (UInt256.shiftRight word (UInt256.ofNat j)) (UInt256.ofNat 1)

def mulWordBits (word : UInt256) (length : Nat) : List Nat :=
  (List.range length).map fun j => (mulWordBit word j).toNat

def mulOuterBits (memory : ByteArray) (bPtr steps : Nat) : List Nat :=
  (List.range steps).flatMap fun i =>
    mulWordBits (MachineState.readWord memory (bPtr + 32 * i)) 256

/-- Bits of the multiplier as the flat loop reads them. -/
def flatBits (memory : ByteArray) (b : UInt256) (steps : Nat) : List Nat :=
  (List.range steps).map fun k => (flatBit memory b k).toNat

theorem mulWordBit_toNat_le_one (word : UInt256) (j : Nat) :
    (mulWordBit word j).toNat ≤ 1 := by
  rw [mulWordBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_right

theorem flatBit_toNat_le_one (memory : ByteArray) (b : UInt256) (k : Nat) :
    (flatBit memory b k).toNat ≤ 1 := by
  rw [flatBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]
  exact Nat.and_le_left

theorem mulWordBit_toNat (word : UInt256) {j : Nat} (hj : j < 256) :
    (mulWordBit word j).toNat = (word.toNat >>> j) &&& 1 := by
  rw [mulWordBit, Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.shiftRight_toNat word hj,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 256)]

theorem mulWordBits_eq_digitsAppend (word : UInt256) :
    mulWordBits word 256 = Nat.digitsAppend 2 256 word.toNat := by
  apply List.ext_get
  · simp [mulWordBits,
      Nat.length_digitsAppend (n := word.toNat) (by norm_num) 256 word.val.isLt]
  · intro j hleft hright
    have hj : j < 256 := by simpa [mulWordBits] using hleft
    have hleftValue :
        (mulWordBits word 256).get ⟨j, hleft⟩ = (mulWordBit word j).toNat := by
      simp [mulWordBits]
    rw [hleftValue]
    rw [mulWordBit_toNat word hj, Nat.and_one_is_mod]
    have hrightValue :
        (Nat.digitsAppend 2 256 word.toNat).get ⟨j, hright⟩ =
          (Nat.digitsAppend 2 256 word.toNat).getD j 0 :=
      (List.getD_eq_getElem
        (Nat.digitsAppend 2 256 word.toNat) 0 hright).symm
    rw [hrightValue]
    have hpadded :
        (Nat.digitsAppend 2 256 word.toNat).getD j 0 =
          (Nat.digits 2 word.toNat).getD j 0 := by
      rw [Nat.digitsAppend]
      by_cases hdigit : j < (Nat.digits 2 word.toNat).length
      · rw [List.getD_append _ _ _ _ hdigit]
      · rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hdigit),
          List.getD_eq_default _ _ (Nat.le_of_not_gt hdigit)]
        simp [List.getD_eq_getElem?_getD]
    rw [hpadded, Nat.getD_digits word.toNat j (by omega),
      Nat.shiftRight_eq_div_pow]

theorem value_mulWordBits (word : UInt256) :
    Nat.ofDigits 2 (mulWordBits word 256) = word.toNat := by
  rw [mulWordBits_eq_digitsAppend, Nat.digitsAppend,
    Nat.ofDigits_append_replicate_zero, Nat.ofDigits_digits]

theorem mulOuterBits_succ (memory : ByteArray) (bPtr i : Nat) :
    mulOuterBits memory bPtr (i + 1) =
      mulOuterBits memory bPtr i ++
        mulWordBits (MachineState.readWord memory (bPtr + 32 * i)) 256 := by
  simp [mulOuterBits, List.range_succ]

@[simp] theorem length_mulOuterBits (memory : ByteArray) (bPtr steps : Nat) :
    (mulOuterBits memory bPtr steps).length = 256 * steps := by
  simp [mulOuterBits, mulWordBits]
  omega

theorem value_mulOuterBits (memory : ByteArray) (bPtr count : Nat) :
    Nat.ofDigits 2 (mulOuterBits memory bPtr count) =
      Nat.ofDigits Limbs.radix (Limbs.memoryLimbs memory bPtr count) := by
  induction count with
  | zero => simp [mulOuterBits, Limbs.memoryLimbs]
  | succ count ih =>
      rw [mulOuterBits_succ, Nat.ofDigits_append, ih, value_mulWordBits]
      simp [Limbs.memoryLimbs, List.range_succ, Nat.ofDigits_append,
        Limbs.radix, Nat.pow_mul]

theorem readWord_eq_of_represents (left right : ByteArray)
    (ptr count value i : Nat) (hi : i < count)
    (hleft : Limbs.Represents left ptr count value)
    (hright : Limbs.Represents right ptr count value) :
    MachineState.readWord left (ptr + 32 * i) =
      MachineState.readWord right (ptr + 32 * i) := by
  have hlists : Limbs.memoryLimbs left ptr count =
      Limbs.memoryLimbs right ptr count := hleft.2.trans hright.2.symm
  have hget := congrArg (fun digits => digits[i]?) hlists
  have htoNat :
      (MachineState.readWord left (ptr + 32 * i)).toNat =
        (MachineState.readWord right (ptr + 32 * i)).toNat := by
    simpa [Limbs.memoryLimbs, hi] using hget
  calc
    MachineState.readWord left (ptr + 32 * i) =
        UInt256.ofNat (MachineState.readWord left (ptr + 32 * i)).toNat :=
      Challenge.EvmProof.Word.word_eq_ofNat_toNat _
    _ = UInt256.ofNat (MachineState.readWord right (ptr + 32 * i)).toNat := by
      rw [htoNat]
    _ = MachineState.readWord right (ptr + 32 * i) :=
      (Challenge.EvmProof.Word.word_eq_ofNat_toNat _).symm

/-! ### Flat bits are the limb bits, regrouped -/

private theorem and_255 (n : Nat) : n &&& 255 = n % 256 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show (256 : Nat) = 2 ^ 8 by norm_num,
    Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · have hb : Nat.testBit 255 i = true := by interval_cases i <;> rfl
    simp [hb, hi]
  · have hlt : (255 : Nat) < 2 ^ i := by
      have h8 : (2 : Nat) ^ 8 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
      have : (2 : Nat) ^ 8 = 256 := by norm_num
      omega
    have hb : Nat.testBit 255 i = false := Nat.testBit_lt_two_pow hlt
    simp [hb, hi]

private theorem land_255 (k : Nat) :
    UInt256.land (UInt256.ofNat k) (UInt256.ofNat 255) =
      UInt256.ofNat (k % 256) := by
  apply Challenge.EvmProof.Word.word_ext
  rw [Challenge.EvmProof.Word.word_toNat_land,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Challenge.EvmProof.Word.word_toNat_ofNat,
    Nat.mod_eq_of_lt (by norm_num : 255 < 2 ^ 256), and_255,
    Nat.mod_mod_of_dvd _ (by norm_num : (256 : Nat) ∣ 2 ^ 256),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
      (by norm_num : (256 : Nat) ≤ 2 ^ 256))]

/-- The word the flat loop reads at bit `256 * i + j` is limb `i`. -/
theorem flatWord_eq (memory : ByteArray) (bPtr i j : Nat) (hj : j < 256)
    (hk : 256 * i + j < 2 ^ 256) (hfit : bPtr + 32 * i < 2 ^ 256) :
    flatWord memory (UInt256.ofNat bPtr) (256 * i + j) =
      MachineState.readWord memory (bPtr + 32 * i) := by
  have hshr : UInt256.shiftRight (UInt256.ofNat (256 * i + j)) (UInt256.ofNat 8) =
      UInt256.ofNat i := by
    rw [Challenge.EvmProof.Word.shiftRight_ofNat hk (by norm_num),
      Nat.shiftRight_eq_div_pow]
    congr 1
    omega
  have haddr : (UInt256.ofNat bPtr +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat =
      bPtr + 32 * i := by
    simpa [BigHelpers.clearOffset, add_comm] using
      BigHelpers.clearOffset_toNat bPtr i hfit
  simp [flatWord, flatPtr, hshr, haddr]

/-- Bit `256 * i + j` of the flat list is bit `j` of limb `i`. -/
theorem flatBit_eq (memory : ByteArray) (bPtr i j : Nat) (hj : j < 256)
    (hk : 256 * i + j < 2 ^ 256) (hfit : bPtr + 32 * i < 2 ^ 256) :
    (flatBit memory (UInt256.ofNat bPtr) (256 * i + j)).toNat =
      (mulWordBit (MachineState.readWord memory (bPtr + 32 * i)) j).toNat := by
  have hmod : (256 * i + j) % 256 = j := by omega
  rw [flatBit, flatWord_eq memory bPtr i j hj hk hfit, land_255, hmod,
    Challenge.EvmProof.Word.word_toNat_land, mulWordBit,
    Challenge.EvmProof.Word.word_toNat_land, Nat.and_comm]

theorem flatBits_add (memory : ByteArray) (b : UInt256) (m n : Nat) :
    flatBits memory b (m + n) =
      flatBits memory b m ++
        (List.range n).map fun j => (flatBit memory b (m + j)).toNat := by
  simp [flatBits, List.range_add, List.map_append, Function.comp_def]

theorem flatBits_eq_mulOuterBits (memory : ByteArray) (bPtr count : Nat)
    (hbits : 256 * count < 2 ^ 256) (hfit : bPtr + 32 * count < 2 ^ 256) :
    flatBits memory (UInt256.ofNat bPtr) (256 * count) =
      mulOuterBits memory bPtr count := by
  induction count with
  | zero => simp [flatBits, mulOuterBits]
  | succ count ih =>
      have hfit' : bPtr + 32 * count < 2 ^ 256 := by omega
      have hbits' : 256 * count < 2 ^ 256 := by omega
      have hstep : 256 * (count + 1) = 256 * count + 256 := by ring
      rw [hstep, flatBits_add, ih hbits' hfit', mulOuterBits_succ]
      congr 1
      apply List.ext_getElem
      · simp [mulWordBits]
      · intro j h1 h2
        have hj : j < 256 := by simpa using h1
        simpa [mulWordBits] using
          flatBit_eq memory bPtr count j hj (by omega) (by omega)

/-! ## The scan's bound is sound -/

theorem scanWord_eq (memory : ByteArray) (bPtr i : Nat)
    (hfit : bPtr + 32 * i < 2 ^ 256) :
    scanWord memory (UInt256.ofNat bPtr) i =
      MachineState.readWord memory (bPtr + 32 * i) := by
  have haddr : (UInt256.ofNat bPtr +
      UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5)).toNat =
      bPtr + 32 * i := by
    simpa [BigHelpers.clearOffset, add_comm] using
      BigHelpers.clearOffset_toNat bPtr i hfit
  simp [scanWord, scanPtr, haddr]

theorem ofDigits_lt_two_pow : ∀ (L : List Nat), (∀ d ∈ L, d ≤ 1) →
    Nat.ofDigits 2 L < 2 ^ L.length
  | [], _ => by norm_num
  | d :: L, h => by
      have hd : d ≤ 1 := h d (by simp)
      have hL : Nat.ofDigits 2 L < 2 ^ L.length :=
        ofDigits_lt_two_pow L fun x hx => h x (by simp [hx])
      have : Nat.ofDigits 2 (d :: L) = d + 2 * Nat.ofDigits 2 L := by
        simp [Nat.ofDigits_cons]
      rw [this]
      have hlen : (d :: L).length = L.length + 1 := by simp
      rw [hlen, pow_succ]
      omega

theorem mem_mulOuterBits_le_one (memory : ByteArray) (bPtr steps : Nat)
    {d : Nat} (hd : d ∈ mulOuterBits memory bPtr steps) : d ≤ 1 := by
  simp only [mulOuterBits, List.mem_flatMap, mulWordBits, List.mem_map] at hd
  rcases hd with ⟨i, _, j, _, rfl⟩
  exact mulWordBit_toNat_le_one _ _

theorem mem_flatBits_le_one (memory : ByteArray) (b : UInt256) (steps : Nat)
    {d : Nat} (hd : d ∈ flatBits memory b steps) : d ≤ 1 := by
  simp only [flatBits, List.mem_map] at hd
  rcases hd with ⟨k, _, rfl⟩
  exact flatBit_toNat_le_one _ _ _

@[simp] theorem length_flatBits (memory : ByteArray) (b : UInt256)
    (steps : Nat) : (flatBits memory b steps).length = steps := by
  simp [flatBits]

set_option linter.unusedSimpArgs false in
theorem scanTotal_le (memory : ByteArray) (bPtr i : Nat) (hi : i ≤ 32) :
    scanTotal memory (UInt256.ofNat bPtr) i ≤ 256 * i := by
  induction i with
  | zero => simp [scanTotal]
  | succ i ih =>
      have hprev := ih (by omega)
      by_cases h : (scanWord memory (UInt256.ofNat bPtr) i).toNat = 0
      · have heq : scanTotal memory (UInt256.ofNat bPtr) (i + 1) =
            scanTotal memory (UInt256.ofNat bPtr) i := by simp [scanTotal, h]
        rw [heq]; omega
      · have hsize : (scanWord memory (UInt256.ofNat bPtr) i).toNat.size ≤ 256 :=
          size_le_256 _
        have hbound : 256 * i + (scanWord memory (UInt256.ofNat bPtr) i).toNat.size
            < 2 ^ 256 := by
          have h1 : 256 * i ≤ 256 * 32 := by omega
          have hb : (2 : Nat) ^ 256 > 256 * 32 + 256 := by norm_num
          omega
        have heq : scanTotal memory (UInt256.ofNat bPtr) (i + 1) =
            256 * i + (scanWord memory (UInt256.ofNat bPtr) i).toNat.size := by
          simp (disch := omega) [scanTotal, h, Nat.mod_eq_of_lt]
        rw [heq]; omega

set_option linter.unusedSimpArgs false in
theorem scanTotal_bound (memory : ByteArray) (bPtr i : Nat) (hi : i ≤ 32)
    (hfit : bPtr + 32 * i < 2 ^ 256) :
    Nat.ofDigits 2 (mulOuterBits memory bPtr i) <
      2 ^ scanTotal memory (UInt256.ofNat bPtr) i := by
  induction i with
  | zero => simp [mulOuterBits, scanTotal, Nat.ofDigits]
  | succ i ih =>
      have hfit' : bPtr + 32 * i < 2 ^ 256 := by omega
      have hprev := ih (by omega) hfit'
      set w := MachineState.readWord memory (bPtr + 32 * i) with hw
      have hscan : scanWord memory (UInt256.ofNat bPtr) i = w :=
        scanWord_eq memory bPtr i hfit'
      have hsplit : Nat.ofDigits 2 (mulOuterBits memory bPtr (i + 1)) =
          Nat.ofDigits 2 (mulOuterBits memory bPtr i) +
            2 ^ (256 * i) * w.toNat := by
        rw [mulOuterBits_succ, Nat.ofDigits_append, length_mulOuterBits,
          value_mulWordBits]
      have hprevLt : Nat.ofDigits 2 (mulOuterBits memory bPtr i) <
          2 ^ (256 * i) := by
        have := ofDigits_lt_two_pow (mulOuterBits memory bPtr i)
          (fun d hd => mem_mulOuterBits_le_one memory bPtr i hd)
        simpa [length_mulOuterBits] using this
      by_cases hz : w.toNat = 0
      · have heq : scanTotal memory (UInt256.ofNat bPtr) (i + 1) =
            scanTotal memory (UInt256.ofNat bPtr) i := by
          simp [scanTotal, hscan, hz]
        rw [heq, hsplit, hz]
        simpa using hprev
      · have hsize : w.toNat.size ≤ 256 := size_le_256 _
        have hbound : 256 * i + w.toNat.size < 2 ^ 256 := by
          have h1 : 256 * i ≤ 256 * 32 := by omega
          have hb : (2 : Nat) ^ 256 > 256 * 32 + 256 := by norm_num
          omega
        have heq : scanTotal memory (UInt256.ofNat bPtr) (i + 1) =
            256 * i + w.toNat.size := by
          simp (disch := omega) [scanTotal, hscan, hz, Nat.mod_eq_of_lt]
        rw [heq, pow_add]
        have hwlt : w.toNat < 2 ^ w.toNat.size := Nat.lt_size_self _
        have hA : 0 < (2 : Nat) ^ (256 * i) := by positivity
        have hS : 0 < (2 : Nat) ^ w.toNat.size := by positivity
        have hle : 2 ^ (256 * i) ≤ 2 ^ (256 * i) * 2 ^ w.toNat.size :=
          Nat.le_mul_of_pos_right _ hS
        have hmul : 2 ^ (256 * i) * w.toNat ≤
            2 ^ (256 * i) * (2 ^ w.toNat.size - 1) :=
          Nat.mul_le_mul_left _ (by omega)
        have hexp : 2 ^ (256 * i) * (2 ^ w.toNat.size - 1) =
            2 ^ (256 * i) * 2 ^ w.toNat.size - 2 ^ (256 * i) := by
          rw [Nat.mul_sub, Nat.mul_one]
        omega

/-- The scan phase produces a bound that really does cover the multiplier. -/
theorem value_flatBits_scanTotal (memory : ByteArray)
    (bPtr count bValue : Nat) (hcount : count ≤ 32)
    (hfit : bPtr + 32 * count < 2 ^ 256)
    (hb : Limbs.Represents memory bPtr count bValue) :
    Nat.ofDigits 2 (flatBits memory (UInt256.ofNat bPtr)
      (scanTotal memory (UInt256.ofNat bPtr) count)) = bValue := by
  set total := scanTotal memory (UInt256.ofNat bPtr) count with htotalDef
  have hbits : 256 * count < 2 ^ 256 := by
    have : 256 * count ≤ 256 * 32 := by omega
    have hb2 : (2 : Nat) ^ 256 > 256 * 32 := by norm_num
    omega
  have hle : total ≤ 256 * count := scanTotal_le memory bPtr count hcount
  have hfull : Nat.ofDigits 2 (flatBits memory (UInt256.ofNat bPtr) (256 * count))
      = bValue := by
    rw [flatBits_eq_mulOuterBits memory bPtr count hbits hfit,
      value_mulOuterBits, Limbs.value_of_represents hb]
  have hlt : bValue < 2 ^ total := by
    rw [← hfull, flatBits_eq_mulOuterBits memory bPtr count hbits hfit]
    exact scanTotal_bound memory bPtr count hcount hfit
  have hdecomp : 256 * count = total + (256 * count - total) := by omega
  have happ := flatBits_add memory (UInt256.ofNat bPtr) total (256 * count - total)
  rw [← hdecomp] at happ
  rw [happ, Nat.ofDigits_append, length_flatBits] at hfull
  set pre := Nat.ofDigits 2 (flatBits memory (UInt256.ofNat bPtr) total) with hpre
  set suf := Nat.ofDigits 2 ((List.range (256 * count - total)).map
    fun j => (flatBit memory (UInt256.ofNat bPtr) (total + j)).toNat) with hsuf
  have hpreLt : pre < 2 ^ total := by
    have := ofDigits_lt_two_pow (flatBits memory (UInt256.ofNat bPtr) total)
      (fun d hd => mem_flatBits_le_one memory (UInt256.ofNat bPtr) total hd)
    simpa [hpre, length_flatBits] using this
  have hsufZero : suf = 0 := by
    by_contra hne
    have hpos : 0 < suf := Nat.pos_of_ne_zero hne
    have : 2 ^ total ≤ 2 ^ total * suf := Nat.le_mul_of_pos_right _ hpos
    omega
  rw [hsufZero] at hfull
  simpa using hfull

/-! ## What the flat loop computes -/

theorem flatWord_eq_of_represents (left right : ByteArray)
    (bPtr count bValue k : Nat) (hk : k < 256 * count) (hcount : count ≤ 32)
    (hfit : bPtr + 32 * count < 2 ^ 256)
    (hleft : Limbs.Represents left bPtr count bValue)
    (hright : Limbs.Represents right bPtr count bValue) :
    flatWord left (UInt256.ofNat bPtr) k = flatWord right (UInt256.ofNat bPtr) k := by
  have hi : k / 256 < count := by omega
  have hsplit : 256 * (k / 256) + k % 256 = k := by omega
  have hj : k % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have hbits : 256 * (k / 256) + k % 256 < 2 ^ 256 := by
    have : k < 2 ^ 256 := by
      have h1 : 256 * count ≤ 256 * 32 := by omega
      have hb : (2 : Nat) ^ 256 > 256 * 32 := by norm_num
      omega
    omega
  have hfit' : bPtr + 32 * (k / 256) < 2 ^ 256 := by omega
  rw [← hsplit, flatWord_eq left bPtr (k / 256) (k % 256) hj hbits hfit',
    flatWord_eq right bPtr (k / 256) (k % 256) hj hbits hfit']
  exact readWord_eq_of_represents left right bPtr count bValue (k / 256) hi
    hleft hright

set_option linter.unusedSimpArgs false in
theorem flatAfterDouble_represents (current : State) (a b : UInt256)
    (count total k acc addend modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let doubled := flatAfterDouble current a b (UInt256.ofNat 3072)
      (UInt256.ofNat 0) count total k returnDest rest
    let bit := (flatBit current.memory b k).toNat
    Limbs.Represents doubled.memory 3072 count
        ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 4096 count
        ((addend + addend) % modulusValue) ∧
      Limbs.Represents doubled.memory 0 count modulusValue := by
  have hfit0 : 0 + 32 * count < 2 ^ 256 := by omega
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  set saved := flatFrame a b (UInt256.ofNat 3072) (UInt256.ofNat 0) count total
    k returnDest rest with hsaved
  set afterAdd := flatAfterAdd current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count total k returnDest rest with hafterAdd
  set bit := (flatBit current.memory b k).toNat with hbit
  have hbitLe : bit ≤ 1 := flatBit_toNat_le_one _ _ _
  have hafterAcc : Limbs.Represents afterAdd.memory 3072 count
      ((acc + bit * addend) % modulusValue) ∧
      Limbs.Represents afterAdd.memory 4096 count addend ∧
      Limbs.Represents afterAdd.memory 0 count modulusValue := by
    by_cases hz : bit = 0
    · have hmem : afterAdd.memory = current.memory := by
        simp [hafterAdd, flatAfterAdd, flatLoaded, ← hbit, hz]
      have hval : (acc + bit * addend) % modulusValue = acc := by
        rw [hz]; simpa using Nat.mod_eq_of_lt haccReduced
      rw [hmem, hval]
      exact ⟨hacc, haddend, hmodulus⟩
    · have hone : bit = 1 := by omega
      have hmem : afterAdd = BigHelpers.addReturned (flatLoaded current b k)
          (UInt256.ofNat 3072) (UInt256.ofNat 4096) (UInt256.ofNat 1)
          (UInt256.ofNat 0) count (UInt256.ofNat 1592) saved := by
        simp [hafterAdd, flatAfterAdd, ← hbit, hz, hsaved]
      have hloadedAcc : Limbs.Represents (flatLoaded current b k).memory 3072
          count acc := by simpa [flatLoaded] using hacc
      have hloadedAddend : Limbs.Represents (flatLoaded current b k).memory 4096
          count addend := by simpa [flatLoaded] using haddend
      have hloadedMod : Limbs.Represents (flatLoaded current b k).memory 0 count
          modulusValue := by simpa [flatLoaded] using hmodulus
      refine ⟨?_, ?_, ?_⟩
      · rw [hmem, hone]
        simpa using BigHelpers.addReturned_represents_mod (flatLoaded current b k)
          3072 4096 0 count 1 acc addend modulusValue (UInt256.ofNat 1592) saved
          (by omega) hfit3072 hfit4096 hfit0 hfit5120 (by right; left; omega)
          (by right; omega) (by left; omega) (by left; omega) hloadedAcc
          hloadedAddend hloadedMod haccReduced haddendReduced.le hmodulusBound
      · rw [hmem]
        simpa using BigHelpers.addReturned_preserves_region
          (flatLoaded current b k) 3072 4096 1 0 4096 count addend
          (UInt256.ofNat 1592) saved hfit3072 hfit5120 (by left; omega)
          (by left; omega) hloadedAddend
      · rw [hmem]
        simpa using BigHelpers.addReturned_preserves_region
          (flatLoaded current b k) 3072 4096 1 0 0 count modulusValue
          (UInt256.ofNat 1592) saved hfit3072 hfit5120 (by right; omega)
          (by left; omega) hloadedMod
  have haccRed' : (acc + bit * addend) % modulusValue < modulusValue :=
    Nat.mod_lt _ hmodulusPos
  refine ⟨?_, ?_, ?_⟩
  · simpa [flatAfterDouble, ← hafterAdd, ← hsaved] using
      BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 3072 count
        ((acc + bit * addend) % modulusValue) (UInt256.ofNat 1610) saved
        hfit4096 hfit5120 (by right; omega) (by left; omega) hafterAcc.1
  · simpa [flatAfterDouble, ← hafterAdd, ← hsaved] using
      BigHelpers.addReturned_represents_mod afterAdd 4096 4096 0 count 1
        addend addend modulusValue (UInt256.ofNat 1610) saved (by omega)
        hfit4096 hfit4096 hfit0 hfit5120 (by left; rfl) (by right; omega)
        (by left; omega) (by left; omega) hafterAcc.2.1 hafterAcc.2.1
        hafterAcc.2.2 haddendReduced haddendReduced.le hmodulusBound
  · simpa [flatAfterDouble, ← hafterAdd, ← hsaved] using
      BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 0 count
        modulusValue (UInt256.ofNat 1610) saved hfit4096 hfit5120
        (by right; omega) (by left; omega) hafterAcc.2.2

set_option linter.unusedSimpArgs false in
theorem flatAfterDouble_preserves_region (current : State) (a b : UInt256)
    (count total k ptr value : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (flatAfterDouble current a b (UInt256.ofNat 3072) (UInt256.ofNat 0)
        count total k returnDest rest).memory ptr count value := by
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit5120 : 5120 + 32 * count < 2 ^ 256 := by omega
  set saved := flatFrame a b (UInt256.ofNat 3072) (UInt256.ofNat 0) count total
    k returnDest rest with hsaved
  set afterAdd := flatAfterAdd current a b (UInt256.ofNat 3072)
    (UInt256.ofNat 0) count total k returnDest rest with hafterAdd
  have hafter : Limbs.Represents afterAdd.memory ptr count value := by
    by_cases hz : (flatBit current.memory b k).toNat = 0
    · have hmem : afterAdd.memory = current.memory := by
        simp [hafterAdd, flatAfterAdd, flatLoaded, hz]
      rw [hmem]; exact hrep
    · have hmem : afterAdd = BigHelpers.addReturned (flatLoaded current b k)
          (UInt256.ofNat 3072) (UInt256.ofNat 4096) (UInt256.ofNat 1)
          (UInt256.ofNat 0) count (UInt256.ofNat 1592) saved := by
        simp [hafterAdd, flatAfterAdd, hz, hsaved]
      rw [hmem]
      simpa using BigHelpers.addReturned_preserves_region
        (flatLoaded current b k) 3072 4096 1 0 ptr count value
        (UInt256.ofNat 1592) saved hfit3072 hfit5120 hptrOut hptrCandidate
        (by simpa [flatLoaded] using hrep)
  simpa [flatAfterDouble, ← hafterAdd, ← hsaved] using
    BigHelpers.addReturned_preserves_region afterAdd 4096 4096 1 0 ptr count
      value (UInt256.ofNat 1610) saved hfit4096 hfit5120 hptrAddend
      hptrCandidate hafter

theorem flatProgress_preserves_region (current : State) (a b : UInt256)
    (count total steps ptr value : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents current.memory ptr count value) :
    Limbs.Represents
      (flatProgress current a b (UInt256.ofNat 3072) (UInt256.ofNat 0) count
        total returnDest rest steps).memory ptr count value := by
  induction steps with
  | zero => simpa [flatProgress] using hrep
  | succ steps ih =>
      simpa [flatProgress] using
        flatAfterDouble_preserves_region
          (flatProgress current a b (UInt256.ofNat 3072) (UInt256.ofNat 0)
            count total returnDest rest steps)
          a b count total steps ptr value returnDest rest hcount hptrOut
          hptrAddend hptrCandidate ih

theorem flatProgress_represents (current : State)
    (bPtr count total steps acc addend bValue modulusValue : Nat)
    (returnDest : UInt256) (rest : List UInt256)
    (hsteps : steps ≤ 256 * count) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (hacc : Limbs.Represents current.memory 3072 count acc)
    (haddend : Limbs.Represents current.memory 4096 count addend)
    (hb : Limbs.Represents current.memory bPtr count bValue)
    (hmodulus : Limbs.Represents current.memory 0 count modulusValue)
    (haccReduced : acc < modulusValue)
    (haddendReduced : addend < modulusValue) :
    let progress := flatProgress current (UInt256.ofNat 2048)
      (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count total
      returnDest rest steps
    let result := Algorithm.mulBits modulusValue acc addend
      (flatBits current.memory (UInt256.ofNat bPtr) steps)
    Limbs.Represents progress.memory 3072 count result.1 ∧
      Limbs.Represents progress.memory 4096 count result.2 ∧
      Limbs.Represents progress.memory bPtr count bValue ∧
      Limbs.Represents progress.memory 0 count modulusValue := by
  induction steps with
  | zero =>
      simp [flatProgress, flatBits, Algorithm.mulBits, hacc, haddend, hb,
        hmodulus]
  | succ steps ih =>
      have hsteps' : steps ≤ 256 * count := by omega
      have hk : steps < 256 * count := by omega
      have hbefore := ih hsteps'
      set before := flatProgress current (UInt256.ofNat 2048)
        (UInt256.ofNat bPtr) (UInt256.ofNat 3072) (UInt256.ofNat 0) count total
        returnDest rest steps with hbeforeDef
      set beforeResult := Algorithm.mulBits modulusValue acc addend
        (flatBits current.memory (UInt256.ofNat bPtr) steps) with hbr
      have hbeforeReduced := Algorithm.mulBits_lt
        (flatBits current.memory (UInt256.ofNat bPtr) steps) hmodulusPos
        haccReduced haddendReduced
      have hword : flatBit before.memory (UInt256.ofNat bPtr) steps =
          flatBit current.memory (UInt256.ofNat bPtr) steps := by
        simp only [flatBit]
        rw [flatWord_eq_of_represents before.memory current.memory bPtr count
          bValue steps hk hcount (by omega) hbefore.2.2.1 hb]
      have hstep := flatAfterDouble_represents before (UInt256.ofNat 2048)
        (UInt256.ofNat bPtr) count total steps beforeResult.1 beforeResult.2
        modulusValue returnDest rest hcount hmodulusPos hmodulusBound
        hbefore.1 hbefore.2.1 hbefore.2.2.2 hbeforeReduced.1 hbeforeReduced.2
      have hregion := flatAfterDouble_preserves_region before
        (UInt256.ofNat 2048) (UInt256.ofNat bPtr) count total steps bPtr bValue
        returnDest rest hcount (by right; omega) (by right; omega)
        (by left; omega) hbefore.2.2.1
      rw [hword] at hstep
      have hbitsSucc : flatBits current.memory (UInt256.ofNat bPtr) (steps + 1) =
          flatBits current.memory (UInt256.ofNat bPtr) steps ++
            [(flatBit current.memory (UInt256.ofNat bPtr) steps).toNat] := by
        simp [flatBits, List.range_succ]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [flatProgress, hbitsSucc, Algorithm.mulBits_append,
          Algorithm.mulBits, hbr] using hstep.1
      · simpa [flatProgress, hbitsSucc, Algorithm.mulBits_append,
          Algorithm.mulBits, hbr] using hstep.2.1
      · simpa [flatProgress] using hregion
      · simpa [flatProgress] using hstep.2.2

/-! ## Exported contract of `mulModBig` -/

@[simp] theorem flatProgress_callStack (current : State)
    (a b out modulus : UInt256) (count total : Nat) (returnDest : UInt256)
    (rest : List UInt256) (k : Nat) :
    (flatProgress current a b out modulus count total returnDest rest k).callStack =
      current.callStack := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [flatProgress, flatAfterDouble, BigHelpers.addReturned,
        flatAfterAdd]
      split <;> simp [flatLoaded, ih]

@[simp] theorem scanProgress_callStack (current : State) (b : UInt256)
    (i : Nat) :
    (scanProgress current b i).callStack = current.callStack := by
  induction i with
  | zero => rfl
  | succ i ih => simp [scanProgress, scanLoaded, ih]

@[simp] theorem mulApplied_executionEnv (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulApplied s a b out modulus count returnDest rest).executionEnv =
      s.executionEnv := by
  simp [mulApplied, mulCopied, mulAfterCopy, mulAfterClear]

@[simp] theorem mulApplied_halt (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulApplied s a b out modulus count returnDest rest).halt = s.halt := by
  simp [mulApplied, mulCopied, mulAfterCopy, mulAfterClear]

@[simp] theorem mulApplied_callStack (s : State) (a b out modulus : UInt256)
    (count : Nat) (returnDest : UInt256) (rest : List UInt256) :
    (mulApplied s a b out modulus count returnDest rest).callStack =
      s.callStack := by
  simp [mulApplied, mulCopied, mulAfterCopy, mulAfterClear]

theorem scanTotal_eq_of_represents (left right : ByteArray)
    (bPtr count bValue i : Nat) (hi : i ≤ count) (_hcount : count ≤ 32)
    (hfit : bPtr + 32 * count < 2 ^ 256)
    (hleft : Limbs.Represents left bPtr count bValue)
    (hright : Limbs.Represents right bPtr count bValue) :
    scanTotal left (UInt256.ofNat bPtr) i =
      scanTotal right (UInt256.ofNat bPtr) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      have hi' : i ≤ count := by omega
      have hilt : i < count := by omega
      have hfit' : bPtr + 32 * i < 2 ^ 256 := by omega
      have hword : scanWord left (UInt256.ofNat bPtr) i =
          scanWord right (UInt256.ofNat bPtr) i := by
        rw [scanWord_eq left bPtr i hfit', scanWord_eq right bPtr i hfit']
        exact readWord_eq_of_represents left right bPtr count bValue i hilt
          hleft hright
      simp [scanTotal, hword, ih hi']

theorem flatBits_eq_of_represents (left right : ByteArray)
    (bPtr count bValue n : Nat) (hn : n ≤ 256 * count) (hcount : count ≤ 32)
    (hfit : bPtr + 32 * count < 2 ^ 256)
    (hleft : Limbs.Represents left bPtr count bValue)
    (hright : Limbs.Represents right bPtr count bValue) :
    flatBits left (UInt256.ofNat bPtr) n =
      flatBits right (UInt256.ofNat bPtr) n := by
  apply List.ext_getElem
  · simp
  · intro k h1 _
    have hk : k < n := by simpa using h1
    have hk' : k < 256 * count := by omega
    simp only [flatBits, List.getElem_map, List.getElem_range]
    simp only [flatBit]
    rw [flatWord_eq_of_represents left right bPtr count bValue k hk' hcount hfit
      hleft hright]

theorem mulCopied_represents (s : State) (bPtr count aValue bValue
    modulusValue : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32) (hbPtr : bPtr + 32 * count ≤ 3072)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let copied := mulCopied s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    Limbs.Represents copied.memory 3072 count 0 ∧
      Limbs.Represents copied.memory 4096 count aValue ∧
      Limbs.Represents copied.memory bPtr count bValue ∧
      Limbs.Represents copied.memory 0 count modulusValue := by
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hfit2048 : 2048 + 32 * count < 2 ^ 256 := by omega
  simp only [mulCopied, mulAfterCopy, mulAfterClear, scanProgress_memory]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 4096 2048 3072
      count 0 hfit4096 (by right; omega)
      (BigHelpers.clearMemory_represents_zero s.memory 3072 count hfit3072)
  · exact BigHelpers.copyMemory_represents _ 4096 2048 count aValue
      (BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 2048
        count aValue hfit3072 (by right; omega) ha)
      hfit4096 hfit2048 (by right; omega)
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 4096 2048 bPtr
      count bValue hfit4096 (by right; omega)
      (BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 bPtr
        count bValue hfit3072 (by right; omega) hb)
  · exact BigHelpers.represents_copyMemory_disjoint_region _ 4096 2048 0
      count modulusValue hfit4096 (by right; omega)
      (BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 0
        count modulusValue hfit3072 (by right; omega) hmodulus)

theorem mulApplied_preserves_region (s : State) (b : UInt256)
    (count ptr value : Nat) (returnDest : UInt256) (rest : List UInt256)
    (hcount : count ≤ 32)
    (hptrOut : 3072 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 3072)
    (hptrAddend : 4096 + 32 * count ≤ ptr ∨ ptr + 32 * count ≤ 4096)
    (hptrCandidate : ptr + 32 * count ≤ 5120 ∨ 5120 + 32 * count ≤ ptr)
    (hrep : Limbs.Represents s.memory ptr count value) :
    Limbs.Represents
      (mulApplied s (UInt256.ofNat 2048) b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest).memory ptr count value := by
  have hfit3072 : 3072 + 32 * count < 2 ^ 256 := by omega
  have hfit4096 : 4096 + 32 * count < 2 ^ 256 := by omega
  have hcopied : Limbs.Represents
      (mulCopied s (UInt256.ofNat 2048) b (UInt256.ofNat 3072)
        (UInt256.ofNat 0) count returnDest rest).memory ptr count value := by
    simp only [mulCopied, mulAfterCopy, mulAfterClear, scanProgress_memory]
    exact BigHelpers.represents_copyMemory_disjoint_region _ 4096 2048 ptr count
      value hfit4096 hptrAddend
      (BigHelpers.represents_clearMemory_disjoint_region s.memory 3072 ptr count
        value hfit3072 hptrOut hrep)
  exact flatProgress_preserves_region _ (UInt256.ofNat 2048) b count
    (mulTotal s b count) (mulTotal s b count) ptr value returnDest rest hcount
    hptrOut hptrAddend hptrCandidate hcopied

/-- `mulModBig(a, b, 0x0c00, modulus, n)` leaves `a * b mod modulus` at
`0x0c00`, and leaves the multiplier and the modulus alone. -/
theorem mulApplied_represents_product (s : State)
    (bPtr count aValue bValue modulusValue : Nat) (returnDest : UInt256)
    (rest : List UInt256) (hcount : count ≤ 32)
    (hbPtr : bPtr + 32 * count ≤ 3072) (hmodulusPos : 0 < modulusValue)
    (hmodulusBound : modulusValue < Limbs.radix ^ count)
    (haReduced : aValue < modulusValue)
    (ha : Limbs.Represents s.memory 2048 count aValue)
    (hb : Limbs.Represents s.memory bPtr count bValue)
    (hmodulus : Limbs.Represents s.memory 0 count modulusValue) :
    let applied := mulApplied s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
      (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest
    Limbs.Represents applied.memory 3072 count
        ((aValue * bValue) % modulusValue) ∧
      Limbs.Represents applied.memory bPtr count bValue ∧
      Limbs.Represents applied.memory 0 count modulusValue := by
  have hfit : bPtr + 32 * count < 2 ^ 256 := by omega
  set copied := mulCopied s (UInt256.ofNat 2048) (UInt256.ofNat bPtr)
    (UInt256.ofNat 3072) (UInt256.ofNat 0) count returnDest rest with hcopiedDef
  have hcopied := mulCopied_represents s bPtr count aValue bValue modulusValue
    returnDest rest hcount hbPtr ha hb hmodulus
  set total := mulTotal s (UInt256.ofNat bPtr) count with htotalDef
  have hle : total ≤ 256 * count := scanTotal_le s.memory bPtr count hcount
  have hcopiedMem : copied.memory =
      BigHelpers.copyMemory (BigHelpers.clearMemory s.memory
        (UInt256.ofNat 3072) count) (UInt256.ofNat 4096) (UInt256.ofNat 2048)
        count := by
    simp [hcopiedDef, mulCopied, mulAfterCopy, mulAfterClear]
  have hsame : scanTotal copied.memory (UInt256.ofNat bPtr) count = total :=
    scanTotal_eq_of_represents copied.memory s.memory bPtr count bValue count
      (le_refl _) hcount hfit hcopied.2.2.1 hb
  have hbitsEq : flatBits copied.memory (UInt256.ofNat bPtr) total =
      flatBits s.memory (UInt256.ofNat bPtr) total :=
    flatBits_eq_of_represents copied.memory s.memory bPtr count bValue total
      hle hcount hfit hcopied.2.2.1 hb
  have hvalue : Nat.ofDigits 2 (flatBits copied.memory (UInt256.ofNat bPtr)
      total) = bValue := by
    rw [hbitsEq]
    have := value_flatBits_scanTotal s.memory bPtr count bValue hcount hfit hb
    simpa [htotalDef, mulTotal] using this
  have hprogress := flatProgress_represents copied bPtr count total total 0
    aValue bValue modulusValue returnDest rest hle hcount hbPtr hmodulusPos
    hmodulusBound hcopied.1 hcopied.2.1 hcopied.2.2.1 hcopied.2.2.2
    hmodulusPos haReduced
  have hresultLt := Algorithm.mulBits_lt
    (flatBits copied.memory (UInt256.ofNat bPtr) total) hmodulusPos
    hmodulusPos haReduced
  have hfst := Algorithm.mulBits_fst modulusValue 0 aValue
    (flatBits copied.memory (UInt256.ofNat bPtr) total)
  rw [Nat.mod_eq_of_lt hresultLt.1, hvalue] at hfst
  refine ⟨?_, ?_, ?_⟩
  · have := hprogress.1
    rw [hfst] at this
    simpa [mulApplied, ← hcopiedDef, ← htotalDef, Nat.zero_add] using this
  · simpa [mulApplied, ← hcopiedDef, ← htotalDef] using hprogress.2.2.1
  · simpa [mulApplied, ← hcopiedDef, ← htotalDef] using hprogress.2.2.2

end Challenge.Modexp.Submission.Proofs.Bytecode.BigMul
